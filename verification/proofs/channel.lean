import Certificate
import Cslib.Foundations.Semantics.LTS.OmegaExecution

open ReactiveModules Verified
namespace Channel

def env (values : List Int) : Nat → Int := fun n => values[n]?.getD 0

theorem submit_spec (n v offered : Int) (busy : Bool) :
    sender_graph.run (env [n, flag busy, v, 0, 0, offered]) =
      if busy then [n, 1, v, 0, 0, 0, 0, 0] else [n, 1, offered, 1, n, offered, 1, 0] := by
  rw [sender_correct]
  cases busy <;>
    simp [sender_source, Source.run, Source.exec, Expr.eval, Bin.eval, flag, env, List.range_succ]

theorem tick_spec (n v : Int) (busy : Bool) :
    sender_graph.run (env [n, flag busy, v, 1, 0, 0]) =
      if busy then [n, 1, v, 1, n, v, 0, 0] else [n, 0, v, 0, 0, 0, 0, 0] := by
  rw [sender_correct]
  cases busy <;>
    simp [sender_source, Source.run, Source.exec, Expr.eval, Bin.eval, flag, env, List.range_succ]

theorem ack_spec (n v k : Int) (busy : Bool) :
    sender_graph.run (env [n, flag busy, v, 2, k, 0]) =
      if busy && k == n then [n + 1, 0, v, 0, 0, 0, 0, 1]
      else [n, flag busy, v, 0, 0, 0, 0, 0] := by
  rw [sender_correct]
  cases busy <;> by_cases h : k = n <;>
    simp [sender_source, Source.run, Source.exec, Expr.eval, Bin.eval, flag, env, h, List.range_succ]

theorem receive_spec (n k v : Int) :
    receiver_graph.run (env [n, k, v]) =
      if k = n then [n + 1, 1, k, 1, v]
      else if k < n then [n, 1, k, 0, 0]
      else [n, 0, 0, 0, 0] := by
  rw [receiver_correct]
  by_cases h : k = n <;> by_cases h' : k < n <;>
    simp [receiver_source, Source.run, Source.exec, Expr.eval, Bin.eval, flag, env, h, h', List.range_succ]

theorem initial_sender_spec : initial_sender_graph.run (env []) = [0, 0, 0] := by
  rw [initial_sender_correct]
  rfl

theorem initial_receiver_spec : initial_receiver_graph.run (env []) = [0] := by
  rw [initial_receiver_correct]
  rfl

structure Packet where
  number : Nat
  value : Int
  deriving DecidableEq, Repr

structure World where
  number : Nat := 0
  busy : Bool := false
  value : Int := 0
  expected : Nat := 0
  offered : List Int := []
  received : List Int := []
  data : List Packet := []
  acks : List Nat := []
  deriving DecidableEq, Repr

inductive Action where
  | submit (value : Int)
  | tick
  | receive (packet : Packet)
  | acknowledge (number : Nat)
  | dropData (packet : Packet)
  | copyData (packet : Packet)
  | dropAck (number : Nat)
  | copyAck (number : Nat)
  | idle
  deriving DecidableEq, Repr

/-- A loss/duplication/reordering channel. Receive/copy require a genuine queued packet.
    Node arithmetic and effects are the normal forms proved above from the actual RM. -/
def step (w : World) : Action → World
  | .submit v => if w.busy then w else
      { w with busy := true, value := v, offered := w.offered ++ [v], data := w.data ++ [⟨w.number, v⟩] }
  | .tick => if w.busy then { w with data := w.data ++ [⟨w.number, w.value⟩] } else w
  | .receive p =>
      let w' := { w with data := w.data.erase p }
      if p.number = w.expected then
        { w' with expected := w.expected + 1, received := w.received ++ [p.value], acks := w.acks ++ [p.number] }
      else if p.number < w.expected then { w' with acks := w.acks ++ [p.number] }
      else w'
  | .acknowledge n =>
      let w' := { w with acks := w.acks.erase n }
      if w.busy && n == w.number then { w' with number := w.number + 1, busy := false } else w'
  | .dropData p => { w with data := w.data.erase p }
  | .copyData p => { w with data := p :: w.data }
  | .dropAck n => { w with acks := w.acks.erase n }
  | .copyAck n => { w with acks := n :: w.acks }
  | .idle => w

def Enabled (w : World) : Action → Prop
  | .receive p | .dropData p | .copyData p => p ∈ w.data
  | .acknowledge n | .dropAck n | .copyAck n => n ∈ w.acks
  | _ => True

def lts : Cslib.LTS World Action := ⟨fun w a w' => Enabled w a ∧ step w a = w'⟩

def field (xs : List Int) (n : Nat) : Int := xs[n]?.getD 0

/-- Adapter for the compiled sender's declared result record. -/
def runSender (w : World) (kind : Int) (number : Nat) (value : Int) : World :=
  let out := sender_graph.run (env [w.number, flag w.busy, w.value, kind, number, value])
  { w with
    number := (field out 0).toNat
    busy := field out 1 != 0
    value := field out 2
    offered := if field out 6 != 0 then w.offered ++ [value] else w.offered
    data := if field out 3 != 0 then w.data ++ [⟨(field out 4).toNat, field out 5⟩] else w.data }

/-- Adapter for the compiled receiver's declared result record. -/
def runReceiver (w : World) (p : Packet) : World :=
  let out := receiver_graph.run (env [w.expected, p.number, p.value])
  { w with
    expected := (field out 0).toNat
    received := if field out 3 != 0 then w.received ++ [field out 4] else w.received
    acks := if field out 1 != 0 then w.acks ++ [(field out 2).toNat] else w.acks }

/-- This execution path calls the actual exported RM graphs. -/
def compiledStep (w : World) : Action → World
  | .submit v => runSender w 0 0 v
  | .tick => runSender w 1 0 0
  | .acknowledge n => runSender { w with acks := w.acks.erase n } 2 n 0
  | .receive p => runReceiver { w with data := w.data.erase p } p
  | action => step w action

theorem compiledStep_eq (w : World) (a : Action) : compiledStep w a = step w a := by
  cases a with
  | submit v =>
    simp only [compiledStep, runSender, Int.ofNat_zero]
    simp only [submit_spec (w.number : Int) w.value v w.busy]
    cases hb : w.busy <;> simp [hb, step, field]
    all_goals (cases w; simp_all)
  | tick =>
    simp only [compiledStep, runSender, Int.ofNat_zero]
    simp only [tick_spec (w.number : Int) w.value w.busy]
    cases hb : w.busy <;> simp [hb, step, field]
    all_goals (cases w; simp_all)
  | acknowledge n =>
    simp only [compiledStep, runSender, ack_spec]
    cases hb : w.busy <;> by_cases he : n = w.number <;>
      simp [hb, he, step, field, flag, Int.ofNat_inj]
  | receive p =>
    simp only [compiledStep, runReceiver, receive_spec]
    by_cases he : p.number = w.expected <;> by_cases hl : p.number < w.expected <;>
      simp [he, hl, step, field, Int.ofNat_inj]
  | _ => rfl

def compiledLTS : Cslib.LTS World Action := ⟨fun w a w' => Enabled w a ∧ compiledStep w a = w'⟩

def compiledInitial : World :=
  let s := initial_sender_graph.run (env [])
  let r := initial_receiver_graph.run (env [])
  { number := (field s 0).toNat, busy := field s 1 != 0, value := field s 2, expected := (field r 0).toNat }

theorem compiledInitial_eq : compiledInitial = {} := by
  simp [compiledInitial, initial_sender_spec, initial_receiver_spec, field]

theorem compiledLTS_eq : compiledLTS = lts := by
  unfold compiledLTS lts
  simp only [compiledStep_eq]

structure Invariant (w : World) : Prop where
  length : w.offered.length = w.number + if w.busy then 1 else 0
  position : w.expected = w.received.length
  lower : w.number ≤ w.expected
  upper : w.expected ≤ w.offered.length
  deliveryPrefix : w.received = w.offered.take w.expected
  pending : w.busy = true → w.offered[w.number]? = some w.value
  packets : ∀ p ∈ w.data, w.offered[p.number]? = some p.value
  acknowledgements : ∀ n ∈ w.acks, n < w.expected

theorem initial_invariant : Invariant ({} : World) := by
  constructor <;> simp

theorem Invariant.requeue {w : World} (h : Invariant w) (data : List Packet) (acks : List Nat)
    (hd : ∀ p ∈ data, w.offered[p.number]? = some p.value)
    (ha : ∀ n ∈ acks, n < w.expected) : Invariant { w with data := data, acks := acks } :=
  ⟨h.length, h.position, h.lower, h.upper, h.deliveryPrefix, h.pending, hd, ha⟩

theorem submit_preserves {w : World} (h : Invariant w) (v : Int) :
    Invariant (step w (.submit v)) := by
  by_cases hb : w.busy = true
  · simpa [step, hb] using h
  · have hf : w.busy = false := by cases h' : w.busy <;> simp_all
    have hn : w.offered.length = w.number := by simpa [hf] using h.length
    simp only [step, hf, Bool.false_eq_true, ↓reduceIte]
    refine ⟨?_, h.position, h.lower, ?_, ?_, ?_, ?_, h.acknowledgements⟩
    · simp [hn]
    · simp only [List.length_append, List.length_singleton]; have := h.upper; omega
    · simpa [List.take_append_of_le_length h.upper] using h.deliveryPrefix
    · intro _; simp [← hn]
    · intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · have hv := h.packets p hp
        rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hv).choose]
        exact hv
      · simp only [List.mem_singleton] at hp
        subst p
        simp [← hn]

theorem tick_preserves {w : World} (h : Invariant w) : Invariant (step w .tick) := by
  by_cases hb : w.busy = true
  · simp only [step, if_pos hb]
    apply h.requeue _ _ _ h.acknowledgements
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact h.packets p hp
    · simp only [List.mem_singleton] at hp
      subst p
      exact h.pending hb
  · simpa [step, hb] using h

theorem receive_preserves {w : World} (h : Invariant w) (p : Packet) (hp : p ∈ w.data) :
    Invariant (step w (.receive p)) := by
  have hd : ∀ q ∈ w.data.erase p, w.offered[q.number]? = some q.value :=
    fun q hq => h.packets q (List.mem_of_mem_erase hq)
  by_cases he : p.number = w.expected
  · have hv : w.offered[w.expected]? = some p.value := by simpa [he] using h.packets p hp
    have bound : w.expected < w.offered.length := (List.getElem?_eq_some_iff.mp hv).choose
    simp only [step, he, ↓reduceIte]
    refine ⟨h.length, ?_, ?_, bound, ?_, h.pending, hd, ?_⟩
    · simp [h.position]
    · change w.number ≤ w.expected + 1; have := h.lower; omega
    · rw [List.take_add_one, hv, ← h.deliveryPrefix]; rfl
    · intro n hn
      rcases List.mem_append.mp hn with hn | hn
      · change n < w.expected + 1; have := h.acknowledgements n hn; omega
      · simp only [List.mem_singleton] at hn
        change n < w.expected + 1
        omega
  · by_cases hl : p.number < w.expected
    · simp only [step, he, hl, ↓reduceIte]
      apply h.requeue _ _ hd
      intro n hn
      rcases List.mem_append.mp hn with hn | hn
      · exact h.acknowledgements n hn
      · simp only [List.mem_singleton] at hn
        simpa [hn] using hl
    · simpa only [step, he, hl, ↓reduceIte] using h.requeue _ _ hd h.acknowledgements

theorem acknowledge_preserves {w : World} (h : Invariant w) (n : Nat) (hn : n ∈ w.acks) :
    Invariant (step w (.acknowledge n)) := by
  have ha : ∀ k ∈ w.acks.erase n, k < w.expected :=
    fun k hk => h.acknowledgements k (List.mem_of_mem_erase hk)
  by_cases hb : w.busy = true
  · by_cases he : n = w.number
    · have bound := h.acknowledgements n hn
      simp only [step, hb, he, beq_self_eq_true, Bool.and_self, ↓reduceIte]
      refine ⟨?_, h.position, ?_, h.upper, h.deliveryPrefix, ?_, h.packets, ?_⟩
      · simpa [hb] using h.length
      · change w.number + 1 ≤ w.expected; omega
      · simp
      · simpa [he] using ha
    · simpa [step, hb, he] using h.requeue _ _ h.packets ha
  · simpa [step, hb] using h.requeue _ _ h.packets ha

theorem step_preserves {w : World} (h : Invariant w) (a : Action) (enabled : Enabled w a) :
    Invariant (step w a) := by
  cases a with
  | submit v => exact submit_preserves h v
  | tick => exact tick_preserves h
  | receive p => exact receive_preserves h p enabled
  | acknowledge n => exact acknowledge_preserves h n enabled
  | dropData p =>
    exact h.requeue _ _ (fun q hq => h.packets q (List.mem_of_mem_erase hq)) h.acknowledgements
  | dropAck n =>
    exact h.requeue _ _ h.packets (fun k hk => h.acknowledgements k (List.mem_of_mem_erase hk))
  | copyData p =>
    apply h.requeue _ _ _ h.acknowledgements
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact h.packets _ enabled
    · exact h.packets q hq
  | copyAck n =>
    apply h.requeue _ _ h.packets
    intro k hk
    rcases List.mem_cons.mp hk with rfl | hk
    · exact h.acknowledgements _ enabled
    · exact h.acknowledgements k hk
  | idle => exact h

theorem reachable_invariant {w : World} {actions : List Action}
    (h : lts.MTr {} actions w) : Invariant w := by
  have lift : ∀ {a b : World} {labels : List Action}, lts.MTr a labels b → Invariant a → Invariant b := by
    intro a b labels path
    induction path with
    | refl => exact id
    | stepL h _ ih =>
      intro inv
      exact ih (h.2 ▸ step_preserves inv _ h.1)
  exact lift h initial_invariant

/-- Universal, unbounded safety; no fairness or delivery-success premise. -/
theorem safety {w : World} {actions : List Action} (h : lts.MTr {} actions w) :
    w.received = w.offered.take w.received.length ∧
      w.number ≤ w.received.length ∧ w.received.length ≤ w.offered.length := by
  have inv := reachable_invariant h
  exact ⟨inv.position ▸ inv.deliveryPrefix, inv.position ▸ inv.lower, inv.position ▸ inv.upper⟩

theorem compiled_safety {w : World} {actions : List Action} (h : compiledLTS.MTr compiledInitial actions w) :
    w.received = w.offered.take w.received.length ∧
      w.number ≤ w.received.length ∧ w.received.length ≤ w.offered.length :=
  safety (by simpa [compiledLTS_eq, compiledInitial_eq] using h)

theorem number_monotone (w : World) (a : Action) : w.number ≤ (step w a).number := by
  cases a <;> grind [step]

theorem expected_monotone (w : World) (a : Action) : w.expected ≤ (step w a).expected := by
  cases a <;> grind [step]

theorem lookup_preserved (w : World) (a : Action) (n : Nat) (v : Int)
    (h : w.offered[n]? = some v) : (step w a).offered[n]? = some v := by
  have bound := (List.getElem?_eq_some_iff.mp h).choose
  cases a <;> simp only [step] <;>
    repeat first | (split) | (simp_all [List.getElem?_append_left bound])

def Execution (trace : Nat → World) (actions : Nat → Action) : Prop :=
  trace 0 = {} ∧ lts.OmegaExecution ⟨trace⟩ ⟨actions⟩

theorem execution_step {trace actions} (ex : Execution trace actions) (t : Nat) :
    Enabled (trace t) (actions t) ∧ step (trace t) (actions t) = trace (t + 1) := ex.2 t

theorem invariant_along {trace actions} (ex : Execution trace actions) (t : Nat) : Invariant (trace t) := by
  induction t with
  | zero => rw [ex.1]; exact initial_invariant
  | succ t ih => exact (execution_step ex t).2 ▸ step_preserves ih _ (execution_step ex t).1

theorem numbers_along {trace actions} (ex : Execution trace actions) :
    Monotone (fun t => (trace t).number) := by
  apply monotone_nat_of_le_succ
  intro t
  rw [← (execution_step ex t).2]
  exact number_monotone _ _

theorem expectations_along {trace actions} (ex : Execution trace actions) :
    Monotone (fun t => (trace t).expected) := by
  apply monotone_nat_of_le_succ
  intro t
  rw [← (execution_step ex t).2]
  exact expected_monotone _ _

def Delivers (w : World) (a : Action) (n : Nat) : Prop :=
  ∃ p, a = .receive p ∧ p.number = w.expected ∧ n = p.number

/-- Request identifiers, not merely payload equality, are delivered at most once. -/
theorem delivery_once {trace actions} (ex : Execution trace actions) {t u n : Nat}
    (order : t < u) (first : Delivers (trace t) (actions t) n) :
    ¬ Delivers (trace u) (actions u) n := by
  obtain ⟨p, action, number, id⟩ := first
  have advanced : n < (trace (t + 1)).expected := by
    rw [← (execution_step ex t).2]
    simp [step, action, number, id]
  have monotone := expectations_along ex (show t + 1 ≤ u by omega)
  dsimp only at monotone
  rintro ⟨q, _, number', id'⟩
  omega

theorem lookup_along {trace actions} (ex : Execution trace actions) {t u : Nat} (hu : t ≤ u)
    {n : Nat} {v : Int} (hv : (trace t).offered[n]? = some v) : (trace u).offered[n]? = some v := by
  induction u, hu using Nat.le_induction with
  | base => exact hv
  | succ u hu ih =>
    rw [← (execution_step ex u).2]
    exact lookup_preserved _ _ _ _ ih

def EmitsData (w : World) (a : Action) (p : Packet) : Prop :=
  match a with
  | .submit v => w.busy = false ∧ p = ⟨w.number, v⟩
  | .tick => w.busy = true ∧ p = ⟨w.number, w.value⟩
  | _ => False

def EmitsAck (w : World) (a : Action) (n : Nat) : Prop :=
  match a with
  | .receive p => p.number ≤ w.expected ∧ n = p.number
  | _ => False

abbrev Frequently := ReactiveModules.Network.Frequently

/-- Fair loss does not require any individual transmission to succeed. It requires
    infinitely repeated transmissions to be processed infinitely often. -/
structure Fair (trace : Nat → World) (actions : Nat → Action) : Prop where
  ticks : Frequently (fun t => actions t = .tick)
  data : ReactiveModules.Network.FairLoss
    (fun t p => EmitsData (trace t) (actions t) p) (fun t p => actions t = .receive p)
  acks : ReactiveModules.Network.FairLoss
    (fun t n => EmitsAck (trace t) (actions t) n) (fun t n => actions t = .acknowledge n)

/-- Every pending request completes; unlike a finite replay this quantifies over
    all infinite executions satisfying the stated scheduler/fair-loss profile. -/
theorem liveness {trace actions} (ex : Execution trace actions) (fair : Fair trace actions)
    (t : Nat) (pending : (trace t).busy = true) :
    ∃ u, t ≤ u ∧ (trace t).number < (trace u).number := by
  by_contra noProgress
  have bounded : ∀ u, t ≤ u → (trace u).number ≤ (trace t).number := by
    intro u hu
    exact Nat.le_of_not_gt (fun h => noProgress ⟨u, hu, h⟩)
  have fixed : ∀ u, t ≤ u → (trace u).number = (trace t).number := by
    intro u hu
    exact Nat.le_antisymm (bounded u hu) (numbers_along ex hu)
  have old := (invariant_along ex t).pending pending
  have busy : ∀ u, t ≤ u → (trace u).busy = true := by
    intro u hu
    have valuePresent := lookup_along ex hu old
    have lengthBound := (List.getElem?_eq_some_iff.mp valuePresent).choose
    have lengthEq := (invariant_along ex u).length
    have same := fixed u hu
    cases hb : (trace u).busy <;> simp_all
  have value : ∀ u, t ≤ u → (trace u).value = (trace t).value := by
    intro u hu
    have current := (invariant_along ex u).pending (busy u hu)
    have saved := lookup_along ex hu old
    rw [fixed u hu] at current
    exact Option.some.inj (current.symm.trans saved)
  let p : Packet := ⟨(trace t).number, (trace t).value⟩
  have sends : Frequently (fun u => EmitsData (trace u) (actions u) p) := by
    intro k
    obtain ⟨u, hu, action⟩ := fair.ticks (max k t)
    have ht : t ≤ u := (Nat.le_max_right k t).trans hu
    refine ⟨u, (Nat.le_max_left k t).trans hu, ?_⟩
    simp [EmitsData, action, p, busy u ht, fixed u ht, value u ht]
  have receives := fair.data p sends
  have replies : Frequently (fun u => EmitsAck (trace u) (actions u) p.number) := by
    intro k
    obtain ⟨u, hu, action⟩ := receives (max k t)
    have ht : t ≤ u := (Nat.le_max_right k t).trans hu
    refine ⟨u, (Nat.le_max_left k t).trans hu, ?_⟩
    simp only [EmitsAck, action, and_true]
    change (trace t).number ≤ (trace u).expected
    rw [← fixed u ht]
    exact (invariant_along ex u).lower
  obtain ⟨u, hu, action⟩ := fair.acks p.number replies t
  have advanced : (trace (u + 1)).number = (trace t).number + 1 := by
    rw [← (execution_step ex u).2]
    simp [step, action, p, busy u hu, fixed u hu]
  have cannot := bounded (u + 1) (by omega)
  omega

theorem compiled_liveness {trace actions}
    (start : trace 0 = compiledInitial)
    (ex : compiledLTS.OmegaExecution ⟨trace⟩ ⟨actions⟩) (fair : Fair trace actions)
    (t : Nat) (pending : (trace t).busy = true) :
    ∃ u, t ≤ u ∧ (trace t).number < (trace u).number :=
  liveness ⟨start.trans compiledInitial_eq, compiledLTS_eq ▸ ex⟩ fair t pending

theorem accepted_liveness {trace actions} (ex : Execution trace actions) (fair : Fair trace actions)
    (t : Nat) (v : Int) (idle : (trace t).busy = false) (action : actions t = .submit v) :
    ∃ u, t + 1 ≤ u ∧ (trace t).number < (trace u).number ∧
      (trace t).number < (trace u).received.length := by
  have pending : (trace (t + 1)).busy = true := by
    rw [← (execution_step ex t).2]; simp [step, action, idle]
  have same : (trace (t + 1)).number = (trace t).number := by
    rw [← (execution_step ex t).2]; simp [step, action, idle]
  obtain ⟨u, hu, complete⟩ := liveness ex fair (t + 1) pending
  have inv := invariant_along ex u
  refine ⟨u, hu, ?_, ?_⟩
  · simpa [same] using complete
  · have := inv.lower; have := inv.position; omega

def witnessTrace : Nat → World
  | 0 => {}
  | 1 => { busy := true, value := 7, offered := [7], data := [⟨0, 7⟩] }
  | 2 => { busy := true, value := 7, expected := 1, offered := [7], received := [7], acks := [0] }
  | _ => { number := 1, value := 7, expected := 1, offered := [7], received := [7] }

def witnessActions : Nat → Action
  | 0 => .submit 7
  | 1 => .receive ⟨0, 7⟩
  | 2 => .acknowledge 0
  | _ => .tick

theorem witness_tail (t : Nat) (ht : 3 ≤ t) :
    witnessActions t = .tick ∧ (witnessTrace t).busy = false := by
  cases t with
  | zero => omega
  | succ t => cases t with
    | zero => omega
    | succ t => cases t with
      | zero => omega
      | succ t => exact ⟨rfl, rfl⟩

theorem witness_execution : Execution witnessTrace witnessActions := by
  refine ⟨rfl, ?_⟩
  intro t
  cases t with
  | zero => simp [lts, Enabled, step, witnessTrace, witnessActions]
  | succ t => cases t with
    | zero => simp [lts, Enabled, step, witnessTrace, witnessActions]
    | succ t => cases t with
      | zero => simp [lts, Enabled, step, witnessTrace, witnessActions]
      | succ t => exact ⟨True.intro, rfl⟩

theorem witness_fair : Fair witnessTrace witnessActions := by
  constructor
  · intro t
    exact ⟨max t 3, Nat.le_max_left _ _, (witness_tail _ (Nat.le_max_right _ _)).1⟩
  · intro p infinite
    obtain ⟨u, hu, h⟩ := infinite 3
    obtain ⟨ha, hb⟩ := witness_tail u hu
    simp [EmitsData, ha, hb] at h
  · intro n infinite
    obtain ⟨u, hu, h⟩ := infinite 3
    have ha := (witness_tail u hu).1
    simp [EmitsAck, ha] at h

theorem nonvacuous : ∃ trace actions, Execution trace actions ∧ Fair trace actions ∧
    (trace 1).busy = true ∧ (trace 3).number = 1 :=
  ⟨witnessTrace, witnessActions, witness_execution, witness_fair, rfl, rfl⟩

#print axioms submit_spec
#print axioms tick_spec
#print axioms ack_spec
#print axioms receive_spec
#print axioms safety
#print axioms compiled_safety
#print axioms compiled_liveness
#print axioms nonvacuous
#print axioms delivery_once
#print axioms accepted_liveness
end Channel
