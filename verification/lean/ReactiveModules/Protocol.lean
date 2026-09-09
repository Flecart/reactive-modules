import ReactiveModules.Compiler
import Cslib.Foundations.Semantics.LTS.Basic

namespace ReactiveModules.Protocol

def environment (values : List Int) : Nat → Int := fun i => values[i]?.getD 0

def bounded (bound : Nat) : Expr → Bool
  | .var n => n < bound
  | .lit _ | .boolean _ => true
  | .not a => bounded bound a
  | .bin _ a b => bounded bound a && bounded bound b
  | .ite c a b => bounded bound c && bounded bound a && bounded bound b

theorem eval_agrees (e : Expr) (n : Nat) (a b : Nat → Int)
    (bound : bounded n e = true) (agree : ∀ i < n, a i = b i) : e.eval a = e.eval b := by
  induction e with
  | var i => exact agree i (by simpa [bounded] using bound)
  | lit _ | boolean _ => rfl
  | not e ih => simp only [Expr.eval, ih bound]
  | bin o x y hx hy =>
    simp only [bounded, Bool.and_eq_true] at bound
    simp only [Expr.eval, hx bound.1, hy bound.2]
  | ite c x y hc hx hy =>
    simp only [bounded, Bool.and_eq_true] at bound
    simp only [Expr.eval, hc bound.1.1, hx bound.1.2, hy bound.2]

/-- Values are supplied by an untrusted evaluator. Every term equation and
    backward wire dependency is independently checked in the kernel. -/
def checkedTerms (values : Array Int) (cursor : Nat) : List Expr → Bool
  | [] => true
  | e :: rest => bounded cursor e &&
      (e.eval (fun n => values[n]?.getD 0) == values[cursor]?.getD 0) &&
      checkedTerms values (cursor+1) rest

theorem checkedTerms_correct (terms : List Expr) (values : Array Int)
    (cursor : Nat) (env : Nat → Int)
    (checked : checkedTerms values cursor terms = true)
    (initially : ∀ n < cursor, env n = values[n]?.getD 0) :
    ∀ n < cursor + terms.length,
      executeWires cursor terms env n = values[n]?.getD 0 := by
  induction terms generalizing cursor env with
  | nil => simpa [executeWires] using initially
  | cons e rest ih =>
    simp only [checkedTerms, Bool.and_eq_true, beq_iff_eq] at checked
    have he : e.eval env = values[cursor]?.getD 0 :=
      (eval_agrees e cursor env _ checked.1.1 initially).trans checked.1.2
    have hp : ∀ n < cursor+1, ReactiveModules.update env cursor (e.eval env) n = values[n]?.getD 0 := by
      intro n hn
      by_cases h : n = cursor
      · simpa [ReactiveModules.update, h] using he
      · simp only [ReactiveModules.update, if_neg h]
        exact initially n (by omega)
    simpa [executeWires, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ih (cursor+1) (ReactiveModules.update env cursor (e.eval env)) checked.2 hp

def checkedRun (g : Graph) (env : Nat → Int) (values : Array Int) : Bool :=
  (List.range g.inputs).all (fun n => env n == values[n]?.getD 0) &&
  checkedTerms values g.inputs g.terms &&
  g.outputs.all (fun n => n < g.inputs + g.terms.length)

theorem checkedRun_correct (g : Graph) (env : Nat → Int) (values : Array Int)
    (checked : checkedRun g env values = true) :
    g.run env = g.outputs.map (fun n => values[n]?.getD 0) := by
  simp only [checkedRun, Bool.and_eq_true, List.all_eq_true] at checked
  apply List.map_congr_left
  intro n hn
  apply checkedTerms_correct g.terms values g.inputs env checked.1.2
  · intro i hi
    exact of_decide_eq_true (checked.1.1 i (List.mem_range.mpr hi))
  · exact of_decide_eq_true (checked.2 n hn)

/-- Atom blocks share latched inputs and fresh next/intermediate wires. The
    exporter resolves next dependencies in RM's atom order and rejects cycles. -/
def rounds (cursor : Nat) (blocks : List (List Expr)) (env : Nat → Int) : Nat → Int :=
  match blocks with
  | [] => env
  | block :: rest => rounds (cursor + block.length) rest (executeWires cursor block env)

theorem execute_append (a b : List Expr) (cursor : Nat) (env : Nat → Int) :
    executeWires cursor (a ++ b) env =
    executeWires (cursor + a.length) b (executeWires cursor a env) := by
  induction a generalizing cursor env with
  | nil => simp [executeWires]
  | cons e es ih =>
    simp only [List.cons_append, executeWires, List.length_cons]
    rw [ih]
    congr 1 <;> omega

theorem flatten_correct (blocks : List (List Expr)) (cursor : Nat) (env : Nat → Int) :
    executeWires cursor blocks.flatten env = rounds cursor blocks env := by
  induction blocks generalizing cursor env with
  | nil => rfl
  | cons block rest ih =>
    simp only [List.flatten_cons, execute_append, rounds, ih]

structure Model where
  initial : Graph
  transition : Graph

def Model.start (m : Model) (i : List Int) : List Int := m.initial.run (environment i)
def Model.step (m : Model) (s i : List Int) : List Int :=
  m.transition.run (environment (s ++ i))

def Model.lts (m : Model) (inputDomain : List Int → Prop) : Cslib.LTS (List Int) (List Int) :=
  ⟨fun s i t => inputDomain i ∧ m.step s i = t⟩

inductive Reachable (m : Model) (inputDomain : List Int → Prop) : List Int → Prop
  | initial (i) : inputDomain i → Reachable m inputDomain (m.start i)
  | advance (s i) : Reachable m inputDomain s → inputDomain i →
      Reachable m inputDomain (m.step s i)

def Invariant (m : Model) (domain : List Int → Prop) (p : Expr) : Prop :=
  ∀ s, Reachable m domain s → p.eval (environment s) ≠ 0

def StepProperty (m : Model) (stateDomain inputDomain : List Int → Prop) (p : Expr) : Prop :=
  ∀ s i, stateDomain s → inputDomain i →
    p.eval (environment (s ++ i ++ m.step s i)) ≠ 0

def Execution (m : Model) (domain : List Int → Prop)
    (states actions : Nat → List Int) : Prop :=
  Reachable m domain (states 0) ∧ ∀ t, (m.lts domain).Tr (states t) (actions t) (states (t+1))

def LeadsTo (m : Model) (domain : List Int → Prop) (trigger goal : Expr) : Prop :=
  ∀ states actions, Execution m domain states actions →
    ∀ t, trigger.eval (environment (states t)) ≠ 0 →
      ∃ u, t ≤ u ∧ goal.eval (environment (states u)) ≠ 0

theorem invariant_of_induction (m : Model) (domain : List Int → Prop) (p : Expr)
    (initial : ∀ i, domain i → p.eval (environment (m.start i)) ≠ 0)
    (step : ∀ s i, p.eval (environment s) ≠ 0 → domain i →
      p.eval (environment (m.step s i)) ≠ 0) : Invariant m domain p := by
  intro s h
  induction h with
  | initial i hi => exact initial i hi
  | advance s i _ hi ih => exact step s i ih hi

/-- A reachable stuttering state refutes unconditional (not fair) progress. -/
theorem idle_refutes (m : Model) (domain : List Int → Prop) (trigger goal : Expr)
    (s i : List Int) (reachable : Reachable m domain s) (allowed : domain i)
    (fixed : m.step s i = s) (enabled : trigger.eval (environment s) ≠ 0)
    (absent : goal.eval (environment s) = 0) : ¬ LeadsTo m domain trigger goal := by
  intro h
  have execution : Execution m domain (fun _ => s) (fun _ => i) :=
    ⟨reachable, fun _ => ⟨allowed, fixed⟩⟩
  obtain ⟨u, _, hu⟩ := h _ _ execution 0 enabled
  exact hu absent

end ReactiveModules.Protocol
