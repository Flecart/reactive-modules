import Std

namespace ReactiveModules

/-- Mathematical integers; Boolean values have the representation 0/1. -/
inductive Bin where
  | add | sub | eq | ne | lt | le | gt | ge | and | or | xor
  deriving Repr, DecidableEq

def flag (p : Bool) : Int := if p then 1 else 0

def Bin.eval : Bin → Int → Int → Int
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .eq, a, b => flag (a == b)
  | .ne, a, b => flag (a != b)
  | .lt, a, b => flag (a < b)
  | .le, a, b => flag (a ≤ b)
  | .gt, a, b => flag (a > b)
  | .ge, a, b => flag (a ≥ b)
  | .and, a, b => flag (a != 0 && b != 0)
  | .or, a, b => flag (a != 0 || b != 0)
  | .xor, a, b => flag ((a != 0) != (b != 0))

inductive Expr where
  | lit (value : Int)
  | boolean (value : Bool)
  | var (slot : Nat)
  | bin (op : Bin) (left right : Expr)
  | not (value : Expr)
  | ite (condition yes no : Expr)
  deriving Repr, DecidableEq

def Expr.eval (env : Nat → Int) : Expr → Int
  | .lit n => n
  | .boolean b => flag b
  | .var n => env n
  | .bin op a b => op.eval (a.eval env) (b.eval env)
  | .not a => flag (a.eval env == 0)
  | .ite c a b => if c.eval env != 0 then a.eval env else b.eval env

def Expr.subst (env : Nat → Expr) : Expr → Expr
  | .lit n => .lit n
  | .boolean b => .boolean b
  | .var n => env n
  | .bin op a b => .bin op (a.subst env) (b.subst env)
  | .not a => .not (a.subst env)
  | .ite c a b => .ite (c.subst env) (a.subst env) (b.subst env)

theorem Expr.subst_correct (e : Expr) (env : Nat → Expr) (inputs : Nat → Int) :
    (e.subst env).eval inputs = e.eval (fun n => (env n).eval inputs) := by
  induction e <;> simp_all [subst, eval]

def update (env : Nat → α) (slot : Nat) (value : α) : Nat → α :=
  fun n => if n = slot then value else env n

def updateMany (env : Nat → α) : List Nat → List α → Nat → α
  | n :: ns, v :: vs => updateMany (update env n v) ns vs
  | _, _ => env

/-- Iterate over a snapshot of a fixed tuple. A return in the body discards
    the remaining iterations, just as it discards any other continuation. -/
def each (body : (Nat → α) → ((Nat → α) → Nat → α) → Nat → α)
    (slots : List Nat) (rows : List (List α)) (env : Nat → α)
    (next : (Nat → α) → Nat → α) : Nat → α :=
  match rows with
  | [] => next env
  | row :: rest => body (updateMany env slots row) (fun env' => each body slots rest env' next)

theorem eval_updateMany (env : Nat → Expr) (inputs : Nat → Int)
    (slots : List Nat) (values : List Expr) :
    (fun i => (updateMany env slots values i).eval inputs) =
      updateMany (fun i => (env i).eval inputs) slots (values.map (Expr.eval inputs)) := by
  induction slots generalizing env values with
  | nil => rfl
  | cons n ns ih =>
    cases values with
    | nil => rfl
    | cons v vs =>
      simp only [updateMany, List.map_cons, ih]
      congr 1
      funext i
      simp only [update]
      split <;> rfl

/-- Structured source statements. Sequencing and early return remain in the source AST. -/
inductive Source where
  | skip
  | assign (slot : Nat) (value : Expr)
  | assignMany (slots : List Nat) (values : List Expr)
  | ret (values : List Expr)
  | branch (condition : Expr) (yes no : Source)
  | seq (first rest : Source)
  | call (targets : List Nat) (body : Source)
  | forEach (slots : List Nat) (rows : List (List Expr)) (body : Source)
  deriving Repr, DecidableEq

/-- Continuation semantics: return discards the continuation, assignment does not.
    Fixed record/tuple layouts determine the number of observable result slots. -/
def Source.exec (env : Nat → Int) (next : (Nat → Int) → Nat → Int) : Source → Nat → Int
  | .skip => next env
  | .assign n e => next (update env n (e.eval env))
  | .assignMany ns es => next (updateMany env ns (es.map (Expr.eval env)))
  | .ret values => fun i => (values[i]?.getD (.lit 0)).eval env
  | .branch c a b => if c.eval env != 0 then a.exec env next else b.exec env next
  | .seq a b => a.exec env (fun env' => b.exec env' next)
  | .call targets body =>
      next (updateMany env targets ((List.range targets.length).map (body.exec env id)))
  | .forEach slots rows body =>
      each (fun env next => body.exec env next) slots
        (rows.map (fun row => row.map (Expr.eval env))) env next

/-- Canonical lowering: eliminate locals, sequencing and return into RM expressions.
    This definition, not the Python candidate emitter, is the reference compiler. -/
def Source.lower (env : Nat → Expr) (next : (Nat → Expr) → Nat → Expr) : Source → Nat → Expr
  | .skip => next env
  | .assign n e => next (update env n (e.subst env))
  | .assignMany ns es => next (updateMany env ns (es.map (Expr.subst env)))
  | .ret values => fun i => (values[i]?.getD (.lit 0)).subst env
  | .branch c a b => fun i => .ite (c.subst env) (a.lower env next i) (b.lower env next i)
  | .seq a b => a.lower env (fun env' => b.lower env' next)
  | .call targets body =>
      next (updateMany env targets ((List.range targets.length).map (body.lower env id)))
  | .forEach slots rows body =>
      each (fun env next => body.lower env next) slots
        (rows.map (fun row => row.map (Expr.subst env))) env next

theorem eval_update (env : Nat → Expr) (inputs : Nat → Int) (n : Nat) (e : Expr) :
    (fun i => (update env n (e.subst env) i).eval inputs) =
      update (fun i => (env i).eval inputs) n (e.eval (fun i => (env i).eval inputs)) := by
  funext i
  simp only [update]
  split <;> simp [Expr.subst_correct]

theorem Source.lower_correct (s : Source) (env : Nat → Expr) (inputs : Nat → Int)
    (next : (Nat → Expr) → Nat → Expr) (cont : (Nat → Int) → Nat → Int)
    (h : ∀ e i, (next e i).eval inputs = cont (fun n => (e n).eval inputs) i) (i : Nat) :
    (s.lower env next i).eval inputs = s.exec (fun n => (env n).eval inputs) cont i := by
  induction s generalizing env next cont i with
  | skip => exact h env i
  | assign n e => simpa only [lower, exec, eval_update] using h (update env n (e.subst env)) i
  | assignMany ns es =>
    simpa only [lower, exec, eval_updateMany, List.map_map, Function.comp_def, Expr.subst_correct] using
      h (updateMany env ns (es.map (Expr.subst env))) i
  | ret values => exact Expr.subst_correct _ _ _
  | branch c a b ha hb =>
    simp only [lower, Expr.eval, Expr.subst_correct, exec]
    split
    · exact ha env next cont h i
    · exact hb env next cont h i
  | seq a b ha hb =>
    exact ha env (fun e => b.lower e next) (fun e => b.exec e cont)
      (fun e j => hb e next cont h j) i
  | call targets body ih =>
    simp only [lower, exec]
    rw [h, eval_updateMany, List.map_map]
    congr 2
    apply List.map_congr_left
    intro j _
    exact ih env id id (fun _ _ => rfl) j
  | forEach slots rows body ih =>
    have loop (rs : List (List Expr)) (e : Nat → Expr) :
        (each (fun env next => body.lower env next) slots rs e next i).eval inputs =
        each (fun env next => body.exec env next) slots
          (rs.map (fun row => row.map (Expr.eval inputs)))
          (fun n => (e n).eval inputs) cont i := by
      induction rs generalizing e i with
      | nil => exact h e i
      | cons row rest hr =>
        simp only [each, List.map_cons]
        rw [ih _ _ (fun env => each (fun env next => body.exec env next) slots
          (rest.map (fun row => row.map (Expr.eval inputs))) env cont)
          (fun e j => hr (e := e) (i := j)), eval_updateMany]
    simpa only [lower, exec, List.map_map, Function.comp_def, Expr.subst_correct] using
      loop (rows.map (fun row => row.map (Expr.subst env))) env

def Source.compiled (s : Source) (outputs : Nat) : List Expr :=
  (List.range outputs).map (s.lower Expr.var id)

def Source.run (s : Source) (inputs : Nat → Int) (outputs : Nat) : List Int :=
  (List.range outputs).map (s.exec inputs id)

theorem Source.compiled_correct (s : Source) (inputs : Nat → Int) (outputs : Nat) :
    (s.compiled outputs).map (Expr.eval inputs) = s.run inputs outputs := by
  simp only [compiled, run, List.map_map]
  congr 1
  funext i
  exact s.lower_correct Expr.var inputs id id (fun _ _ => rfl) i

/-- A concrete RM wire graph. Instructions append a single fresh wire. -/
structure Graph where
  inputs : Nat
  terms : List Expr
  outputs : List Nat
  deriving Repr, DecidableEq

def graphBody (cursor : Nat) (terms : List Expr) (outputs : List Nat) : Source :=
  match terms with
  | [] => .ret (outputs.map Expr.var)
  | term :: rest => .seq (.assign cursor term) (graphBody (cursor + 1) rest outputs)

def Graph.source (g : Graph) : Source := graphBody g.inputs g.terms g.outputs

/-- Integer wire execution, independent of the source-to-expression lowering. -/
def executeWires (cursor : Nat) (terms : List Expr) (env : Nat → Int) : Nat → Int :=
  match terms with
  | [] => env
  | term :: rest => executeWires (cursor + 1) rest (update env cursor (term.eval env))

theorem graphBody_correct (terms : List Expr) (cursor : Nat) (outputs : List Nat)
    (env : Nat → Int) (cont : (Nat → Int) → Nat → Int) (i : Nat) :
    (graphBody cursor terms outputs).exec env cont i =
      match outputs[i]? with
      | some n => executeWires cursor terms env n
      | none => 0 := by
  induction terms generalizing cursor env with
  | nil =>
    simp only [graphBody, Source.exec, List.getElem?_map, executeWires]
    split <;> simp_all [Expr.eval]
  | cons t ts ih => exact ih (cursor + 1) (update env cursor (t.eval env))

def Graph.run (g : Graph) (env : Nat → Int) : List Int :=
  g.outputs.map (executeWires g.inputs g.terms env)

theorem Graph.source_correct (g : Graph) (env : Nat → Int) :
    g.source.run env g.outputs.length = g.run env := by
  apply List.ext_getElem
  · simp [Source.run, Graph.run]
  · intro i h₁ h₂
    simp only [Source.run, List.getElem_map, List.getElem_range, Graph.source,
      graphBody_correct, Graph.run]
    have hi : i < g.outputs.length := by simpa [Source.run] using h₁
    simp [List.getElem?_eq_getElem hi]

/-- Certification compares actual RM expansion with the proved canonical lowering. -/
def Certifies (s : Source) (g : Graph) : Prop :=
  s.compiled g.outputs.length = g.source.compiled g.outputs.length

theorem certified_correct (s : Source) (g : Graph) (h : Certifies s g) (env : Nat → Int) :
    g.run env = s.run env g.outputs.length := by
  rw [← g.source_correct env, ← Source.compiled_correct, ← h]
  exact s.compiled_correct env g.outputs.length

end ReactiveModules
