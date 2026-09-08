import Certificate

open ReactiveModules Verified
namespace Register

def environment (state offered : Int) : Nat → Int :=
  fun i => if i = 0 then state else if i = 1 then offered else 0

theorem step_spec (state offered : Int) :
    step_graph.run (environment state offered) = [if offered > state then offered else state] := by
  rw [step_correct]
  by_cases h : state < offered <;>
    simp [step_source, Source.run, Source.exec, Expr.eval, Bin.eval, flag, environment, h]

def advance (state offered : Int) : Int :=
  (step_graph.run (environment state offered))[0]?.getD 0

theorem never_decreases (state offered : Int) : state ≤ advance state offered := by
  simp only [advance, step_spec]
  split <;> simp_all <;> omega

theorem covers_offer (state offered : Int) : offered ≤ advance state offered := by
  simp only [advance, step_spec]
  split <;> simp_all <;> omega

theorem returns_an_input (state offered : Int) :
    advance state offered = state ∨ advance state offered = offered := by
  simp only [advance, step_spec]
  split <;> simp_all

#print axioms never_decreases
#print axioms covers_offer
#print axioms returns_an_input
end Register
