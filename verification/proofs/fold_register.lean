import Certificate

open ReactiveModules Verified
namespace FoldRegister

def environment (state a b c : Int) : Nat → Int :=
  fun i => if i = 0 then state else if i = 1 then a else if i = 2 then b else if i = 3 then c else 0

def higher (a b : Int) : Int := if b > a then b else a

theorem step_spec (state a b c : Int) :
    step_graph.run (environment state a b c) = [higher (higher (higher state a) b) c] := by
  rw [step_correct]
  simp [step_source, Source.run, Source.exec, each, updateMany, update,
    Expr.eval, Bin.eval, flag, environment, higher, ite_apply]

def advance (state a b c : Int) : Int :=
  (step_graph.run (environment state a b c))[0]?.getD 0

theorem higher_left (a b : Int) : a ≤ higher a b := by
  unfold higher
  split <;> omega

theorem higher_right (a b : Int) : b ≤ higher a b := by
  unfold higher
  split <;> omega

theorem never_decreases (state a b c : Int) : state ≤ advance state a b c := by
  simp only [advance, step_spec, List.getElem?_cons_zero, Option.getD_some]
  exact le_trans (le_trans (higher_left state a) (higher_left (higher state a) b))
    (higher_left (higher (higher state a) b) c)

theorem covers_offers (state a b c : Int) :
    a ≤ advance state a b c ∧ b ≤ advance state a b c ∧ c ≤ advance state a b c := by
  simp only [advance, step_spec, List.getElem?_cons_zero, Option.getD_some]
  exact ⟨le_trans (le_trans (higher_right state a) (higher_left (higher state a) b))
    (higher_left (higher (higher state a) b) c),
    le_trans (higher_right (higher state a) b) (higher_left (higher (higher state a) b) c),
    higher_right (higher (higher state a) b) c⟩

#print axioms never_decreases
#print axioms covers_offers
end FoldRegister
