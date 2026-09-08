import Certificate

open ReactiveModules Verified
namespace RegisterBug

def environment (state offered : Int) : Nat → Int :=
  fun i => if i = 0 then state else if i = 1 then offered else 0

def Monotonicity : Prop := ∀ state offered : Int,
  state ≤ (step_graph.run (environment state offered))[0]?.getD 0

/-- The incorrect Python implementation itself yields the counterexample. -/
theorem decreases : step_graph.run (environment 5 3) = [3] := by
  rw [step_correct]
  decide

theorem monotonicity_refuted : ¬ Monotonicity := by
  intro h
  have claimed := h 5 3
  rw [decreases] at claimed
  simp at claimed

#print axioms monotonicity_refuted
end RegisterBug
