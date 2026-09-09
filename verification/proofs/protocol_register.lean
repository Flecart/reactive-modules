open ReactiveModules ReactiveModules.Protocol ProtocolArtifact
namespace Register

theorem nonnegative : obligation0 := by
  have stronger : ∀ s, Reachable model inputDomain s →
      s.length = 1 ∧ 0 ≤ environment s 0 := by
    intro s h
    induction h with
    | initial i hi =>
      simp [model, Model.start, initGraph, initBlocks, Graph.run, executeWires,
        Expr.eval, environment, ReactiveModules.update]
    | advance s i _ hi ih =>
      obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp ih.1
      cases i with
      | nil => simp [inputDomain] at hi
      | cons w rest =>
        cases rest with
        | nil => simp [inputDomain] at hi
        | cons offered tail =>
          have ht : tail = [] := by simpa [inputDomain] using hi.1
          subst tail
          have hx : 0 ≤ x := by simpa [environment] using ih.2
          have hv : 0 ≤ offered := by simpa [inputDomain, environment] using hi.2.2
          simp [model, Model.step, updateGraph, updateBlocks, Graph.run, executeWires,
            Expr.eval, environment, ReactiveModules.update]
          split <;> assumption
  intro s h
  have hs := (stronger s h).2
  simpa [formula0, Expr.eval, Bin.eval, flag] using hs
end Register
