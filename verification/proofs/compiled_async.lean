import Certificate

open ReactiveModules Verified
namespace AsyncDictionary

def finish (key value : Int) : Heap.Store × Coroutine.State :=
  Coroutine.runTickets (Coroutine.compiledSegment coroutine_blocks) []
    (Coroutine.initial (Coroutine.compiledSegment coroutine_blocks) 0 [key, value])
    [(0, 0), (0, 1), (0, 2)]

/-- The directly compiled async handler retrieves the value it stored, for
    all integer keys/values, through the declared unbounded heap service. -/
theorem round_trip (key value : Int) :
    (finish key value).2.phase = .done [value] := by
  unfold finish
  rw [funext coroutine_segment_correct]
  simp [Coroutine.initial, Coroutine.runTickets, Coroutine.sourceSegment,
    Coroutine.segment, Coroutine.sourceRun, Coroutine.environment, coroutine_blocks,
    Effects.advance, Effects.serve, Effects.resume,
    step_stage_0_source, step_stage_1_source, step_stage_2_source, step_stage_3_source,
    Source.run, Source.exec, Expr.eval,
    Heap.apply, Heap.execute, Heap.allocate, Heap.access, Heap.replace, Heap.put, Heap.lookup,
    List.range_succ, Pure.pure, Bind.bind, Except.pure, Except.bind]

#print axioms round_trip
end AsyncDictionary
