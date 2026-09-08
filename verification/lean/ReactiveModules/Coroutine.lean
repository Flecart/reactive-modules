import ReactiveModules.Compiler
import ReactiveModules.Validation
import ReactiveModules.Effects

namespace ReactiveModules.Coroutine

/-- Each boundary is part of the declared source interface, not inferred from
    an unchecked RM graph. Await outputs are [reference, key, value] ++ frame. -/
structure Block where
  source : Source
  graph : Graph
  outputs : Nat
  effect : Option Heap.Operation

structure Interface where
  inputs : List ScalarSort
  outputs : List ScalarSort
  suspends : Bool
  deriving DecidableEq

/-- Await frames flow unchanged into the next segment, followed by one integer
    response. Requests have exactly three integer payload fields. -/
def validFrames : List Interface → Bool
  | [] => false
  | [last] => !last.suspends
  | first :: next :: rest =>
    first.suspends && first.outputs.take 3 == [.int, .int, .int] &&
      first.outputs.drop 3 ++ [.int] == next.inputs && validFrames (next :: rest)

structure Frame where
  pc : Nat := 0
  values : List Int := []
  error : Option Heap.Error := none

abbrev Result := List Int
abbrev State := Effects.Machine Frame Result

def environment (values : List Int) : Nat → Int := fun i => values[i]?.getD 0

def sourceRun (block : Block) (values : List Int) : List Int :=
  block.source.run (environment values) block.outputs

def compiledRun (block : Block) (values : List Int) : List Int :=
  block.graph.run (environment values)

def segment (run : Block → List Int → List Int) (blocks : List Block)
    (frame : Frame) : Effects.Phase Frame Result :=
  match frame.error with
  | some error => .failed error
  | none =>
    match blocks[frame.pc]? with
    | none => .done []
    | some block =>
      let values := run block frame.values
      match block.effect with
      | none => .done values
      | some operation =>
        .waiting ⟨operation, values[0]?.getD 0, values[1]?.getD 0, values[2]?.getD 0⟩
          (fun response => match response with
            | .ok value => ⟨frame.pc + 1, values.drop 3 ++ [value], none⟩
            | .error error => ⟨frame.pc + 1, [], some error⟩)

abbrev sourceSegment := segment sourceRun
abbrev compiledSegment := segment compiledRun

def Correct (blocks : List Block) : Prop :=
  ∀ block ∈ blocks, ∀ env, block.graph.run env = block.source.run env block.outputs

theorem segment_correct (blocks : List Block) (correct : Correct blocks) (frame : Frame) :
    compiledSegment blocks frame = sourceSegment blocks frame := by
  unfold compiledSegment sourceSegment segment
  cases frame.error with
  | some error => rfl
  | none =>
    cases found : blocks[frame.pc]? with
    | none => rfl
    | some block =>
      simp only [compiledRun, sourceRun, correct block (List.mem_of_getElem? found)]

theorem serve_correct (blocks : List Block) (correct : Correct blocks)
    (heap : Heap.Store) (machine : State) (ticket : Effects.Ticket) :
    Effects.serve (compiledSegment blocks) heap machine ticket =
      Effects.serve (sourceSegment blocks) heap machine ticket :=
  Effects.serve_congr _ _ (segment_correct blocks correct) heap machine ticket

def initial (run : Frame → Effects.Phase Frame Result) (owner : Nat) (args : List Int) : State :=
  Effects.advance run ⟨owner, 0, .ready ⟨0, args, none⟩⟩

def runTickets (run : Frame → Effects.Phase Frame Result) (heap : Heap.Store)
    (machine : State) (tickets : List Effects.Ticket) : Heap.Store × State :=
  match tickets with
  | [] => (heap, machine)
  | ticket :: rest =>
    let (after, state) := Effects.serve run heap machine ticket
    runTickets run after state rest
termination_by structural tickets

theorem initial_correct (blocks : List Block) (correct : Correct blocks) (owner : Nat) (args : List Int) :
    initial (compiledSegment blocks) owner args = initial (sourceSegment blocks) owner args := by
  rw [funext (segment_correct blocks correct)]

/-- Every finite response schedule, including stale/foreign tickets. This
    composes actual RM segment equality with the unbounded heap/effect model. -/
theorem execution_correct (blocks : List Block) (correct : Correct blocks)
    (heap : Heap.Store) (machine : State) (tickets : List Effects.Ticket) :
    runTickets (compiledSegment blocks) heap machine tickets =
      runTickets (sourceSegment blocks) heap machine tickets := by
  rw [funext (segment_correct blocks correct)]

end ReactiveModules.Coroutine
