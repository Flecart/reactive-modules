import ReactiveModules.Heap

namespace ReactiveModules.Effects

open Heap

/-- One terminating segment between declared effects. This is an interface
    semantics, not an interpreter for arbitrary CPython/asyncio execution. -/
inductive Phase (State Result : Type) where
  | ready (state : State)
  | waiting (request : Request) (continuation : Response → State)
  | done (result : Result)
  | failed (error : Error)

structure Machine (State Result : Type) where
  owner : Nat
  epoch : Nat := 0
  phase : Phase State Result

abbrev Ticket := Nat × Nat

def advance (segment : State → Phase State Result) (machine : Machine State Result) : Machine State Result :=
  match machine.phase with
  | .ready state => { machine with phase := segment state }
  | _ => machine

def resume (segment : State → Phase State Result) (machine : Machine State Result)
    (ticket : Ticket) (response : Response) : Machine State Result :=
  if ticket = (machine.owner, machine.epoch) then
    match machine.phase with
    | .waiting _ continuation =>
      advance segment { machine with epoch := machine.epoch + 1, phase := .ready (continuation response) }
    | _ => machine
  else machine

/-- Validate the suspension before executing an effect, so a replay cannot
    allocate, mutate, or consume a request a second time. -/
def serve (segment : State → Phase State Result) (heap : Store) (machine : Machine State Result)
    (ticket : Ticket) : Store × Machine State Result :=
  if ticket = (machine.owner, machine.epoch) then
    match machine.phase with
    | .waiting request _ =>
      let (after, response) := Heap.apply heap request
      (after, resume segment machine ticket response)
    | _ => (heap, machine)
  else (heap, machine)

theorem stale_has_no_effect (segment : State → Phase State Result) (heap : Store)
    (machine : Machine State Result) (ticket : Ticket)
    (stale : ticket ≠ (machine.owner, machine.epoch)) :
    serve segment heap machine ticket = (heap, machine) := by
  simp [serve, stale]

theorem foreign_has_no_effect (segment : State → Phase State Result) (heap : Store)
    (machine : Machine State Result) (ticket : Ticket) (foreign : ticket.1 ≠ machine.owner) :
    serve segment heap machine ticket = (heap, machine) := by
  apply stale_has_no_effect
  intro h
  exact foreign (congrArg Prod.fst h)

theorem resume_advances_epoch (segment : State → Phase State Result) (owner epoch : Nat)
    (request : Request) (continuation : Response → State) (response : Response) :
    (resume segment ⟨owner, epoch, .waiting request continuation⟩ (owner, epoch) response).epoch = epoch + 1 := by
  simp [resume, advance]

theorem replay_has_no_effect (segment : State → Phase State Result) (heap : Store)
    (owner epoch : Nat) (request : Request) (continuation : Response → State) :
    let after := serve segment heap ⟨owner, epoch, .waiting request continuation⟩ (owner, epoch)
    serve segment after.1 after.2 (owner, epoch) = after := by
  dsimp
  apply stale_has_no_effect
  simp [serve, resume, advance]

/-- A future certified segment compiler can use this interface theorem to
    transfer request/resumption behavior; equality of the segments is required. -/
theorem serve_congr (source compiled : State → Phase State Result)
    (correct : ∀ state, compiled state = source state)
    (heap : Store) (machine : Machine State Result) (ticket : Ticket) :
    serve compiled heap machine ticket = serve source heap machine ticket := by
  have h : compiled = source := funext correct
  rw [h]

end ReactiveModules.Effects
