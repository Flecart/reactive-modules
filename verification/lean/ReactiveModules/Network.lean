import Cslib.Foundations.Semantics.LTS.Basic

namespace ReactiveModules.Network

/-- Finite queues are unbounded over executions; no overflow success assumption. -/
inductive Fault (Packet : Type) where
  | deliver (packet : Packet)
  | drop (packet : Packet)
  | duplicate (packet : Packet)

def Fault.packet : Fault α → α
  | .deliver p | .drop p | .duplicate p => p

def enabled (queue : List α) (action : Fault α) : Prop := action.packet ∈ queue

def faultStep [DecidableEq α] (queue : List α) : Fault α → List α
  | .deliver p | .drop p => queue.erase p
  | .duplicate p => p :: queue

def faultLTS [DecidableEq α] : Cslib.LTS (List α) (Fault α) :=
  ⟨fun q a q' => enabled q a ∧ faultStep q a = q'⟩

/-- Network faults cannot create a payload not satisfying the sender's invariant. -/
theorem faults_preserve [DecidableEq α] (p : α → Prop) (q : List α) (a : Fault α)
    (valid : ∀ x ∈ q, p x) (allowed : enabled q a) : ∀ x ∈ faultStep q a, p x := by
  cases a with
  | deliver packet | drop packet =>
    intro x hx
    exact valid x (List.mem_of_mem_erase hx)
  | duplicate packet =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact valid _ allowed
    · exact valid x hx

def Frequently (p : Nat → Prop) : Prop := ∀ t, ∃ u, t ≤ u ∧ p u

/-- Fair loss: infinitely retransmitted messages are received infinitely often.
    No guarantee is imposed on a message transmitted only finitely many times. -/
def FairLoss (sent received : Nat → Packet → Prop) : Prop :=
  ∀ p, Frequently (fun t => sent t p) → Frequently (fun t => received t p)

end ReactiveModules.Network
