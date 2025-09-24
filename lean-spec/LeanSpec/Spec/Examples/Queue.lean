import Lean
import LeanSpec.Dsl.Core
import LeanSpec.Dsl.Invariants
import LeanSpec.Dsl.Temporal
import LeanSpec.Dsl.Liveness

namespace LeanSpec
namespace Spec
namespace Examples

open System
open Dsl
open Temporal
open Liveness

structure QueueState where
  buffer : List Nat
  deriving Repr

inductive Label where
  | enqueue : Nat → Label
  | dequeue : Label
  deriving Repr, DecidableEq

/-- Transition relation for a single-slot queue. -/
def next : QueueState → Label → QueueState → Prop
  | ⟨buf⟩, Label.enqueue x, ⟨buf'⟩ => buf = [] ∧ buf' = [x]
  | ⟨buf⟩, Label.dequeue, ⟨buf'⟩ => buf ≠ [] ∧ buf' = []

/-- Queue specification as a Lean `System`. -/
noncomputable def queue : System :=
  { Store := QueueState
  , Label := Label
  , Init := fun s => s.buffer = []
  , Next := next
  }

@[simp] def empty (s : QueueState) : Prop := s.buffer = []
@[simp] def full (s : QueueState) : Prop := s.buffer ≠ []

lemma next_preserves_capacity {s s' : QueueState} {ℓ : Label}
    (hStep : next s ℓ s') : s'.buffer.length ≤ 1 := by
  cases s with
  | mk buf =>
    cases s' with
    | mk buf' =>
        cases ℓ with
        | enqueue x =>
            rcases hStep with ⟨_, hbuf'⟩; subst hbuf'; simp
        | dequeue =>
            rcases hStep with ⟨_, hbuf'⟩; subst hbuf'; simp

lemma safety : System.Invariant (Σ:=queue) (fun s => s.buffer.length ≤ 1) := by
  inv_auto
  · intro s hs; subst hs; simp
  · intro s ℓ s' hInv hStep
    cases s with
    | mk buf =>
        cases s' with
        | mk buf' =>
            simpa using next_preserves_capacity (s:=⟨buf⟩) (s':=⟨buf'⟩) hStep

lemma dequeue_eventually_empty :
    Ensures (Σ:=queue) full empty := by
  intro ρ n hn
  have hstep := ρ.step n
  dsimp [queue, next] at hstep
  dsimp [full, queue] at hn
  cases hstate : ρ.state n with
  | mk buf =>
      have hbuf : buf ≠ [] := by simpa [full, hstate] using hn
      cases hnext : ρ.state (n.succ) with
      | mk buf' =>
          cases hlabel : ρ.label n with
          | enqueue x =>
              have hstep' : buf = [] ∧ buf' = [x] := by
                simpa [hstate, hnext, hlabel] using hstep
              exact (hbuf hstep'.1).elim
          | dequeue =>
              have hstep' : buf ≠ [] ∧ buf' = [] := by
                simpa [hstate, hnext, hlabel] using hstep
              refine ⟨n + 1, Nat.le_succ _, ?_⟩
              simp [empty, hnext, hstep'.2]

end Examples
end Spec
end LeanSpec
