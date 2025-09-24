import Lean
import LeanSpec.Dsl.Core
import LeanSpec.Dsl.Invariants

namespace LeanSpec
namespace Spec
namespace Examples

open Lean
open System
open Dsl

inductive Label where
  | acquire : Nat → Label
  | release : Nat → Label
  deriving Repr, DecidableEq

abbrev Store := List Nat

/-- Next-state relation for the mutex. -/
def next : Store → Label → Store → Prop
  | s, Label.acquire wid, s' =>
      (s = [] ∧ s' = [wid]) ∨ (s ≠ [] ∧ s' = s)
  | s, Label.release wid, s' =>
      (s.head? = some wid ∧ s' = []) ∨ (s.head? ≠ some wid ∧ s' = s)

/-- Mutex specification as a Lean `System`. -/
noncomputable def mutex : System :=
  { Store := Store
  , Label := Label
  , Init := fun s => s = []
  , Next := next
  }

@[simp] def atMostOne (s : Store) : Prop := s.length ≤ 1

lemma next_preserves_atMostOne {s s' : Store} {ℓ : Label}
    (hInv : atMostOne s) (hStep : next s ℓ s') : atMostOne s' := by
  cases ℓ with
  | acquire wid =>
      rcases hStep with h | h
      · rcases h with ⟨hs, hs'⟩; subst hs; subst hs'; simp [atMostOne]
      · rcases h with ⟨_, hs'⟩; subst hs'; simpa [atMostOne] using hInv
  | release wid =>
      rcases hStep with h | h
      · rcases h with ⟨_, hs'⟩; subst hs'; simp [atMostOne]
      · rcases h with ⟨_, hs'⟩; subst hs'; simpa [atMostOne] using hInv

/-- Safety: the mutex never allows more than one active holder. -/
lemma safety : System.Invariant (Σ:=mutex) atMostOne := by
  inv_auto
  · intro s hs; subst hs; simp [mutex, atMostOne]
  · intro s ℓ s' hInv hStep
    have : next s ℓ s' := by simpa [mutex, next]
    exact next_preserves_atMostOne hInv this

end Examples
end Spec
end LeanSpec
