import LeanSpec.Dsl.Invariants
import LeanSpec.Dsl.Core

namespace LeanSpec
namespace Dsl

open System

structure Counter where
  value : Nat
  deriving Repr

def boundedCounter : System where
  Store := Counter
  Label := Unit
  Init := fun s => s.value = 0
  Next := fun _ _ s' => s'.value ≤ 1

lemma boundedCounter_invariant :
    System.Invariant (Σ:=boundedCounter) (fun s => s.value ≤ 1) := by
  inv_auto
  · intro s hs
    simpa [boundedCounter, hs]
  · intro s _ s' _ hstep
    simpa [boundedCounter] using hstep

example :
    System.Invariant (Σ:=boundedCounter) (fun s => s.value ≤ 1) :=
  boundedCounter_invariant

end Dsl
end LeanSpec
