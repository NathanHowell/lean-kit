import LeanSpec.Dsl.Explorer.Scope
import LeanSpec.Dsl.Explorer.Search
import LeanSpec.Dsl.Core

namespace LeanSpec
namespace Dsl
namespace Explorer

open System

structure NatCounter where
  value : Nat
  deriving BEq, Hashable, Repr

def natSystem : System where
  Store := NatCounter
  Label := Nat
  Init := fun s => s.value = 0
  Next := fun s ℓ s' => s'.value = s.value + ℓ

private def succFn : NatCounter → List (Nat × NatCounter)
  | ⟨n⟩ =>
      [ (1, ⟨n + 1⟩)
      , (2, ⟨n + 2⟩)
      ]

private def goal : NatCounter → Bool
  | ⟨n⟩ => n ≥ 3

@[simp] def cfg : Config natSystem := {}

example :
    bfs cfg succFn ⟨0⟩ goal = some ⟨[(1, ⟨1⟩), (2, ⟨3⟩)]⟩ := by
  rfl

end Explorer
end Dsl
end LeanSpec
