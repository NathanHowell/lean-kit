import LeanSpec.Dsl.Core

namespace LeanSpec
namespace Dsl

def toggleSystem : System where
  Store := Bool
  Label := Unit
  Init := fun s => s = false
  Next := fun s _ s' => s' = not s

open System

lemma toggleExec_init : toggleSystem.Init false := by rfl

def toggleExecution : Execution toggleSystem :=
  { state := fun n => Nat.bodd n
  , label := fun _ => ()
  , init := by
      change Nat.bodd 0 = false
      rfl
  , step := by
      intro n
      change Nat.bodd (Nat.succ n) = Bool.not (Nat.bodd n)
      simpa using Nat.bodd_succ n
  }

example : Eventually (fun s => s = true) toggleExecution := by
  refine ⟨1, ?_⟩
  change Nat.bodd 1 = true
  rfl

example : Always (fun s => s = true ∨ s = false) toggleExecution := by
  intro n
  have h : Nat.bodd n = true ∨ Nat.bodd n = false := by
    cases h' : Nat.bodd n <;> simp [h']
  simpa using h

example : Invariant (Σ := toggleSystem) (fun _ => True) := by
  intro ρ _ n
  trivial

end Dsl
end LeanSpec
