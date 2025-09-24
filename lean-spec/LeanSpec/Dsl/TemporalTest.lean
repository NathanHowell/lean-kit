import LeanSpec.Dsl.Core
import LeanSpec.Dsl.Temporal

namespace LeanSpec
namespace Dsl
namespace TemporalTest

open System
open Temporal

def trivialSystem : System where
  Store := Nat
  Label := Unit
  Init := fun _ => True
  Next := fun s _ s' => s' = s + 1

def trivialExecution : System.Execution trivialSystem :=
  { state := fun n => n
  , label := fun _ => ()
  , init := by trivial
  , step := by intro n; simp
  }

example : Always (Σ:=trivialSystem) (fun s => s ≤ s) trivialExecution := by
  intro n; exact Nat.le_refl _

example : Eventually (Σ:=trivialSystem) (fun s => s ≥ 2) trivialExecution := by
  refine Eventually.of_exists (Σ:=trivialSystem) 2 ?_
  simp [trivialExecution]

example : LeadsTo (Σ:=trivialSystem)
    (fun s => s ≥ 0) (fun s => s ≥ 0) :=
  LeadsTo.refl (Σ:=trivialSystem) _

end TemporalTest
end Dsl
end LeanSpec
