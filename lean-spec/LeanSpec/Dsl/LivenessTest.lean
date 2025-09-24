import LeanSpec.Dsl.Liveness
import LeanSpec.Dsl.Core
import LeanSpec.Dsl.Temporal

namespace LeanSpec
namespace Dsl
namespace LivenessTest

open System
open Temporal
open Liveness

def trivialSystem : System where
  Store := Nat
  Label := Unit
  Init := fun _ => True
  Next := fun s _ s' => s' = s + 1

lemma ensures_growth :
    Ensures (Σ:=trivialSystem) (fun s => s ≥ 0) (fun s => s ≥ 0) :=
  LeadsTo.refl (Σ:=trivialSystem) _

lemma ensures_trans_example :
    Ensures (Σ:=trivialSystem) (fun s => s ≥ 0) (fun s => s ≥ 0) :=
  ensures_trans (Σ:=trivialSystem) ensures_growth ensures_growth

end LivenessTest
end Dsl
end LeanSpec
