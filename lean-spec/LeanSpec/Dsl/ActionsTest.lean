import LeanSpec.Dsl.Actions
import LeanSpec.Dsl.Composition

namespace LeanSpec
namespace Dsl

open System
open System.Action
open System.LabeledAction

def boolSystem : System where
  Store := Bool
  Label := Unit
  Init := fun _ => True
  Next := fun _ _ _ => True

example :
    Action.seq (Σ:=boolSystem) Action.skip
      (Action.assign (Σ:=boolSystem) fun s : Bool => not s)
      = Action.assign (Σ:=boolSystem) (fun s => not s) := by
  simpa using Action.seq_skip_left (Σ:=boolSystem)
    (Action.assign (Σ:=boolSystem) fun s : Bool => not s)

example (s : Bool) :
    Action.enabled (Σ:=boolSystem)
      (Action.guarded (fun _ => True)
        (Action.assign (Σ:=boolSystem) fun s : Bool => not s)) s := by
  have base := Action.assign_enabled (Σ:=boolSystem) (fun s : Bool => not s) s
  have := (Action.enabled_guarded (Σ:=boolSystem)
    (g := fun _ => True)
    (a := Action.assign (Σ:=boolSystem) fun s : Bool => not s)
    (s := s)).mpr ⟨trivial, base⟩
  simpa using this

def flipLabel : LabeledAction boolSystem :=
  { label := ()
  , action := Action.assign (Σ:=boolSystem) fun s : Bool => not s }

def waitLabel : LabeledAction boolSystem :=
  { label := ()
  , action := Action.skip (Σ:=boolSystem) }

example (s : Bool) :
    compile [flipLabel] s () (not s) := by
  simp [compile, flipLabel]

example (s : Bool) :
    compile (flipLabel :: [waitLabel]) s () s := by
  refine ⟨waitLabel, ?_, rfl, ?_⟩
  · simp [waitLabel]
  · simp [waitLabel]

end Dsl
end LeanSpec
