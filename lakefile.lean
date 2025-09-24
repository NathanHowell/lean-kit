import Lake
open Lake DSL

namespace InitSpecScript

structure Options where
  capability : String
  deriving Repr

private def normalizeCapability (cap : String) : List String :=
  let sanitized := cap.trim.map (fun c => if c = '-' ∨ c = '_' then ' ' else c)
  sanitized.splitOn " " |>.filter (· ≠ "")

private def capitalizeWord (word : String) : String :=
  match word.data with
  | [] => ""
  | c :: cs =>
      let head := String.singleton c.toUpper
      let tail := String.mk (cs.map Char.toLower)
      head ++ tail

private def moduleNameOf (cap : String) : String :=
  (normalizeCapability cap).map capitalizeWord |>.foldl (· ++ ·) ""

private def specPath (cap : String) : System.FilePath :=
  ("lean-spec" : System.FilePath) / "LeanSpec" / "Spec" / s!"{moduleNameOf cap}.lean"

private def planPath (cap : String) : System.FilePath :=
  ("docs" : System.FilePath) / "plan" / s!"{cap}.md"

private def capabilityDocPath (cap : String) : System.FilePath :=
  ("docs" : System.FilePath) / "capabilities" / s!"{cap}.md"

private def joinArgs (args : List String) : String :=
  args.foldl (fun acc a => if acc = "" then a else acc ++ " " ++ a) ""

private def parseArgs : List String → Except String Options
  | [] => .error "expected `--cap <name>`"
  | "--cap" :: cap :: rest =>
      if rest = [] then
        .ok { capability := cap }
      else
        .error s!"unexpected arguments: {joinArgs rest}"
  | arg :: _ => .error s!"unknown argument `{arg}`"

private def specTemplate (opts : Options) : String :=
  let moduleName := moduleNameOf opts.capability
  let lines := [
    "import LeanSpec.Dsl.Core"
  , ""
  , "namespace LeanSpec"
  , "namespace Spec"
  , s!"namespace {moduleName}"
  , ""
  , s!"/-- Auto-generated stub for capability `{opts.capability}`."
  , "Fill this module with Init/Next definitions and obligations. -/"
  , "def placeholder : Unit := ()"
  , ""
  , s!"end {moduleName}"
  , "end Spec"
  , "end LeanSpec"
  ]
  String.intercalate "
" lines

private def planTemplate (opts : Options) : String :=
  let moduleName := moduleNameOf opts.capability
  let lines := [
    s!"# Plan — {moduleName}"
  , ""
  , s!"- [ ] Req `{moduleName}.init`: Define the initial state predicate."
  , s!"- [ ] Req `{moduleName}.next`: Define the next-state transition relation."
  , s!"- [ ] Req `{moduleName}.invariant`: State and prove the primary safety invariant."
  , s!"- [ ] Req `{moduleName}.liveness`: Identify the liveness obligation and proof approach."
  ]
  String.intercalate "
" lines

private def ensureCapabilityDocExists (opts : Options) : IO Unit := do
  let docPath := capabilityDocPath opts.capability
  let docExists ← System.FilePath.pathExists docPath
  if !docExists then
    throw <| IO.userError s!"Capability doc not found: {docPath}"

private def writeIfMissing (path : System.FilePath) (contents : String) : IO Bool := do
  let pathExists ← System.FilePath.pathExists path
  if pathExists then
    pure false
  else
    match path.parent with
      | some dir => IO.FS.createDirAll dir
      | none => pure ()
    IO.FS.writeFile path contents
    pure true

private def logCreation (label : String) (created : Bool) : IO Unit :=
  if created then
    IO.println s!"Created {label}"
  else
    IO.println s!"Skipped {label}; already exists"

def run (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .error err => do
      IO.eprintln s!"init:spec: {err}"
      pure 1
  | .ok opts => do
      ensureCapabilityDocExists opts
      let specCreated ← writeIfMissing (specPath opts.capability) (specTemplate opts)
      let planCreated ← writeIfMissing (planPath opts.capability) (planTemplate opts)
      logCreation (toString (specPath opts.capability)) specCreated
      logCreation (toString (planPath opts.capability)) planCreated
      pure 0

end InitSpecScript

package «lean-kit» where
  -- Add package configuration options here.

@[default_target]
lean_lib LeanSpec where
  srcDir := "lean-spec"
  -- Library-wide configuration lives here.

lean_exe cli where
  root := `LeanSpec.Cli.Main
  srcDir := "lean-spec"
  supportInterpreter := true
  -- The CLI will be implemented in subsequent iterations.

script initSpec (args) do
  let exit ← InitSpecScript.run args
  if exit == 0 then
    return 0
  else
    return exit

