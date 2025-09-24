import System

namespace LeanSpec
namespace Cli
namespace Gen

open System

structure InitSpecOptions where
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

private def specPath (cap : String) : FilePath :=
  ("lean-spec" : FilePath) / "LeanSpec" / "Spec" / s!"{moduleNameOf cap}.lean"

private def planPath (cap : String) : FilePath :=
  ("docs" : FilePath) / "plan" / s!"{cap}.md"

private def capabilityDocPath (cap : String) : FilePath :=
  ("docs" : FilePath) / "capabilities" / s!"{cap}.md"

private def joinArgs (args : List String) : String :=
  args.foldl (fun acc a => if acc = "" then a else acc ++ " " ++ a) ""

def parseInitSpecArgs : List String → Except String InitSpecOptions
  | [] => .error "expected `--cap <name>`"
  | "--cap" :: cap :: rest =>
      if rest = [] then
        .ok { capability := cap }
      else
        .error s!"unexpected arguments: {joinArgs rest}"
  | arg :: _ => .error s!"unknown argument `{arg}`"

private def specTemplate (opts : InitSpecOptions) : String :=
  let moduleName := moduleNameOf opts.capability
  s!"""import LeanSpec.Dsl.Core

namespace LeanSpec
namespace Spec
namespace {moduleName}

/-- Auto-generated stub for capability `{opts.capability}`.
Fill this module with Init/Next definitions and obligations. -/
def placeholder : Unit := ()

end {moduleName}
end Spec
end LeanSpec
"""

private def planTemplate (opts : InitSpecOptions) : String :=
  let moduleName := moduleNameOf opts.capability
  s!"""# Plan — {moduleName}

- [ ] Req `{moduleName}.init`: Define the initial state predicate.
- [ ] Req `{moduleName}.next`: Define the next-state transition relation.
- [ ] Req `{moduleName}.invariant`: State and prove the primary safety invariant.
- [ ] Req `{moduleName}.liveness`: Identify the liveness obligation and proof approach.
"""

private def ensureCapabilityDocExists (opts : InitSpecOptions) : IO Unit := do
  let docPath := capabilityDocPath opts.capability
  let exists ← IO.FS.pathExists docPath
  if !exists then
    throw <| IO.userError s!"Capability doc not found: {docPath}"

private def writeIfMissing (path : FilePath) (contents : String) : IO Bool := do
  let exists ← IO.FS.pathExists path
  if exists then
    pure false
  else
    IO.FS.createDirAll path.parent
    IO.FS.writeFile path contents
    pure true

private def logCreation (label : String) (created : Bool) : IO Unit :=
  if created then
    IO.println s!"Created {label}"
  else
    IO.println s!"Skipped {label}; already exists"

/-- Entry point used by CLI and Lake scripts to initialise a spec module. -/
def runInitSpec (args : List String) : IO UInt32 := do
  match parseInitSpecArgs args with
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

end Gen
end Cli
end LeanSpec
