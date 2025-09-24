import Lean
import LeanSpec.Cli.Gen

namespace LeanSpec
namespace Cli

private def helpLines : List String :=
  [ "Lean Spec CLI"
  , ""
  , "Commands:"
  , "  help              Display this help message"
  , "  init:spec         Generate a spec stub (use `--cap <name>`)."
  , "  spec              Run specification-phase tasks (stub)."
  , "  plan              Run plan-phase tasks (stub)."
  , "  implement         Run implementation-phase tasks (stub)."
  ]

private def helpText : String :=
  String.intercalate "
" helpLines

private def unknownCmd (cmd : String) : String :=
  s!"Unknown command: {cmd}
Use `lake run cli -- help` for usage."

private def normalizeArgs : List String → List String
  | [] => []
  | "--" :: rest => rest
  | args => args

private def runCommand : List String → IO UInt32
  | [] => do
      IO.println helpText
      pure 0
  | cmd :: rest =>
      match cmd with
      | "help" | "--help" | "-h" => do
          IO.println helpText
          pure 0
      | "init:spec" =>
          Gen.runInitSpec rest
      | "spec" => do
          IO.println "[stub] SPEC gate commands will live here."
          pure 0
      | "plan" => do
          IO.println "[stub] PLAN gate commands will live here."
          pure 0
      | "implement" => do
          IO.println "[stub] IMPLEMENT gate commands will live here."
          pure 0
      | other => do
          IO.eprintln (unknownCmd other)
          pure 1

/-- Entry point for `lake exe cli` and `lake run cli`. -/
def main (args : List String) : IO UInt32 :=
  runCommand (normalizeArgs args)

end Cli
end LeanSpec
