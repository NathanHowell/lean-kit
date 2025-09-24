import Lake
open Lake DSL

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
