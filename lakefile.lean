import Lake
open Lake DSL

package codex32 where
  version := v!"0.1.0"

@[default_target]
lean_lib Codex32

@[test_driver]
lean_exe codex32_tests where
  root := `Codex32Test.Main

lean_lib Codex32Test

lean_lib Codex32Proofs

lean_exe codex32_test_cli where
  root := `Codex32Test.Cli.Main
