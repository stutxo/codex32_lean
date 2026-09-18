import Codex32Proofs
import Codex32Test.VectorProofs
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-! Fail CI if a project declaration depends on admissions, native proof
evaluation, or axioms beyond Lean's ordinary logical foundations. -/
open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← getEnv
  let mut checked : Nat := 0
  for (name, _) in env.constants do
    let text := name.toString
    if text.startsWith "Codex32." || text.startsWith "_private.Codex32" then
      let axioms ← Lean.collectAxioms name
      for axiomName in axioms do
        unless allowed.contains axiomName do
          throwError "{name} depends on disallowed axiom {axiomName}"
      checked := checked + 1
  logInfo m!"Axiom audit passed for {checked} project declarations."
