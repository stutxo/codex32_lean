import Codex32Cli.Input
import Codex32Cli.Random

/-! Boundary tests for byte-stream adapters; executable integration tests are in
`scripts/test-cli.sh`. These inputs are disposable, public test data. -/
namespace Codex32Cli.Tests

private def check (condition : Bool) (name : String) : IO Unit :=
  unless condition do throw (IO.userError s!"CLI stream check failed: {name}")

private def expectFailure (action : IO α) (name : String) : IO Unit := do
  let failed ← try
    let _ ← action
    pure false
  catch _ => pure true
  check failed name

def main : IO Unit := do
  -- Exact-size input is accepted, one additional byte is rejected, and the
  -- adapter never reads the rest of a large attacker-controlled stream.
  let buffer ← IO.mkRef ({ data := "abc".toUTF8 } : IO.FS.Stream.Buffer)
  let bytes ← Input.readBounded (IO.FS.Stream.ofBuffer buffer) 3
  check (bytes == "abc".toUTF8) "exact input limit"
  let buffer ← IO.mkRef ({ data := ByteArray.mk (Array.replicate 100000 65) } : IO.FS.Stream.Buffer)
  expectFailure (Input.readBounded (IO.FS.Stream.ofBuffer buffer) 3) "oversized input"
  check ((← buffer.get).pos == 4) "oversized input consumed only limit plus one"
  let buffer ← IO.mkRef ({ data := "abc".toUTF8 } : IO.FS.Stream.Buffer)
  let stream := IO.FS.Stream.ofBuffer buffer
  let bytes ← Input.readBounded { stream with read := fun _ => stream.read 1 } 3
  check (bytes == "abc".toUTF8) "short input reads"
  let buffer ← IO.mkRef ({} : IO.FS.Stream.Buffer)
  check ((← Input.readBounded (IO.FS.Stream.ofBuffer buffer) 0).isEmpty) "empty input"

  let calls ← IO.mkRef (0 : Nat)
  let bytes ← Random.readExact (fun _ => do
    calls.modify (· + 1)
    return ByteArray.mk #[255]) 103
  check (bytes.size == 103 && (← calls.get) == 103) "short entropy reads"
  expectFailure (Random.readExact (fun _ => pure ByteArray.empty) 1) "entropy EOF"
  expectFailure (Random.readExact (fun _ => throw (IO.userError "simulated failure")) 1)
    "entropy read failure"
  expectFailure (Random.readExact (fun _ => pure (ByteArray.mk #[1, 2])) 1)
    "invalid entropy read size"
  expectFailure (Random.readExact (fun _ => pure ByteArray.empty) 4097)
    "entropy request bound"
  let bytes ← Random.readExact (fun _ => throw (IO.userError "unexpected read")) 0
  check bytes.isEmpty "zero entropy request"
  for symbol in [:32] do
    let occurrences := (List.range 256).filter fun byte =>
      (Codex32.Symbol.ofNat byte).val == symbol
    check (occurrences.length == 8) "byte-to-symbol mapping is balanced"
  IO.println "CLI stream and entropy checks passed"

end Codex32Cli.Tests

def main : IO Unit := Codex32Cli.Tests.main
