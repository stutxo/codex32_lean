import Codex32Test.Cli.Command

/-! Boundary and failure tests for the CLI, run by `lake test`. Executable and
OS-entropy integration tests are in `scripts/test-cli.sh`. All fixtures are public. -/
namespace Codex32Test.Cli.Tests

private abbrev TestM := StateT Nat IO

private def check (condition : Bool) (name : String) : TestM Unit := do
  unless condition do throw (IO.userError s!"CLI stream check failed: {name}")
  modify (· + 1)

private def expectError (action : IO α) (expected : IO.Error) (name : String) : TestM Unit := do
  let actual ← try
    let _ ← action
    pure none
  catch error => pure (some error.toString)
  check (actual == some expected.toString) name

private def streamTests : TestM Unit := do
  -- Exact-size input is accepted, one additional byte is rejected, and the
  -- adapter never reads the rest of a large attacker-controlled stream.
  let buffer ← IO.mkRef ({ data := "abc".toUTF8 } : IO.FS.Stream.Buffer)
  let bytes ← Input.readBounded (IO.FS.Stream.ofBuffer buffer) 3
  check (bytes == "abc".toUTF8) "exact input limit"
  let buffer ← IO.mkRef ({ data := ByteArray.mk (Array.replicate 100000 65) } : IO.FS.Stream.Buffer)
  expectError (Input.readBounded (IO.FS.Stream.ofBuffer buffer) 3)
    (.userError "input exceeds the permitted size") "oversized input"
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
  expectError (Random.readExact (fun _ => pure ByteArray.empty) 1)
    (.userError "OS randomness source returned an invalid or incomplete read") "entropy EOF"
  expectError (Random.readExact (fun _ => throw (.otherError 5 "simulated failure")) 1)
    (.otherError 5 "simulated failure") "entropy read failure"
  expectError (Random.readExact (fun _ => pure (ByteArray.mk #[1, 2])) 1)
    (.userError "OS randomness source returned an invalid or incomplete read")
    "invalid entropy read size"
  expectError (Random.readExact (fun _ => throw (.userError "unexpected read")) 4097)
    (.userError "randomness request exceeds CLI limit")
    "entropy request bound"
  let bytes ← Random.readExact (fun _ => throw (IO.userError "unexpected read")) 0
  check bytes.isEmpty "zero entropy request"
  for symbol in [:32] do
    let occurrences := (List.range 256).filter fun byte =>
      (Codex32.Symbol.ofNat byte).val == symbol
    check (occurrences.length == 8) "byte-to-symbol mapping is balanced"

private def seed : String := "ffeeddccbbaa99887766554433221100"
private def encoded : String := "ms13cashsllhdmn9m42vcsamx24zrxgs3qqjzqud4m0d6nln"
private def genericError : String :=
  "codex32: IO failed; check redirected files and the OS randomness source\n"

private structure Result where
  exitCode : UInt32
  stdout : String
  stderr : String

private def capture (args : List String) (input : String)
    (entropy : Nat → IO (List Codex32.Symbol))
    (outputStream : IO.FS.Stream → IO.FS.Stream := id) : IO Result := do
  let stdin ← IO.mkRef ({ data := input.toUTF8 } : IO.FS.Stream.Buffer)
  let stdout ← IO.mkRef ({} : IO.FS.Stream.Buffer)
  let stderr ← IO.mkRef ({} : IO.FS.Stream.Buffer)
  let exitCode ← IO.withStdin (IO.FS.Stream.ofBuffer stdin) <|
    IO.withStdout (outputStream (IO.FS.Stream.ofBuffer stdout)) <|
    IO.withStderr (IO.FS.Stream.ofBuffer stderr) <| runWithEntropy entropy args
  let output := String.fromUTF8! (← stdout.get).data
  let errors := String.fromUTF8! (← stderr.get).data
  return { exitCode, stdout := output, stderr := errors }

private def commandTests : TestM Unit := do
  let noEntropy := fun _ => throw (IO.userError "unexpected entropy request")
  let result ← capture ["encode", "cash", "3"] (seed ++ "\n") noEntropy
  check (result.exitCode == 0 && result.stdout == encoded ++ "\n" && result.stderr.isEmpty)
    "official encoding through command runner"
  let result ← capture ["decode"] (encoded ++ "\r\n") noEntropy
  check (result.exitCode == 0 && result.stdout == seed ++ "\n" && result.stderr.isEmpty)
    "official decoding through command runner"

  let entropyCalls ← IO.mkRef (0 : Nat)
  let entropy := fun count => do
    entropyCalls.modify (· + 1)
    return List.replicate count (0 : Codex32.Symbol)
  let result ← capture ["split", "cash", "3", "5"] "zz\n" entropy
  check (result.exitCode == 1 && result.stdout.isEmpty &&
    result.stderr == "codex32: seed must contain only hexadecimal digits\n")
    "validation rejects without output and with exact diagnostic"
  check ((← entropyCalls.get) == 0) "validation precedes entropy acquisition"
  let result ← capture ["split", "cash", "3", "2"] (seed ++ "\n") entropy
  check (result.exitCode == 1 && result.stdout.isEmpty &&
    result.stderr == "codex32: share count must be between the threshold and 31\n")
    "argument validation rejects without output"

  -- Fail after a short entropy read, when some material has already been gathered.
  let reads ← IO.mkRef (0 : Nat)
  let entropy := fun count => do
    let bytes ← Random.readExact (fun _ => do
      let call ← reads.modifyGet fun n => (n, n + 1)
      return if call == 0 then ByteArray.mk #[255] else ByteArray.empty) count
    return bytes.data.toList.map fun byte => Codex32.Symbol.ofNat byte.toNat
  let result ← capture ["split", "cash", "3", "5"] (seed ++ "\n") entropy
  check (result.exitCode == 1 && result.stdout.isEmpty && result.stderr ==
    "codex32: OS randomness source returned an invalid or incomplete read\n")
    "incomplete entropy rejects without output and with exact diagnostic"
  check ((← reads.get) == 2) "entropy failure exercised a partial read"
  let result ← capture ["split", "cash", "3", "5"] (seed ++ "\n")
    (fun count => do
      let _ ← Random.readExact (fun _ => throw (.otherError 5 s!"private detail {seed}")) count
      return [])
  check (result.exitCode == 1 && result.stdout.isEmpty && result.stderr == genericError)
    "entropy IO error omits OS exception details"

  -- A successful deterministic split still exercises the complete command path.
  let result ← capture ["split", "cash", "3", "5"] (seed ++ "\n")
    (fun count => pure (List.replicate count 0))
  let shares := (Input.removeFinalNewline result.stdout).splitOn "\n"
  check (result.exitCode == 0 && shares.length == 5 && result.stderr.isEmpty)
    "complete split output"
  let recovered ← capture ["recover"] (String.intercalate "\n" (shares.take 3) ++ "\n") noEntropy
  check (recovered.exitCode == 0 && recovered.stdout == seed ++ "\n" && recovered.stderr.isEmpty)
    "split output recovers through command runner"

  -- A device may consume a prefix before raising an error. The CLI must report
  -- failure, preserve that fact, and never retry or flush a failed write.
  let writes ← IO.mkRef (0 : Nat)
  let flushes ← IO.mkRef (0 : Nat)
  let result ← capture ["encode", "cash", "3"] (seed ++ "\n") noEntropy fun stream =>
    { stream with
      putStr := fun output => do
        writes.modify (· + 1)
        stream.putStr (output.take 17).toString
        throw (.otherError 5 s!"private device detail {seed}")
      flush := flushes.modify (· + 1) }
  check (result.exitCode == 1 && result.stderr == genericError)
    "partial output write returns failure and generic diagnostic"
  check (result.stdout == (encoded.take 17).toString) "failed output remains a truncated prefix"
  check ((← writes.get) == 1 && (← flushes.get) == 0) "failed write is not retried or flushed"

  let result ← capture ["encode", "cash", "3"] (seed ++ "\n") noEntropy fun stream =>
    { stream with
      flush := do
        flushes.modify (· + 1)
        throw (.otherError 5 s!"private flush detail {seed}") }
  check (result.exitCode == 1 && result.stderr == genericError &&
    result.stdout == encoded ++ "\n") "flush failure after complete write is reported"
  check ((← flushes.get) == 1) "failed flush is not retried"

def run : IO Nat := do
  let (_, count) ← (streamTests *> commandTests).run 0
  return count

end Codex32Test.Cli.Tests
