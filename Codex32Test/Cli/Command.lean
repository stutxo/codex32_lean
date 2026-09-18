import Codex32
import Codex32Test.Cli.Input
import Codex32Test.Cli.Random

/-! Command-line integration-test harness for exercising the executable
specification with public fixtures. This is not a reference CLI. -/
namespace Codex32Test.Cli
open Codex32

private def help : String := "codex32_test_cli — BIP 93 integration-test harness

For disposable test fixtures. This harness is not a reference CLI.

Usage:
  codex32_test_cli encode IDENTIFIER [THRESHOLD [PADDING]] < fixture.hex
  codex32_test_cli decode < fixture.codex32
  codex32_test_cli split IDENTIFIER THRESHOLD COUNT < fixture.hex
  codex32_test_cli recover < fixture-shares.codex32
  codex32_test_cli --help

encode: one hexadecimal seed on stdin; output one codex32 secret.
        THRESHOLD defaults to 0; PADDING defaults to 0 (range 0..31).
decode: one codex32 secret on stdin; output lowercase hexadecimal seed.
split:  one hexadecimal seed on stdin; output COUNT distinct shares, one per line.
recover: exactly THRESHOLD distinct shares on stdin, one per line;
         output the recovered seed as lowercase hexadecimal.

IDENTIFIER is four Bech32 characters. Threshold is 0 or 2..9 for encode,
and 2..9 for split. Split count must be between threshold and 31.
Seed sizes are 16, 20, 24, 28, 32, or 64 bytes. LF and CRLF are accepted.
Input is bounded; blank lines and extra input are rejected. Fixture contents
are accepted through redirected/piped stdin, never as command arguments.

Examples using the public BIP 93 vector 3 seed:
  printf '%s\\n' ffeeddccbbaa99887766554433221100 | codex32_test_cli encode cash 3
  printf '%s\\n' ffeeddccbbaa99887766554433221100 | codex32_test_cli split cash 3 5

Run all stream, entropy-adapter, and CLI integration tests:
  bash scripts/test-cli.sh

Randomized split tests obtain uniform symbols from /dev/urandom on Linux/macOS.
OS randomness must be initialized; read failures abort without a fallback.
Output indices follow Bech32 order q,p,z,..., skipping the secret index s.
"

private inductive Command where
  | encode (identifier : Identifier) (threshold : Threshold) (padding : Symbol)
  | decode
  | split (identifier : Identifier) (threshold : Threshold) (count : Nat)
  | recover

private def decimal (s : String) : Except String Nat := do
  if s.isEmpty || s.utf8ByteSize > 2 || !s.toList.all Char.isDigit then
    throw "numeric arguments must contain one or two decimal digits"
  let some n := s.toNat? | throw "invalid decimal argument"
  return n

private def identifierArg (s : String) : Except String Identifier := do
  if s.utf8ByteSize != 4 then throw "identifier must contain four Bech32 characters"
  Identifier.parse s |>.mapError toString

private def encodeCommand (identifier : String) (threshold := "0") (padding := "0") :
    Except String Command := do
  let identifier ← identifierArg identifier
  let threshold ← Threshold.ofNat (← decimal threshold) |>.mapError toString
  let p ← decimal padding
  if h : p < 32 then return .encode identifier threshold ⟨p, h⟩
  else throw "padding must be between 0 and 31"

private def parseCommand : List String → Except String Command
  | ["encode", identifier] => encodeCommand identifier
  | ["encode", identifier, threshold] => encodeCommand identifier threshold
  | ["encode", identifier, threshold, padding] => encodeCommand identifier threshold padding
  | ["decode"] => .ok .decode
  | ["split", identifier, threshold, count] => do
    let identifier ← identifierArg identifier
    let threshold ← Threshold.ofNat (← decimal threshold) |>.mapError toString
    if threshold.count == 0 then throw "split threshold must be between 2 and 9"
    let count ← decimal count
    if count < threshold.count || count > 31 then
      throw "share count must be between the threshold and 31"
    return .split identifier threshold count
  | ["recover"] => .ok .recover
  | _ => .error "invalid command or arguments; use --help"

private def checked (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error e => throw (IO.userError e)

private def libraryResult (result : Except Codex32.Error α) : IO α :=
  checked (result.mapError toString)

private def readSeed : IO Seed := do
  checked (Input.parseSeed (← Input.readStdin 130))

/-- Build all output before writing any of it: validation or entropy failures
cannot leave a partial set of shares on stdout. Output-device write failures
can still truncate output, as with any streamed output. -/
private def execute (entropy : Nat → IO (List Symbol)) : Command → IO String
  | .encode identifier threshold padding => do
    let seed ← readSeed
    return Seed.encodeString seed identifier threshold padding ++ "\n"
  | .decode => do
    let text ← Input.readStdin 1023
    let seed ← libraryResult (Seed.decodeString (Input.removeFinalNewline text))
    return Input.seedHex seed ++ "\n"
  | .split identifier threshold count => do
    let seed ← readSeed
    let secret := Seed.encode seed identifier threshold
    let length := secret.payload.length
    let entropy ← entropy ((threshold.count - 1) * length)
    let payloads := (List.range (threshold.count - 1)).map fun i =>
      (entropy.drop (i * length)).take length
    let initial ← libraryResult (Shares.initializeExisting secret payloads)
    let checked ← libraryResult (Shares.validate initial)
    let indices := ((List.range 32).filter (· != 16)).take count
    let shares := indices.map fun index => checked.interpolate (Symbol.ofNat index)
    return String.intercalate "\n" (shares.map Encoding.serialize) ++ "\n"
  | .recover => do
    let lines ← checked (Input.shareLines (← Input.readStdin (9 * 1023)))
    let shares ← lines.mapM fun line => libraryResult (Seed.parse line)
    let secret ← libraryResult (Shares.recover shares)
    let seed ← libraryResult (Seed.decode secret)
    return Input.seedHex seed ++ "\n"

/-- Run the harness with an explicit entropy adapter for deterministic failure tests.
CLI execution always supplies `Random.symbols`. Standard streams can be
redirected with `IO.withStdin`, `IO.withStdout`, and `IO.withStderr`. -/
def runWithEntropy (entropy : Nat → IO (List Symbol)) (args : List String) : IO UInt32 := do
  if args == ["--help"] || args == ["-h"] then
    IO.print help
    return 0
  try
    let command ← checked (parseCommand args)
    let output ← execute entropy command
    let stdout ← IO.getStdout
    stdout.putStr output
    stdout.flush
    return 0
  catch e =>
    -- Validation messages never contain seed/share contents. Keep OS diagnostics
    -- generic rather than rendering implementation-specific exception details.
    match e with
    | .userError message => IO.eprintln s!"codex32: {message}"
    | _ => IO.eprintln "codex32: IO failed; check redirected files and the OS randomness source"
    return 1

def main (args : List String) : IO UInt32 := runWithEntropy Random.symbols args

end Codex32Test.Cli
