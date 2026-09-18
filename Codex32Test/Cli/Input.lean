import Codex32.Seed

/-! Bounded, noninteractive fixture input and hexadecimal conversion for the
CLI integration-test harness. -/
namespace Codex32Test.Cli.Input

/-- Read at most `limit + 1` bytes before rejecting, including short reads.
The extra byte distinguishes exact-size input from a longer stream. -/
def readBounded (stream : IO.FS.Stream) (limit : Nat) : IO ByteArray := do
  let mut data := ByteArray.empty
  for _ in [:limit + 1] do
    let chunk ← stream.read (USize.ofNat (min 1024 (limit + 1 - data.size)))
    if chunk.isEmpty then return data
    if data.size + chunk.size > limit then
      throw (IO.userError "input exceeds the permitted size")
    data := data ++ chunk
  throw (IO.userError "input exceeds the permitted size")

/-- Input must be redirected or piped, avoiding terminal echo of secret material. -/
def readStdin (limit : Nat) : IO String := do
  let stream ← IO.getStdin
  if ← stream.isTty then
    throw (IO.userError "redirect a private input file or pipe into stdin; interactive secret entry is disabled")
  let bytes ← readBounded stream limit
  match String.fromUTF8? bytes with
  | some s => return s
  | none => throw (IO.userError "input is not UTF-8")

/-- Accept one optional final LF or CRLF, without trimming arbitrary whitespace. -/
def removeFinalNewline (s : String) : String :=
  if s.endsWith "\r\n" then (s.dropEnd 2).toString
  else if s.endsWith "\n" then (s.dropEnd 1).toString
  else s

private def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

private def parsePairs : List Char → Except String (List UInt8)
  | [] => .ok []
  | a :: b :: rest => do
    let some hi := hexDigit a | throw "seed must contain only hexadecimal digits"
    let some lo := hexDigit b | throw "seed must contain only hexadecimal digits"
    return UInt8.ofNat (16 * hi + lo) :: (← parsePairs rest)
  | [_] => .error "seed hexadecimal input must have an even number of digits"

def parseSeed (s : String) : Except String Codex32.Seed := do
  let s := removeFinalNewline s
  if s.utf8ByteSize > 128 then throw "seed exceeds 64 bytes"
  let bytes ← parsePairs s.toList
  (Codex32.Seed.ofBytes bytes).mapError toString

def seedHex (seed : Codex32.Seed) : String :=
  let digits := "0123456789abcdef".toList.toArray
  String.ofList (seed.bytes.flatMap fun b =>
    [digits[b.toNat / 16]!, digits[b.toNat % 16]!])

/-- Newline-delimited shares, with LF/CRLF line endings and no blank lines. -/
def shareLines (s : String) : Except String (List String) := do
  let normalized := s.replace "\r\n" "\n"
  -- Strip only LF after normalization; stripping CRLF again would accept an
  -- extra carriage return in a malformed final CRCRLF sequence.
  let normalized := if normalized.endsWith "\n" then (normalized.dropEnd 1).toString
    else normalized
  let lines := normalized.splitOn "\n"
  if lines.length > 9 then throw "recovery accepts at most nine shares"
  if lines.any (fun line => line.isEmpty || line.utf8ByteSize > 1021) then
    throw "each share must be a nonempty codex32 string of at most 1021 bytes"
  return lines

end Codex32Test.Cli.Input
