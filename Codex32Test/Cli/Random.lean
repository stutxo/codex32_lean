import Codex32.Alphabet

/-! OS randomness for the CLI integration-test harness. The executable
specification does not depend on this module. No deterministic PRNG or entropy
fallback is used. -/
namespace Codex32Test.Cli.Random

/-- A bounded exact read that handles short reads and rejects premature EOF.
The function argument permits testing OS-read behavior without replacing the
OS entropy source. -/
def readExact (read : USize → IO ByteArray) (count : Nat) : IO ByteArray := do
  if count > 4096 then throw (IO.userError "randomness request exceeds CLI limit")
  let mut bytes := ByteArray.empty
  for _ in [:count] do
    if bytes.size == count then return bytes
    let remaining := count - bytes.size
    let chunk ← read (USize.ofNat remaining)
    if chunk.isEmpty || chunk.size > remaining then
      throw (IO.userError "OS randomness source returned an invalid or incomplete read")
    bytes := bytes ++ chunk
  if bytes.size == count then return bytes
  throw (IO.userError "OS randomness source returned insufficient bytes")

/-- Uniform five-bit symbols, including all payload padding bits.
Reduction modulo 32 is unbiased because 32 divides 256. Linux/macOS only;
failure to open or read the OS source aborts the operation. The host must have
completed OS random-generator initialization before use. -/
def symbols (count : Nat) : IO (List Codex32.Symbol) := do
  if !System.Platform.isLinux && !System.Platform.isOSX then
    throw (IO.userError "secure randomness currently requires Linux or macOS")
  let bytes ← IO.FS.withFile "/dev/urandom" .read fun handle =>
    readExact handle.read count
  return bytes.data.toList.map fun b => Codex32.Symbol.ofNat b.toNat

end Codex32Test.Cli.Random
