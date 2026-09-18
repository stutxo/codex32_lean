import Codex32.Alphabet

/-!
The regular (65-bit) and long (75-bit) BIP 93 checksum recurrences.
`Nat` is deliberate: neither recurrence fits in a 64-bit machine word.
The initial residue already incorporates the expansion of the fixed HRP `ms`.
-/

namespace Codex32.Checksum

def regularConstant : Nat := 0x10ce0795c2fd1e62a

def longConstant : Nat := 0x43381e570bf4798ab26

def regularGenerators : List Nat :=
  [0x19dc500ce73fde210, 0x1bfae00def77fe529, 0x1fbd920fffe7bee52,
   0x1739640bdeee3fdad, 0x07729a039cfc75f5a]

def longGenerators : List Nat :=
  [0x3d59d273535ea62d897, 0x7a9becb6361c6c51507, 0x543f9b7e6c38d8a2a0e,
   0x0c577eaeccf1990d13c, 0x1887f74f8dc71b10651]

def step (shift mask : Nat) (generators : List Nat)
    (residue : Nat) (value : Symbol) : Nat :=
  let top := residue >>> shift
  let next := ((residue &&& mask) <<< 5) ^^^ value.val
  generators.zipIdx.foldl (fun acc (generator, i) =>
    if ((top >>> i) &&& 1) == 1 then acc ^^^ generator else acc) next

def regularPolymod (values : List Symbol) : Nat :=
  values.foldl (step 60 0x0fffffffffffffff regularGenerators) 0x23181b3

def longPolymod (values : List Symbol) : Nat :=
  values.foldl (step 70 0x3fffffffffffffffff longGenerators) 0x23181b3

/-- Choose by complete data length, including its checksum but excluding `ms1`.
The expanded HRP contributes five symbols, not three printed characters. -/
def checksumLength (completeDataLength : Nat) : Option Nat :=
  let expandedLength := 5 + completeDataLength
  if expandedLength ≤ 93 then some 13
  else if 96 ≤ expandedLength ∧ expandedLength ≤ 1023 then some 15
  else none

/-- Verify only the regular variant, within its specified period. -/
def verifyRegular (data : List Symbol) : Bool :=
  5 + data.length ≤ 93 && regularPolymod data == regularConstant

/-- Verify only the long variant, as in `ms32_verify_long_checksum`.
This low-level function intentionally does not impose the variant-selection
lower bound; use `verify` for complete Codex32 checksum validation. -/
def verifyLong (data : List Symbol) : Bool :=
  5 + data.length ≤ 1023 && longPolymod data == longConstant

/-- Select and verify the required checksum, rejecting forbidden lengths. -/
def verify (data : List Symbol) : Bool :=
  match checksumLength data.length with
  | some 13 => verifyRegular data
  | some 15 => verifyLong data
  | _ => false

def extract (count residue : Nat) : List Symbol :=
  (List.range count).map fun i =>
    Symbol.ofNat ((residue >>> (5 * (count - 1 - i))) &&& 31)

/-- Construct the regular checksum. Variant selection is the caller's concern. -/
def createRegular (data : List Symbol) : List Symbol :=
  extract 13 (regularPolymod (data ++ List.replicate 13 (Symbol.ofNat 0))
    ^^^ regularConstant)

/-- Construct the long checksum. Variant selection is the caller's concern. -/
def createLong (data : List Symbol) : List Symbol :=
  extract 15 (longPolymod (data ++ List.replicate 15 (Symbol.ofNat 0))
    ^^^ longConstant)

/-- Construct the checksum required by BIP 93, rejecting inputs whose completed
expanded codeword would exceed the maximum length. -/
def create (data : List Symbol) : Except Error (List Symbol) :=
  if 5 + data.length + 13 ≤ 93 then .ok (createRegular data)
  else if 5 + data.length + 15 ≤ 1023 then .ok (createLong data)
  else .error .codewordTooLong

end Codex32.Checksum
