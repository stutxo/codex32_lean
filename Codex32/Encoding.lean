import Codex32.Checksum

namespace Codex32

/-- A generic Codex32 message. Master-seed lengths are checked separately.
Checksums are derived, so stale checksum fields cannot be represented. -/
structure Message where
  threshold : Threshold
  identifier : Identifier
  index : Symbol
  payload : List Symbol
  zeroIndex : threshold = .unshared → index = 16
  lengthValid : payload.length ≤ 997
  deriving Repr, DecidableEq, BEq

namespace Message

def create (threshold : Threshold) (identifier : Identifier) (index : Symbol)
    (payload : List Symbol) : Except Error Message :=
  if hzero : threshold = .unshared → index = 16 then
    if hlen : payload.length ≤ 997 then
      .ok ⟨threshold, identifier, index, payload, hzero, hlen⟩
    else .error .payloadTooLong
  else .error .zeroThresholdIndex

def data (m : Message) : List Symbol :=
  [m.threshold.toSymbol] ++ m.identifier.symbols ++ [m.index] ++ m.payload

theorem data_length_le (m : Message) : m.data.length ≤ 1003 := by
  have := m.lengthValid
  simp only [data, List.length_append, List.length_cons, List.length_nil,
    m.identifier.length_eq]
  omega

end Message

namespace Encoding

/-- Maximum printed length: `ms1` plus 1018 data/checksum symbols. -/
def maxStringBytes : Nat := 1021

/-- Generic Codex32 parsing; does not impose the master seed application sizes. -/
def parse (s : String) : Except Error Message := do
  -- Check the stored UTF-8 byte size before allocating character or symbol lists.
  -- Every valid string is ASCII, so this preserves the full valid length range.
  -- A character-count guard would add a scan without rejecting any further input:
  -- every character occupies at least one byte.
  if s.utf8ByteSize > maxStringBytes then throw .codewordTooLong
  if s.toList.any (fun c => c.toNat < 33 || c.toNat > 126) then
    throw .nonAscii
  if s != s.toLower && s != s.toUpper then throw .mixedCase
  let chars := s.toLower.toList
  if chars.take 3 != ['m', 's', '1'] then throw .invalidPrefix
  let data ← Alphabet.decodeList (String.ofList (chars.drop 3))
  let checksumSize ← match Checksum.checksumLength data.length with
    | some n => pure n
    | none => throw .invalidLength
  if data.length < 6 + checksumSize then throw .incompleteHeader
  if !Checksum.verify data then throw .invalidChecksum
  let body := data.take (data.length - checksumSize)
  let t :: a :: b :: c :: d :: index :: payload := body
    | throw .incompleteHeader
  let threshold ← Threshold.fromSymbol t
  Message.create threshold ⟨[a,b,c,d], rfl⟩ index payload

/-- Lowercase is canonical. All payload symbols, including padding, are preserved. -/
def serialize (m : Message) : String :=
  let data := m.data
  let checksum := Checksum.createBounded data m.data_length_le
  "ms1" ++ Alphabet.encodeList (data ++ checksum)

def serializeUpper (m : Message) : String := (serialize m).toUpper

def validChecksum (s : String) : Bool :=
  match parse s with
  | .ok _ => true
  | .error _ => false

end Encoding
end Codex32
