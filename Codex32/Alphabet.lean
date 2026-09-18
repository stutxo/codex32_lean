import Codex32.Error

/-! BIP 93's Bech32 alphabet and bounded header types. -/
namespace Codex32

abbrev Symbol := Fin 32

namespace Symbol
def ofNat (n : Nat) : Symbol := ⟨n % 32, Nat.mod_lt _ (by decide)⟩
end Symbol

namespace Alphabet

def chars : List Char := "qpzry9x8gf2tvdw0s3jn54khce6mua7l".toList

def encode (v : Symbol) : Char := chars[v.val]'(by exact v.isLt)

/-- Values are case insensitive; the enclosing string parser enforces uniform case. -/
def decode (c : Char) : Option Symbol :=
  let n := chars.idxOf c.toLower
  if h : n < 32 then some ⟨n, h⟩ else none

def encodeList (vs : List Symbol) : String := String.ofList (vs.map encode)

def decodeList (s : String) : Except Error (List Symbol) :=
  s.toList.mapM fun c => match decode c with
    | some v => .ok v
    | none => .error .invalidCharacter

end Alphabet

/-- Numeric thresholds are distinct from Bech32 field values. -/
inductive Threshold where
  | unshared
  | shared (k : Fin 8)
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

namespace Threshold

def count : Threshold → Nat
  | .unshared => 0
  | .shared k => k.val + 2

def ofNat (n : Nat) : Except Error Threshold :=
  if n = 0 then .ok .unshared
  else if h : 2 ≤ n ∧ n ≤ 9 then .ok (.shared ⟨n - 2, by omega⟩)
  else .error .invalidThreshold

def toSymbol (t : Threshold) : Symbol :=
  (Alphabet.decode (Char.ofNat (48 + t.count))).getD 0

def fromSymbol (s : Symbol) : Except Error Threshold :=
  ofNat ((Alphabet.encode s).toNat - 48)

end Threshold

structure Identifier where
  symbols : List Symbol
  length_eq : symbols.length = 4
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

namespace Identifier
def parse (s : String) : Except Error Identifier := do
  if s.utf8ByteSize != 4 then throw .invalidIdentifierLength
  let symbols ← Alphabet.decodeList s
  if h : symbols.length = 4 then return ⟨symbols, h⟩
  else throw .invalidIdentifierLength

def toString (id : Identifier) : String := Alphabet.encodeList id.symbols
end Identifier

end Codex32
