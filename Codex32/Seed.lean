import Codex32.Encoding

namespace Codex32

namespace Bits

/-- Most significant bit first; using bounded groups keeps conversion auditable. -/
def unpack (width value : Nat) : List Bool :=
  (List.range width).map fun i => (value >>> (width - 1 - i)) &&& 1 == 1

def pack (bits : List Bool) : Nat :=
  bits.foldl (fun n b => 2 * n + if b then 1 else 0) 0

def chunks (width count : Nat) (bits : List Bool) : List Nat :=
  (List.range count).map fun i => pack ((bits.drop (i * width)).take width)

/-- Padding uses the low padding-width bits of `padding`, including nonzero bits. -/
def encode (bytes : List UInt8) (padding : Symbol := 0) : List Symbol :=
  let bits := bytes.flatMap fun b => unpack 8 b.toNat
  let pad := (5 - bits.length % 5) % 5
  (chunks 5 ((bits.length + pad) / 5) (bits ++ unpack pad padding.val)).map Symbol.ofNat

/-- Discard at most four trailing bits, whether zero or nonzero. -/
def decode (payload : List Symbol) : Except Error (List UInt8) :=
  let bits := payload.flatMap fun v => unpack 5 v.val
  if bits.length % 8 > 4 then .error .incompletePayload
  else .ok ((chunks 8 (bits.length / 8) bits).map UInt8.ofNat)

end Bits

def SupportedSeedLength (n : Nat) : Prop :=
  n = 16 ∨ n = 20 ∨ n = 24 ∨ n = 28 ∨ n = 32 ∨ n = 64

instance (n : Nat) : Decidable (SupportedSeedLength n) :=
  inferInstanceAs (Decidable (n = 16 ∨ n = 20 ∨ n = 24 ∨ n = 28 ∨ n = 32 ∨ n = 64))

structure Seed where
  bytes : List UInt8
  supported : SupportedSeedLength bytes.length
  deriving Repr, DecidableEq, BEq

namespace Seed

def ofBytes (bytes : List UInt8) : Except Error Seed :=
  if h : SupportedSeedLength bytes.length then .ok ⟨bytes, h⟩
  else .error .unsupportedSeedLength

/-- Supported master-seed payload lengths, measured in five-bit symbols. -/
def supportedPayloadLengths : List Nat :=
  [26, 32, 39, 45, 52, 103]

def validPayloadLength (n : Nat) : Bool :=
  supportedPayloadLengths.contains n

/-- Application parser corresponding to the BIP's `ms32_decode`, including shares. -/
def parse (s : String) : Except Error Message := do
  let m ← Encoding.parse s
  if !validPayloadLength m.payload.length then throw .unsupportedPayloadLength
  return m

def decode (m : Message) : Except Error Seed := do
  if m.index != 16 then throw .expectedSecret
  ofBytes (← Bits.decode m.payload)

def decodeString (s : String) : Except Error Seed := do
  decode (← parse s)

/-- Encode a supported seed; threshold is retained even for the secret index. -/
def encode (seed : Seed) (identifier : Identifier) (threshold : Threshold := .unshared)
    (padding : Symbol := 0) : Message :=
  let payload := Bits.encode seed.bytes padding
  have hlen : payload.length ≤ 997 := by
    have sum_eight : ∀ bs : List UInt8, (bs.map (fun _ => 8 : UInt8 → Nat)).sum = bs.length * 8 := by
      intro bs
      induction bs with
      | nil => rfl
      | cons b bs ih => simp [ih, Nat.add_mul, Nat.add_comm]
    simp only [payload, Bits.encode, List.length_map, Bits.chunks, List.length_range,
      Bits.unpack, List.length_flatMap, sum_eight]
    have h := seed.supported
    unfold SupportedSeedLength at h
    omega
  ⟨threshold, identifier, 16, payload, fun _ => rfl, hlen⟩

def encodeString (seed : Seed) (identifier : Identifier)
    (threshold : Threshold := .unshared) (padding : Symbol := 0) : String :=
  Encoding.serialize (encode seed identifier threshold padding)

end Seed
end Codex32
