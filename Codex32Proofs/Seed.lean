import Codex32.Seed

/-!
Kernel-checked alphabet and payload invariants, including round trips for every
byte list and every supported seed with arbitrary padding. No executable module
imports proofs. The serialized-string round trip is proved in `Codex32Proofs.Encoding`.
-/
namespace Codex32.Proofs

theorem alphabet_roundtrip : ∀ v : Symbol, Alphabet.decode (Alphabet.encode v) = some v := by
  decide

theorem alphabet_uppercase_roundtrip :
    ∀ v : Symbol, Alphabet.decode (Alphabet.encode v).toUpper = some v := by
  decide

theorem threshold_symbol_roundtrip (threshold : Threshold) :
    Threshold.fromSymbol threshold.toSymbol = .ok threshold := by
  cases threshold with
  | unshared => rfl
  | shared k =>
    rcases k with ⟨k, hk⟩
    have h : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
    rcases h with h | h | h | h | h | h | h | h <;> subst k <;> rfl

theorem unpack_length (width value : Nat) : (Bits.unpack width value).length = width := by
  simp [Bits.unpack]

theorem byte_bits_length (bytes : List UInt8) :
    (bytes.flatMap fun b => Bits.unpack 8 b.toNat).length = bytes.length * 8 := by
  induction bytes with
  | nil => rfl
  | cons b bs ih => simp [ih, unpack_length, Nat.add_mul, Nat.add_comm]

theorem encode_payload_length (bytes : List UInt8) (padding : Symbol) :
    (Bits.encode bytes padding).length = (bytes.length * 8 + 4) / 5 := by
  simp only [Bits.encode, List.length_map, Bits.chunks, List.length_range, byte_bits_length]
  omega

theorem encoded_seed_payload_supported (seed : Seed) (identifier : Identifier)
    (threshold : Threshold) (padding : Symbol) :
    Seed.validPayloadLength (Seed.encode seed identifier threshold padding).payload.length = true := by
  change Seed.validPayloadLength (Bits.encode seed.bytes padding).length = true
  rw [encode_payload_length]
  have h := seed.supported
  rcases h with h | h | h | h | h | h <;> rw [h] <;> decide

theorem encoded_seed_index (seed : Seed) (identifier : Identifier)
    (threshold : Threshold) (padding : Symbol) :
    (Seed.encode seed identifier threshold padding).index = 16 := rfl

set_option maxRecDepth 10000 in
theorem symbol_pack_unpack : ∀ v : Symbol, Bits.pack (Bits.unpack 5 v.val) = v.val := by
  decide

set_option maxRecDepth 10000 in
theorem byte_pack_unpack : ∀ v : Fin 256, Bits.pack (Bits.unpack 8 v.val) = v.val := by
  decide

theorem five_bits_unpack_pack : ∀ a b c d e : Bool,
    Bits.unpack 5 (Bits.pack [a,b,c,d,e]) = [a,b,c,d,e] := by
  decide



theorem chunks_succ (width count : Nat) (bits : List Bool) :
    Bits.chunks width (count + 1) bits =
    Bits.pack (bits.take width) :: Bits.chunks width count (bits.drop width) := by
  simp only [Bits.chunks, List.range_succ_eq_map, List.map_cons, Nat.zero_mul,
    List.drop_zero, List.map_map, Function.comp_def, List.drop_drop]
  congr 1
  apply List.map_congr_left
  intro i _
  simp [Nat.add_mul, Nat.add_comm]

theorem five_bits_symbol_unpack_pack : ∀ a b c d e : Bool,
    Bits.unpack 5 (Symbol.ofNat (Bits.pack [a,b,c,d,e])).val = [a,b,c,d,e] := by
  decide

theorem five_list_unpack_pack (bits : List Bool) (hlen : bits.length = 5) :
    Bits.unpack 5 (Symbol.ofNat (Bits.pack bits)).val = bits := by
  rcases bits with _ | ⟨a, bits⟩
  · simp at hlen
  rcases bits with _ | ⟨b, bits⟩
  · simp at hlen
  rcases bits with _ | ⟨c, bits⟩
  · simp at hlen
  rcases bits with _ | ⟨d, bits⟩
  · simp at hlen
  rcases bits with _ | ⟨e, bits⟩
  · simp at hlen
  cases bits with
  | nil => exact five_bits_symbol_unpack_pack a b c d e
  | cons f bits => simp at hlen

theorem unpack_chunks_five (count : Nat) (bits : List Bool) (hlen : bits.length = 5 * count) :
    ((Bits.chunks 5 count bits).map Symbol.ofNat).flatMap (fun v => Bits.unpack 5 v.val) = bits := by
  induction count generalizing bits with
  | zero =>
    have : bits = [] := by simpa using hlen
    subst bits
    rfl
  | succ count ih =>
    rw [chunks_succ]
    simp only [List.map_cons, List.flatMap_cons]
    rw [five_list_unpack_pack (bits.take 5) (by simp; omega)]
    rw [ih (bits.drop 5) (by simp; omega)]
    exact List.take_append_drop 5 bits

theorem unpack_encode (bytes : List UInt8) (padding : Symbol) :
    (Bits.encode bytes padding).flatMap (fun v => Bits.unpack 5 v.val) =
    (bytes.flatMap fun b => Bits.unpack 8 b.toNat) ++
      Bits.unpack ((5 - (bytes.length * 8) % 5) % 5) padding.val := by
  unfold Bits.encode
  rw [unpack_chunks_five]
  · rw [byte_bits_length]
  · simp only [List.length_append, unpack_length]
    omega

theorem chunks_bytes_suffix (bytes : List UInt8) (suffix : List Bool) :
    Bits.chunks 8 bytes.length ((bytes.flatMap fun b => Bits.unpack 8 b.toNat) ++ suffix) =
    bytes.map UInt8.toNat := by
  induction bytes with
  | nil => rfl
  | cons b bytes ih =>
    rw [List.length_cons, chunks_succ]
    simp only [List.flatMap_cons, List.append_assoc]
    rw [List.take_append_of_le_length (by simp [unpack_length]),
      List.drop_append_of_le_length (by simp [unpack_length])]
    have hu := unpack_length 8 b.toNat
    have ht : (Bits.unpack 8 b.toNat).take 8 = Bits.unpack 8 b.toNat := by
      simpa only [hu] using (List.take_length (l := Bits.unpack 8 b.toNat))
    have hd : (Bits.unpack 8 b.toNat).drop 8 = [] := by
      simpa only [hu] using (List.drop_length (l := Bits.unpack 8 b.toNat))
    rw [ht, hd, List.nil_append]
    rw [byte_pack_unpack ⟨b.toNat, b.toNat_lt⟩]
    rw [ih]
    rfl

theorem bits_roundtrip (bytes : List UInt8) (padding : Symbol) :
    Bits.decode (Bits.encode bytes padding) = .ok bytes := by
  unfold Bits.decode
  rw [unpack_encode]
  simp only [List.length_append, byte_bits_length, unpack_length]
  have hpad : (5 - bytes.length * 8 % 5) % 5 < 5 := Nat.mod_lt _ (by decide)
  rw [ite_eq_right (by omega)]
  have hcount : (bytes.length * 8 + (5 - bytes.length * 8 % 5) % 5) / 8 = bytes.length := by
    omega
  rw [hcount, chunks_bytes_suffix]
  simp [Function.comp_def]

theorem seed_roundtrip (seed : Seed) (identifier : Identifier)
    (threshold : Threshold) (padding : Symbol) :
    Seed.decode (Seed.encode seed identifier threshold padding) = .ok seed := by
  unfold Seed.decode
  simp only [Seed.encode]
  rw [bits_roundtrip]
  change Seed.ofBytes seed.bytes = .ok seed
  simp [Seed.ofBytes, seed.supported]

end Codex32.Proofs
