import Codex32Proofs.Seed
import Codex32Proofs.Checksum

/-!
Generic serialized-message and seed round trips. Character validity, header
reconstruction, checksum creation and verification are proved for all messages;
there are no unchecked parser or checksum assumptions in the final theorems.
-/

namespace Codex32.Proofs

theorem alphabet_encode_lower : ∀ v : Symbol, (Alphabet.encode v).toLower = Alphabet.encode v := by
  decide

theorem alphabet_encode_printable : ∀ v : Symbol,
    ((Alphabet.encode v).toNat < 33 || (Alphabet.encode v).toNat > 126) = false := by
  decide

theorem alphabet_encode_one_byte : ∀ v : Symbol, (Alphabet.encode v).utf8Size = 1 := by
  decide

theorem encodeList_byteSize (values : List Symbol) :
    (Alphabet.encodeList values).utf8ByteSize = values.length := by
  induction values with
  | nil => rfl
  | cons v values ih =>
    simp only [Alphabet.encodeList, List.map_cons, String.ofList_cons,
      String.utf8ByteSize_append, String.utf8ByteSize_singleton, alphabet_encode_one_byte]
    change 1 + (Alphabet.encodeList values).utf8ByteSize = (v :: values).length
    simp [ih, Nat.add_comm]

theorem alphabet_list_roundtrip (values : List Symbol) :
    Alphabet.decodeList (Alphabet.encodeList values) = .ok values := by
  unfold Alphabet.decodeList Alphabet.encodeList
  simp only [String.toList_ofList]
  induction values with
  | nil => rfl
  | cons v values ih =>
    simp only [List.map_cons, List.mapM_cons, alphabet_roundtrip]
    rw [ih]
    rfl

theorem encodeList_lower (values : List Symbol) :
    (Alphabet.encodeList values).toLower = Alphabet.encodeList values := by
  apply String.toList_inj.mp
  simp [Alphabet.encodeList, String.toLower, String.toList_map, Function.comp_def,
    alphabet_encode_lower]

theorem encoded_ascii (values : List Symbol) :
    ("ms1" ++ Alphabet.encodeList values).toList.any
      (fun c => c.toNat < 33 || c.toNat > 126) = false := by
  simp [String.toList_append, Alphabet.encodeList, List.any_map, alphabet_encode_printable]

theorem encoded_lower (values : List Symbol) :
    ("ms1" ++ Alphabet.encodeList values).toLower = "ms1" ++ Alphabet.encodeList values := by
  apply String.toList_inj.mp
  simp [String.toLower, String.toList_map, String.toList_append, Alphabet.encodeList,
    Function.comp_def, alphabet_encode_lower]

theorem four_list (values : List α) (hlen : values.length = 4) :
    ∃ a b c d, values = [a,b,c,d] := by
  rcases values with _ | ⟨a, values⟩
  · simp at hlen
  rcases values with _ | ⟨b, values⟩
  · simp at hlen
  rcases values with _ | ⟨c, values⟩
  · simp at hlen
  rcases values with _ | ⟨d, values⟩
  · simp at hlen
  cases values with
  | nil => exact ⟨a,b,c,d,rfl⟩
  | cons e values => simp at hlen

theorem message_create_roundtrip (m : Message) :
    Message.create m.threshold m.identifier m.index m.payload = .ok m := by
  unfold Message.create
  rw [dite_eq_left m.zeroIndex, dite_eq_left m.lengthValid]

theorem encoded_prefix (values : List Symbol) :
    ("ms1" ++ Alphabet.encodeList values).toList.take 3 = ['m', 's', '1'] := by
  simp [String.toList_append]

theorem encoded_drop (values : List Symbol) :
    String.ofList (("ms1" ++ Alphabet.encodeList values).toList.drop 3) =
    Alphabet.encodeList values := by
  simp [String.toList_append]

theorem parse_encoded_data (m : Message) (checksum : List Symbol)
    (hselect : Checksum.checksumLength (m.data ++ checksum).length = some checksum.length)
    (hvalid : Checksum.verify (m.data ++ checksum) = true) :
    Encoding.parse ("ms1" ++ Alphabet.encodeList (m.data ++ checksum)) = .ok m := by
  unfold Encoding.parse
  have hsize : ¬ ("ms1" ++ Alphabet.encodeList (m.data ++ checksum)).utf8ByteSize >
      Encoding.maxStringBytes := by
    have hlen : (m.data ++ checksum).length ≤ 1018 := by
      have h := hselect
      simp only [Checksum.checksumLength] at h
      split at h
      · omega
      · split at h
        · omega
        · cases h
    simp only [String.utf8ByteSize_append, encodeList_byteSize, Encoding.maxStringBytes]
    change ¬ 3 + (m.data ++ checksum).length > 1021
    omega
  rw [ite_eq_right hsize]
  rw [encoded_ascii, encoded_lower]
  simp only [Bool.false_eq_true, ↓reduceIte, bne_self_eq_false, Bool.false_and]
  rw [encoded_prefix, encoded_drop, alphabet_list_roundtrip]
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [hselect]
  dsimp only
  have hheader : ¬ (m.data ++ checksum).length < 6 + checksum.length := by
    simp only [Message.data, List.length_append, List.length_cons, List.length_nil,
      m.identifier.length_eq]
    omega
  rw [ite_eq_right hheader, hvalid]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  have hbody : (m.data ++ checksum).take ((m.data ++ checksum).length - checksum.length) = m.data := by
    simp
  rw [hbody]
  rcases m with ⟨threshold, ⟨symbols, hsymbols⟩, index, payload, hzero, hlen⟩
  obtain ⟨a,b,c,d,rfl⟩ := four_list symbols hsymbols
  simp only [Message.data, List.cons_append, List.nil_append]
  rw [threshold_symbol_roundtrip]
  exact message_create_roundtrip
    ⟨threshold, ⟨[a,b,c,d], hsymbols⟩, index, payload, hzero, hlen⟩

theorem serialize_uses_create (m : Message) (checksum : List Symbol)
    (h : Checksum.create m.data = .ok checksum) :
    Encoding.serialize m = "ms1" ++ Alphabet.encodeList (m.data ++ checksum) := by
  unfold Checksum.create at h
  unfold Encoding.serialize
  split at h <;> rename_i hregular
  · cases h
    simp only [hregular, ↓reduceIte]
  · split at h
    · cases h
      simp only [hregular, ↓reduceIte]
    · cases h

theorem parse_serialize (m : Message) : Encoding.parse (Encoding.serialize m) = .ok m := by
  have hlen : m.data.length ≤ 1003 := by
    have := m.lengthValid
    simp only [Message.data, List.length_append, List.length_cons, List.length_nil,
      m.identifier.length_eq]
    omega
  obtain ⟨checksum, hcreate⟩ := (Checksum.create_exists_iff m.data).2 hlen
  rw [serialize_uses_create m checksum hcreate]
  exact parse_encoded_data m checksum
    (Checksum.create_selects_valid_length m.data checksum hcreate)
    (Checksum.verify_create m.data checksum hcreate)

theorem serialized_checksum_valid (m : Message) :
    Encoding.validChecksum (Encoding.serialize m) = true := by
  unfold Encoding.validChecksum
  rw [parse_serialize]

theorem seed_string_roundtrip (seed : Seed) (identifier : Identifier)
    (threshold : Threshold) (padding : Symbol) :
    Seed.decodeString (Seed.encodeString seed identifier threshold padding) = .ok seed := by
  unfold Seed.decodeString Seed.parse Seed.encodeString
  rw [parse_serialize]
  dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [encoded_seed_payload_supported]
  exact seed_roundtrip seed identifier threshold padding

theorem encoded_seed_checksum_valid (seed : Seed) (identifier : Identifier)
    (threshold : Threshold) (padding : Symbol) :
    Encoding.validChecksum (Seed.encodeString seed identifier threshold padding) = true :=
  serialized_checksum_valid _

end Codex32.Proofs
