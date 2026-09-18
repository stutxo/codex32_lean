import Codex32Proofs.Encoding

/-!
Declarative BIP 93 parsing specification. The specification uses the printed
alphabet, header, permitted checksum widths and periods, and polymod equations.
It does not refer to either parser, checksum creation, or serialization.
-/

namespace Codex32.Spec

/-- Printable ASCII is required before case normalization. -/
def Printable (s : String) : Prop :=
  ∀ c ∈ s.toList, 33 ≤ c.toNat ∧ c.toNat ≤ 126

/-- The entire printed string has one case. -/
def UniformCase (s : String) : Prop := s = s.toLower ∨ s = s.toUpper

/-- The two checksum alternatives, including the five expanded HRP symbols.
The supplied suffix is unconstrained by any checksum constructor. -/
def Checksum (body suffix : List Symbol) : Prop :=
  (suffix.length = 13 ∧ 5 + (body ++ suffix).length ≤ 93 ∧
    Codex32.Checksum.regularPolymod (body ++ suffix) = Codex32.Checksum.regularConstant) ∨
  (suffix.length = 15 ∧ 96 ≤ 5 + (body ++ suffix).length ∧
    5 + (body ++ suffix).length ≤ 1023 ∧
    Codex32.Checksum.longPolymod (body ++ suffix) = Codex32.Checksum.longConstant)

/-- A generic BIP 93 string with the indicated message. The normalized text
contains the literal HRP/separator, threshold digit, four identifier symbols,
index, payload and checksum. `Message`'s bounded header types express threshold
0 or 2–9 and the requirement that threshold zero has index `s`. -/
def Encoding (s : String) (m : Message) : Prop :=
  Printable s ∧ UniformCase s ∧
    ∃ suffix : List Symbol,
      s.toLower = "ms1" ++ Alphabet.encodeList (m.data ++ suffix) ∧
      Checksum m.data suffix

/-- Master-seed application sizes, retaining both secrets and shares. -/
def Seed (s : String) (m : Message) : Prop :=
  Encoding s m ∧
    (m.payload.length = 26 ∨ m.payload.length = 32 ∨ m.payload.length = 39 ∨
      m.payload.length = 45 ∨ m.payload.length = 52 ∨ m.payload.length = 103)

end Codex32.Spec

namespace Codex32.Proofs

private theorem printable_iff (s : String) :
    Spec.Printable s ↔
      s.toList.any (fun c => c.toNat < 33 || c.toNat > 126) = false := by
  simp [Spec.Printable, List.any_eq_false]

private theorem uniformCase_iff (s : String) :
    Spec.UniformCase s ↔ (s != s.toLower && s != s.toUpper) = false := by
  simp [Spec.UniformCase]
  constructor
  · intro h hn
    exact h.resolve_left hn
  · intro h
    by_cases hl : s = s.toLower
    · exact Or.inl hl
    · exact Or.inr (h hl)

private theorem ascii_sizes (c : Char) (hc : c.toNat < 128) :
    c.utf8Size = 1 ∧ c.toLower.utf8Size = 1 := by
  have h : ∀ n : Fin 128,
      (Char.ofNat n.val).utf8Size = 1 ∧ (Char.ofNat n.val).toLower.utf8Size = 1 := by
    decide +kernel
  simpa using h ⟨c.toNat, hc⟩

private theorem printable_lower_byteSize (s : String) (h : Spec.Printable s) :
    s.toLower.utf8ByteSize = s.utf8ByteSize := by
  have aux : ∀ cs : List Char, (∀ c ∈ cs, c.toNat < 128) →
      (String.ofList (cs.map Char.toLower)).utf8ByteSize = (String.ofList cs).utf8ByteSize := by
    intro cs
    induction cs with
    | nil => intro _; rfl
    | cons c cs ih =>
      intro hc
      have hs := ascii_sizes c (hc c (by simp))
      simp only [List.map_cons, String.ofList_cons, String.utf8ByteSize_append,
        String.utf8ByteSize_singleton, hs.1, hs.2]
      rw [ih (fun d hd => hc d (by simp [hd]))]
  have hx := aux s.toList (fun c hc => by have := h c hc; omega)
  have he : String.ofList (s.toList.map Char.toLower) = s.toLower := by
    apply String.toList_inj.mp
    simp [String.toLower, String.toList_map]
  simpa [he] using hx

theorem alphabet_decode_sound (c : Char) (v : Symbol)
    (h : Alphabet.decode c = some v) : Alphabet.encode v = c.toLower := by
  unfold Alphabet.decode Alphabet.index? at h
  dsimp only at h
  split at h
  · cases h
    exact List.getElem_idxOf _
  · cases h

private theorem alphabet_decodeList_sound (s : String) (vs : List Symbol)
    (h : Alphabet.decodeList s = .ok vs) : Alphabet.encodeList vs = s.toLower := by
  have aux : ∀ cs : List Char, ∀ vs : List Symbol,
      (cs.mapM fun c => match Alphabet.decode c with
        | some v => Except.ok v | none => Except.error Error.invalidCharacter) = .ok vs →
      vs.map Alphabet.encode = cs.map Char.toLower := by
    intro cs
    induction cs with
    | nil => intro vs h; cases h; rfl
    | cons c cs ih =>
      intro vs h
      simp only [List.mapM_cons] at h
      cases hd : Alphabet.decode c with
      | none => simp [hd, Bind.bind, Except.bind] at h
      | some v =>
        simp only [hd] at h
        cases ht : cs.mapM (fun c => match Alphabet.decode c with
          | some v => Except.ok v | none => Except.error Error.invalidCharacter) with
        | error e => simp [ht, Bind.bind, Except.bind] at h
        | ok tail =>
          simp [ht, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
          subst vs
          simp only [List.map_cons, alphabet_decode_sound c v hd, ih tail ht]
  apply String.toList_inj.mp
  simpa [Alphabet.encodeList, String.toLower, String.toList_map] using aux s.toList vs h

theorem threshold_fromSymbol_sound (v : Symbol) (t : Threshold)
    (h : Threshold.fromSymbol v = .ok t) : t.toSymbol = v := by
  have hfinite : ∀ v : Symbol,
      ((Threshold.fromSymbol v).toOption.map Threshold.toSymbol).all (· == v) = true := by
    decide +kernel
  have hf := hfinite v
  rw [h] at hf
  change (t.toSymbol == v) = true at hf
  exact beq_iff_eq.mp hf

private theorem checksum_spec_iff (body suffix : List Symbol) :
    Spec.Checksum body suffix ↔
      Checksum.checksumLength (body ++ suffix).length = some suffix.length ∧
      Checksum.verify (body ++ suffix) = true := by
  simp only [Spec.Checksum, Checksum.checksumLength, Checksum.verify]
  split <;> rename_i hregular
  · simp only [List.length_append] at *
    simp [Checksum.verifyRegular]
    omega
  · split <;> rename_i hlong
    · simp only [List.length_append] at *
      simp [Checksum.verifyLong]
      omega
    · simp only [List.length_append] at *
      simp
      omega

/-- Every string described by the declarative format is accepted, in either
permitted case, with exactly the stated metadata and payload. -/
theorem parse_complete (s : String) (m : Message) (h : Spec.Encoding s m) :
    Encoding.parse s = .ok m := by
  obtain ⟨hascii, hcase, suffix, htext, hchecksum⟩ := h
  obtain ⟨hselect, hvalid⟩ := (checksum_spec_iff m.data suffix).1 hchecksum
  have hbound : (m.data ++ suffix).length ≤ 1018 := by
    rcases hchecksum with ⟨_, hb, _⟩ | ⟨_, _, hb, _⟩ <;> omega
  have hsize : ¬ s.utf8ByteSize > Encoding.maxStringBytes := by
    rw [← printable_lower_byteSize s hascii, htext,
      String.utf8ByteSize_append, encodeList_byteSize]
    change ¬ 3 + (m.data ++ suffix).length > 1021
    omega
  unfold Encoding.parse
  rw [ite_eq_right hsize, (printable_iff s).1 hascii, (uniformCase_iff s).1 hcase]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [htext, encoded_prefix, encoded_drop, alphabet_list_roundtrip]
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [hselect]
  dsimp only
  have hheader : ¬ (m.data ++ suffix).length < 6 + suffix.length := by
    simp only [Message.data, List.length_append, List.length_cons, List.length_nil,
      m.identifier.length_eq]
    omega
  rw [ite_eq_right hheader, hvalid]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  have hbody : (m.data ++ suffix).take ((m.data ++ suffix).length - suffix.length) = m.data := by
    simp
  rw [hbody]
  rcases m with ⟨threshold, ⟨symbols, hsymbols⟩, index, payload, hzero, hlen⟩
  obtain ⟨a,b,c,d,rfl⟩ := four_list symbols hsymbols
  simp only [Message.data, List.cons_append, List.nil_append]
  rw [threshold_symbol_roundtrip]
  exact message_create_roundtrip
    ⟨threshold, ⟨[a,b,c,d], hsymbols⟩, index, payload, hzero, hlen⟩

private theorem printable_lower_idem (s : String) (hs : Spec.Printable s) :
    s.toLower.toLower = s.toLower := by
  have hfinite : ∀ n : Fin 128,
      (Char.ofNat n.val).toLower.toLower = (Char.ofNat n.val).toLower := by
    decide +kernel
  apply String.toList_inj.mp
  simp only [String.toLower, String.toList_map, List.map_map]
  apply List.map_congr_left
  intro c hc
  have hb : c.toNat < 128 := by have := hs c hc; omega
  simpa using hfinite ⟨c.toNat, hb⟩

private theorem decoded_text (s : String) (vs : List Symbol)
    (hascii : Spec.Printable s)
    (hprefix : s.toLower.toList.take 3 = ['m', 's', '1'])
    (hdecode : Alphabet.decodeList (String.ofList (s.toLower.toList.drop 3)) = .ok vs) :
    s.toLower = "ms1" ++ Alphabet.encodeList vs := by
  have hn : (String.ofList (s.toLower.toList.drop 3)).toLower =
      String.ofList (s.toLower.toList.drop 3) := by
    apply String.toList_inj.mp
    have hh := congrArg (fun t : String => t.toList.drop 3) (printable_lower_idem s hascii)
    simpa [String.toLower, String.toList_map, List.map_drop] using hh
  have hd := alphabet_decodeList_sound _ vs hdecode
  rw [hn] at hd
  apply String.toList_inj.mp
  rw [String.toList_append]
  change s.toLower.toList = ['m', 's', '1'] ++ (Alphabet.encodeList vs).toList
  rw [hd, String.toList_ofList, ← hprefix]
  exact (List.take_append_drop 3 s.toLower.toList).symm

/-- Every successful generic parse satisfies the independent printed-format
and checksum conditions, with the same threshold, identifier, index and payload. -/
theorem parse_sound (s : String) (m : Message) (hp : Encoding.parse s = .ok m) :
    Spec.Encoding s m := by
  unfold Encoding.parse at hp
  by_cases hsize : s.utf8ByteSize > Encoding.maxStringBytes
  · rw [ite_eq_left hsize] at hp
    cases hp
  · rw [ite_eq_right hsize] at hp
    by_cases hascii : s.toList.any (fun c => c.toNat < 33 || c.toNat > 126) = true
    · rw [ite_eq_left hascii] at hp
      cases hp
    · rw [ite_eq_right hascii] at hp
      by_cases hcase : (s != s.toLower && s != s.toUpper) = true
      · rw [ite_eq_left hcase] at hp
        cases hp
      · rw [ite_eq_right hcase] at hp
        dsimp only at hp
        split at hp
        · cases hp
        · rename_i hprefix
          cases hd : Alphabet.decodeList (String.ofList (s.toLower.toList.drop 3)) with
          | error e => simp [hd, Bind.bind, Except.bind] at hp
          | ok vs =>
            rw [hd] at hp
            dsimp only [Bind.bind, Except.bind] at hp
            cases hn : Checksum.checksumLength vs.length with
            | none => simp [hn] at hp
            | some n =>
              rw [hn] at hp
              dsimp only [Pure.pure, Except.pure, Bind.bind, Except.bind] at hp
              split at hp
              · cases hp
              · rename_i hheader
                split at hp
                · cases hp
                · rename_i hverify
                  split at hp
                  next t a b c d index payload heq =>
                    cases ht : Threshold.fromSymbol t with
                    | error e => simp [ht] at hp
                    | ok threshold =>
                      rw [ht] at hp
                      dsimp only [Bind.bind, Except.bind] at hp
                      unfold Message.create at hp
                      split at hp
                      next hzero =>
                        split at hp
                        next hlen =>
                          cases hp
                          have ha : Spec.Printable s := (printable_iff s).2 (by simpa using hascii)
                          have hc : Spec.UniformCase s := (uniformCase_iff s).2 (by simpa using hcase)
                          refine ⟨ha, hc, vs.drop (vs.length - n), ?_, ?_⟩
                          all_goals
                            have hb :
                                (Message.data ⟨threshold, ⟨[a,b,c,d], rfl⟩, index, payload, hzero, hlen⟩) =
                                  vs.take (vs.length - n) := by
                              simp only [Message.data, List.cons_append, List.nil_append,
                                threshold_fromSymbol_sound t threshold ht]
                              exact heq.symm
                            rw [hb]
                          · rw [List.take_append_drop]
                            exact decoded_text s vs ha (by simpa using hprefix) hd
                          · apply (checksum_spec_iff _ _).2
                            rw [List.take_append_drop]
                            have hnl : n ≤ vs.length := by omega
                            simpa [List.length_drop, Nat.sub_sub_self hnl] using
                              And.intro hn (show Checksum.verify vs = true from by simpa using hverify)
                        next hlen => cases hp
                      next hzero => cases hp
                  next heq => cases hp

/-- Exact acceptance characterization of the generic executable parser. -/
theorem parse_iff_spec (s : String) (m : Message) :
    Encoding.parse s = .ok m ↔ Spec.Encoding s m :=
  ⟨parse_sound s m, parse_complete s m⟩

private theorem seed_payload_iff (m : Message) :
    Seed.validPayloadLength m.payload.length = true ↔
      (m.payload.length = 26 ∨ m.payload.length = 32 ∨ m.payload.length = 39 ∨
        m.payload.length = 45 ∨ m.payload.length = 52 ∨ m.payload.length = 103) := by
  simp only [Seed.validPayloadLength, Seed.supportedPayloadLengths,
    List.contains_cons, List.contains_nil,
    Bool.or_eq_true, beq_iff_eq, Bool.false_eq_true, or_false]

/-- The application parser accepts exactly the declarative BIP format with
one of the six supported master-seed payload lengths, for secrets and shares. -/
theorem seed_parse_iff_spec (s : String) (m : Message) :
    Seed.parse s = .ok m ↔ Spec.Seed s m := by
  have haux : Seed.parse s = .ok m ↔
      Encoding.parse s = .ok m ∧ Seed.validPayloadLength m.payload.length = true := by
    unfold Seed.parse
    cases hp : Encoding.parse s with
    | error e => simp [Bind.bind, Except.bind]
    | ok parsed =>
      dsimp only [Bind.bind, Except.bind]
      by_cases hv : Seed.validPayloadLength parsed.payload.length = true
      · simp [hv, Pure.pure, Except.pure]
        intro heq
        subst parsed
        exact hv
      · have hf : Seed.validPayloadLength parsed.payload.length = false := by simpa using hv
        simp [hf]
        intro heq
        subst parsed
        exact hf
  rw [haux, parse_iff_spec, seed_payload_iff]
  rfl

private theorem printable_upper_properties (c : Char) (hc : 33 ≤ c.toNat ∧ c.toNat ≤ 126) :
    (33 ≤ c.toUpper.toNat ∧ c.toUpper.toNat ≤ 126) ∧
      c.toUpper.toUpper = c.toUpper ∧ c.toUpper.toLower = c.toLower := by
  have hfinite : ∀ n : Fin 128, 33 ≤ n.val → n.val ≤ 126 →
      (33 ≤ (Char.ofNat n.val).toUpper.toNat ∧ (Char.ofNat n.val).toUpper.toNat ≤ 126) ∧
        (Char.ofNat n.val).toUpper.toUpper = (Char.ofNat n.val).toUpper ∧
        (Char.ofNat n.val).toUpper.toLower = (Char.ofNat n.val).toLower := by
    decide +kernel
  simpa using hfinite ⟨c.toNat, by omega⟩ hc.1 hc.2

/-- Uppercasing preserves the independently specified BIP message. -/
theorem encoding_spec_upper (s : String) (m : Message) (h : Spec.Encoding s m) :
    Spec.Encoding s.toUpper m := by
  obtain ⟨hascii, _, suffix, htext, hchecksum⟩ := h
  have hupper : Spec.Printable s.toUpper := by
    intro c hc
    simp only [String.toUpper, String.toList_map, List.mem_map] at hc
    obtain ⟨d, hd, rfl⟩ := hc
    exact (printable_upper_properties d (hascii d hd)).1
  have hu : s.toUpper.toUpper = s.toUpper := by
    apply String.toList_inj.mp
    simp only [String.toUpper, String.toList_map, List.map_map]
    apply List.map_congr_left
    intro c hc
    exact (printable_upper_properties c (hascii c hc)).2.1
  have hl : s.toUpper.toLower = s.toLower := by
    apply String.toList_inj.mp
    simp only [String.toUpper, String.toLower, String.toList_map, List.map_map]
    apply List.map_congr_left
    intro c hc
    exact (printable_upper_properties c (hascii c hc)).2.2
  exact ⟨hupper, Or.inr hu.symm, suffix, hl.trans htext, hchecksum⟩

/-- Every accepted generic input remains accepted after uppercasing. -/
theorem parse_upper (s : String) (m : Message) (h : Encoding.parse s = .ok m) :
    Encoding.parse s.toUpper = .ok m :=
  parse_complete _ m (encoding_spec_upper s m (parse_sound s m h))

/-- Full uppercase serialized-message roundtrip, including both checksum variants. -/
theorem parse_serializeUpper (m : Message) :
    Encoding.parse (Encoding.serializeUpper m) = .ok m :=
  parse_upper _ m (parse_serialize m)

/-- Uppercase application inputs preserve the same master-seed/share message. -/
theorem seed_parse_upper (s : String) (m : Message) (h : Seed.parse s = .ok m) :
    Seed.parse s.toUpper = .ok m := by
  obtain ⟨he, hl⟩ := (seed_parse_iff_spec s m).1 h
  exact (seed_parse_iff_spec _ m).2 ⟨encoding_spec_upper s m he, hl⟩

/-- Uppercase secret strings decode to the same seed, with arbitrary padding. -/
theorem seed_string_upper_roundtrip (seed : Seed) (identifier : Identifier)
    (threshold : Threshold) (padding : Symbol) :
    Seed.decodeString (Seed.encodeString seed identifier threshold padding).toUpper = .ok seed := by
  have hp : Seed.parse (Seed.encodeString seed identifier threshold padding) =
      .ok (Seed.encode seed identifier threshold padding) := by
    unfold Seed.parse Seed.encodeString
    rw [parse_serialize]
    dsimp only [Bind.bind, Except.bind]
    rw [encoded_seed_payload_supported]
    rfl
  unfold Seed.decodeString
  rw [seed_parse_upper _ _ hp]
  exact seed_roundtrip seed identifier threshold padding

end Codex32.Proofs
