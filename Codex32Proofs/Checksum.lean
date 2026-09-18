import Codex32.Checksum

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-! Kernel-checked properties of the executable BIP 93 checksum operations. -/

namespace Codex32.Checksum

@[simp] theorem extract_length (count residue : Nat) :
    (extract count residue).length = count := by
  simp [extract]

@[simp] theorem createRegular_length (data : List Symbol) :
    (createRegular data).length = 13 := by
  simp [createRegular]

@[simp] theorem createLong_length (data : List Symbol) :
    (createLong data).length = 15 := by
  simp [createLong]

theorem checksumLength_regular_iff (n : Nat) :
    checksumLength n = some 13 ↔ n ≤ 88 := by
  simp only [checksumLength]
  split <;> simp_all <;> omega

theorem checksumLength_long_iff (n : Nat) :
    checksumLength n = some 15 ↔ 91 ≤ n ∧ n ≤ 1018 := by
  simp only [checksumLength]
  split <;> simp_all <;> omega

theorem checksumLength_invalid_iff (n : Nat) :
    checksumLength n = none ↔ n = 89 ∨ n = 90 ∨ 1018 < n := by
  simp only [checksumLength]
  split <;> simp_all <;> omega

/-- Construction always picks a permitted completed codeword length. -/
theorem create_selects_valid_length (data checksum : List Symbol)
    (h : create data = .ok checksum) :
    checksumLength (data ++ checksum).length = some checksum.length := by
  unfold create at h
  split at h
  · unfold createBounded at h
    split at h
    · cases h
      simp only [List.length_append, createRegular_length]
      apply (checksumLength_regular_iff _).2
      omega
    · cases h
      simp only [List.length_append, createLong_length]
      apply (checksumLength_long_iff _).2
      omega
  · cases h

/-- Exactly 1003 data symbols can precede the largest supported checksum. -/
theorem create_exists_iff (data : List Symbol) :
    (∃ checksum, create data = .ok checksum) ↔ data.length ≤ 1003 := by
  unfold create
  split
  · exact ⟨fun _ => by assumption, fun _ => ⟨_, rfl⟩⟩
  · simp_all

/-- Variant selection prevents acceptance of forbidden expanded lengths. -/
theorem verify_rejects_invalid_length (data : List Symbol)
    (h : data.length = 89 ∨ data.length = 90 ∨ 1018 < data.length) :
    verify data = false := by
  simp [verify, (checksumLength_invalid_iff _).2 h]

/- The finite-width model below is confined to proofs. `*_toNat` proves that
it agrees with the executable, arbitrary-precision recurrence. Linearity
splits a suffix into the zero-symbol advance and its own zero-state residue;
the extracted checksum digits then cancel the advance. -/
private def stepBV {w : Nat} (shift : Nat) (mask : BitVec w)
    (generators : List (BitVec w)) (residue value : BitVec w) : BitVec w :=
  let top := residue >>> shift
  let next := ((residue &&& mask) <<< 5) ^^^ value
  generators.zipIdx.foldl (fun acc (generator, i) =>
    if ((top >>> i) &&& 1) == 1 then acc ^^^ generator else acc) next

private theorem bit_condition (x : BitVec (w+1)) :
    ((x &&& 1) == 1) = x.getLsbD 0 := by
  change ((x &&& (1#(w+1))) == (1#(w+1))) = x.getLsbD 0
  rw [BitVec.and_one_eq_setWidth_ofBool_getLsbD]
  cases x.getLsbD 0 <;> simp

private theorem gate_linear (x y g : BitVec w) (a b : Bool) :
    (if a ^^ b then (x ^^^ y) ^^^ g else x ^^^ y) =
      (if a then x ^^^ g else x) ^^^ (if b then y ^^^ g else y) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  cases a <;> cases b <;>
    simp [BitVec.getLsbD_xor, Bool.xor_left_comm, Bool.xor_comm]

private theorem fold_gate_xor (gs : List (BitVec w × Nat)) (a b : Nat → Bool)
    (x y : BitVec w) :
    gs.foldl (fun acc (g, i) => if a i ^^ b i then acc ^^^ g else acc) (x ^^^ y) =
      gs.foldl (fun acc (g, i) => if a i then acc ^^^ g else acc) x ^^^
      gs.foldl (fun acc (g, i) => if b i then acc ^^^ g else acc) y := by
  induction gs generalizing x y with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.foldl_cons]
    rw [gate_linear]
    exact ih _ _

private theorem stepBV_xor (shift : Nat) (mask : BitVec (w+1))
    (gens : List (BitVec (w+1))) (r s v t : BitVec (w+1)) :
    stepBV shift mask gens (r ^^^ s) (v ^^^ t) =
      stepBV shift mask gens r v ^^^ stepBV shift mask gens s t := by
  unfold stepBV
  simp only [bit_condition, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_xor]
  have hadd (x y : BitVec (w+1)) :
      ((x ^^^ y) &&& mask) <<< 5 = (x &&& mask) <<< 5 ^^^ (y &&& mask) <<< 5 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i
    simp [BitVec.getLsbD_shiftLeft, Bool.and_xor_distrib_right, Bool.and_xor_distrib_left]
  rw [hadd]
  have hinit : (r &&& mask) <<< 5 ^^^ (s &&& mask) <<< 5 ^^^ (v ^^^ t) =
      ((r &&& mask) <<< 5 ^^^ v) ^^^ ((s &&& mask) <<< 5 ^^^ t) := by ac_rfl
  rw [hinit]
  simpa only using fold_gate_xor gens.zipIdx
    (fun i => r.getLsbD (shift + (i + 0))) (fun i => s.getLsbD (shift + (i + 0)))
    ((r &&& mask) <<< 5 ^^^ v) ((s &&& mask) <<< 5 ^^^ t)

private def regularStepBV (r v : BitVec 65) : BitVec 65 :=
  stepBV 60 0x0fffffffffffffff
    [0x19dc500ce73fde210, 0x1bfae00def77fe529, 0x1fbd920fffe7bee52,
     0x1739640bdeee3fdad, 0x07729a039cfc75f5a] r v
private theorem toNat_ite (p : Prop) [Decidable p] (x y : BitVec w) :
    (if p then x else y).toNat = if p then x.toNat else y.toNat := by
  split <;> rfl
private theorem regularStepBV_xor (r s v w : BitVec 65) :
    regularStepBV (r ^^^ s) (v ^^^ w) = regularStepBV r v ^^^ regularStepBV s w := by
  exact stepBV_xor (w := 64) 60 _ _ r s v w
private theorem regularStepBV_toNat (r : BitVec 65) (v : Symbol) :
    (regularStepBV r (BitVec.ofNat 65 v.val)).toNat =
      step 60 0x0fffffffffffffff regularGenerators r.toNat v := by
  have hv : v.val < 2^65 := by have := v.isLt; omega
  have hm := Nat.and_le_right (n := r.toNat) (m := 0x0fffffffffffffff)
  have hs : (r.toNat &&& 0x0fffffffffffffff) <<< 5 < 2^65 := by
    rw [Nat.shiftLeft_eq]
    omega
  simp only [regularStepBV, stepBV, step, regularGenerators,
    List.zipIdx_cons, List.zipIdx_nil, List.foldl_cons, List.foldl_nil]
  simp [toNat_ite, BitVec.toNat_eq, ← Nat.shiftRight_add, BitVec.toNat_xor,
    BitVec.toNat_shiftLeft, BitVec.toNat_and,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt hs]

private def extractBV (count : Nat) (r : BitVec w) : List (BitVec w) :=
  (List.range count).map fun i => (r >>> (5 * (count - 1 - i))) &&& 31

private theorem shift_add (r : BitVec w) (a b : Nat) :
    r >>> (a+b) = (r >>> a) >>> b := by
  apply BitVec.eq_of_toNat_eq
  simp [Nat.shiftRight_add]
private theorem extractBV_succ (n : Nat) (r : BitVec w) :
    extractBV (n+1) r = extractBV n (r >>> 5) ++ [r &&& 31] := by
  simp only [extractBV, List.range_succ, List.map_append, List.map_cons, List.map_nil]
  simp only [Nat.add_sub_cancel, Nat.sub_self, Nat.mul_zero, BitVec.ushiftRight_zero]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi := List.mem_range.mp hi
  have he : 5 * (n - i) = 5 + 5 * (n - 1 - i) := by omega
  simp only [he, shift_add]
private theorem fold_extractBV (f : BitVec w → BitVec w → BitVec w)
    (hchunk : ∀ (r : BitVec w), f (r >>> 5) (r &&& 31) = r)
    (n : Nat) (r : BitVec w) (h : r >>> (5*n) = 0) :
    (extractBV n r).foldl f 0 = r := by
  induction n generalizing r with
  | zero => simpa [extractBV] using h.symm
  | succ n ih =>
    rw [extractBV_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hr : (r >>> 5) >>> (5*n) = 0 := by
      rw [← shift_add]
      simpa [Nat.mul_add, Nat.add_comm] using h
    rw [ih (r >>> 5) hr]
    exact hchunk r

private theorem regularChunk (r : BitVec 65) : regularStepBV (r >>> 5) (r &&& 31) = r := by
  unfold regularStepBV stepBV
  simp only [List.zipIdx_cons, List.zipIdx_nil, List.foldl_cons, List.foldl_nil]
  simp [BitVec.ushiftRight_eq_zero]
  rw [BitVec.shiftLeft_and_distrib, BitVec.shiftLeft_ushiftRight]
  have hm : (BitVec.ofNat 65 1152921504606846975) <<< (5 : Nat) = BitVec.allOnes 65 <<< (5 : Nat) := by decide +kernel
  rw [hm, BitVec.and_assoc, BitVec.and_self]
  have hd (a b c : BitVec 65) : a &&& b ^^^ a &&& c = a &&& (b ^^^ c) := by
    apply BitVec.eq_of_getLsbD_eq_iff.mpr
    intro i _
    simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and]
    cases a.getLsbD i <;> simp
  rw [hd]
  have hc : (BitVec.allOnes 65 <<< (5 : Nat)) ^^^ (BitVec.ofNat 65 31) = BitVec.allOnes 65 := by decide +kernel
  rw [hc, BitVec.and_allOnes]


private theorem regularStepBV_extract (r : BitVec 65) :
    (extractBV 13 r).foldl regularStepBV 0 = r := by
  exact fold_extractBV regularStepBV regularChunk 13 r
    (BitVec.ushiftRight_eq_zero (by decide))

private theorem foldBV_xor (f : BitVec w → BitVec w → BitVec w)
    (hf : ∀ r s v t, f (r ^^^ s) (v ^^^ t) = f r v ^^^ f s t)
    (xs : List (BitVec w)) (r s : BitVec w) :
    xs.foldl f (r ^^^ s) =
      (List.replicate xs.length 0).foldl f r ^^^ xs.foldl f s := by
  induction xs generalizing r s with
  | nil => simp
  | cons v vs ih =>
    simp only [List.foldl_cons, List.length_cons, List.replicate_succ]
    rw [show f (r ^^^ s) v = f r 0 ^^^ f s v by simpa using hf r s 0 v]
    exact ih _ _

private theorem foldBV_decompose (f : BitVec w → BitVec w → BitVec w)
    (hf : ∀ r s v t, f (r ^^^ s) (v ^^^ t) = f r v ^^^ f s t)
    (xs : List (BitVec w)) (r : BitVec w) :
    xs.foldl f r =
      (List.replicate xs.length 0).foldl f r ^^^ xs.foldl f 0 := by
  simpa using foldBV_xor f hf xs r 0

private theorem regularSuffixBV (r : BitVec 65) :
    (extractBV 13 ((List.replicate 13 0).foldl regularStepBV r ^^^
      BitVec.ofNat 65 regularConstant)).foldl regularStepBV r =
      BitVec.ofNat 65 regularConstant := by
  rw [foldBV_decompose regularStepBV regularStepBV_xor]
  rw [regularStepBV_extract]
  simp [extractBV, ← BitVec.xor_assoc]

private theorem map_extractBV (hw : 32 ≤ 2^w) (count : Nat) (r : BitVec w) :
    (extract count r.toNat).map (fun v => BitVec.ofNat w v.val) = extractBV count r := by
  simp only [extract, extractBV, List.map_map]
  apply List.map_congr_left
  intro i _
  apply BitVec.eq_of_toNat_eq
  have hm : (r.toNat >>> (5 * (count - 1 - i))) &&& 31 < 32 :=
    Nat.and_lt_two_pow _ (by decide : 31 < 2^5)
  have hmw : (r.toNat >>> (5 * (count - 1 - i))) &&& 31 < 2^w :=
    Nat.lt_of_lt_of_le hm hw
  have hc : 31 < 2^w := by omega
  simp only [Function.comp_apply, Symbol.ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hmw, BitVec.toNat_and,
    BitVec.toNat_ushiftRight]
  change _ = _ &&& (31 % 2^w)
  rw [Nat.mod_eq_of_lt hc]

private theorem fold_toNat (f : BitVec w → BitVec w → BitVec w)
    (g : Nat → Symbol → Nat)
    (hf : ∀ r v, (f r (BitVec.ofNat w v.val)).toNat = g r.toNat v)
    (data : List Symbol) (r : BitVec w) :
    ((data.map (fun v => BitVec.ofNat w v.val)).foldl f r).toNat =
      data.foldl g r.toNat := by
  induction data generalizing r with
  | nil => rfl
  | cons v vs ih =>
    simp only [List.map_cons, List.foldl_cons, ih, hf]

private theorem regularFold_toNat (data : List Symbol) (r : BitVec 65) :
    ((data.map (fun v => BitVec.ofNat 65 v.val)).foldl regularStepBV r).toNat =
      data.foldl (step 60 0x0fffffffffffffff regularGenerators) r.toNat :=
  fold_toNat regularStepBV _ regularStepBV_toNat data r

/-- The arbitrary-precision regular recurrence stays within its 65-bit register. -/
theorem regularPolymod_lt (data : List Symbol) : regularPolymod data < 2^65 := by
  change data.foldl (step 60 0x0fffffffffffffff regularGenerators)
    (BitVec.ofNat 65 initResidue).toNat < 2^65
  rw [← regularFold_toNat]
  exact BitVec.isLt _

/-- Appending the regular checksum gives the required residue for every prefix;
the separate verifier also enforces the checksum's length limit. -/
theorem regularPolymod_createRegular (data : List Symbol) :
    regularPolymod (data ++ createRegular data) = regularConstant := by
  let r : BitVec 65 := (data.map (fun v => BitVec.ofNat 65 v.val)).foldl regularStepBV
    (BitVec.ofNat 65 initResidue)
  have hr : r.toNat = regularPolymod data := by
    exact regularFold_toNat data (BitVec.ofNat 65 initResidue)
  have hz : ((List.replicate 13 0).foldl regularStepBV r).toNat =
      regularPolymod (data ++ List.replicate 13 (Symbol.ofNat 0)) := by
    have h := regularFold_toNat (List.replicate 13 (Symbol.ofNat 0)) r
    simpa only [List.map_replicate, hr, regularPolymod, List.foldl_append,
      show BitVec.ofNat 65 (Symbol.ofNat 0).val = (0 : BitVec 65) by decide] using h
  have hc : (createRegular data).map (fun v => BitVec.ofNat 65 v.val) =
      extractBV 13 ((List.replicate 13 0).foldl regularStepBV r ^^^
        BitVec.ofNat 65 regularConstant) := by
    have h := map_extractBV (by decide : 32 ≤ 2^65) 13
      ((List.replicate 13 0).foldl regularStepBV r ^^^ BitVec.ofNat 65 regularConstant)
    simpa only [createRegular, BitVec.toNat_xor, hz, BitVec.toNat_ofNat,
      show regularConstant % 2^65 = regularConstant by decide] using h
  have h := regularFold_toNat (createRegular data) r
  rw [hc, regularSuffixBV] at h
  simpa only [BitVec.toNat_ofNat, show regularConstant % 2^65 = regularConstant by decide,
    hr, regularPolymod, List.foldl_append] using h.symm

private def longStepBV (r v : BitVec 75) : BitVec 75 :=
  stepBV 70 0x3fffffffffffffffff
    [0x3d59d273535ea62d897, 0x7a9becb6361c6c51507, 0x543f9b7e6c38d8a2a0e,
     0x0c577eaeccf1990d13c, 0x1887f74f8dc71b10651] r v

private theorem longStepBV_xor (r s v w : BitVec 75) :
    longStepBV (r ^^^ s) (v ^^^ w) = longStepBV r v ^^^ longStepBV s w := by
  exact stepBV_xor (w := 74) 70 _ _ r s v w

private theorem longStepBV_toNat (r : BitVec 75) (v : Symbol) :
    (longStepBV r (BitVec.ofNat 75 v.val)).toNat =
      step 70 0x3fffffffffffffffff longGenerators r.toNat v := by
  have hv : v.val < 2^75 := by have := v.isLt; omega
  have hm := Nat.and_le_right (n := r.toNat) (m := 0x3fffffffffffffffff)
  have hs : (r.toNat &&& 0x3fffffffffffffffff) <<< 5 < 2^75 := by
    rw [Nat.shiftLeft_eq]
    omega
  simp only [longStepBV, stepBV, step, longGenerators,
    List.zipIdx_cons, List.zipIdx_nil, List.foldl_cons, List.foldl_nil]
  simp [toNat_ite, BitVec.toNat_eq, ← Nat.shiftRight_add, BitVec.toNat_xor,
    BitVec.toNat_shiftLeft, BitVec.toNat_and,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt hs]
private theorem longChunk (r : BitVec 75) : longStepBV (r >>> 5) (r &&& 31) = r := by
  unfold longStepBV stepBV
  simp only [List.zipIdx_cons, List.zipIdx_nil, List.foldl_cons, List.foldl_nil]
  simp [BitVec.ushiftRight_eq_zero]
  rw [BitVec.shiftLeft_and_distrib, BitVec.shiftLeft_ushiftRight]
  have hm : (BitVec.ofNat 75 0x3fffffffffffffffff) <<< (5 : Nat) = BitVec.allOnes 75 <<< (5 : Nat) := by decide +kernel
  rw [hm, BitVec.and_assoc, BitVec.and_self]
  have hd (a b c : BitVec 75) : a &&& b ^^^ a &&& c = a &&& (b ^^^ c) := by
    apply BitVec.eq_of_getLsbD_eq_iff.mpr
    intro i _
    simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and]
    cases a.getLsbD i <;> simp
  rw [hd]
  have hc : (BitVec.allOnes 75 <<< (5 : Nat)) ^^^ (BitVec.ofNat 75 31) = BitVec.allOnes 75 := by decide +kernel
  rw [hc, BitVec.and_allOnes]

private theorem longStepBV_extract (r : BitVec 75) :
    (extractBV 15 r).foldl longStepBV 0 = r := by
  exact fold_extractBV longStepBV longChunk 15 r
    (BitVec.ushiftRight_eq_zero (by decide))
private theorem longSuffixBV (r : BitVec 75) :
    (extractBV 15 ((List.replicate 15 0).foldl longStepBV r ^^^
      BitVec.ofNat 75 longConstant)).foldl longStepBV r =
      BitVec.ofNat 75 longConstant := by
  rw [foldBV_decompose longStepBV longStepBV_xor]
  rw [longStepBV_extract]
  simp [extractBV, ← BitVec.xor_assoc]
private theorem longFold_toNat (data : List Symbol) (r : BitVec 75) :
    ((data.map (fun v => BitVec.ofNat 75 v.val)).foldl longStepBV r).toNat =
      data.foldl (step 70 0x3fffffffffffffffff longGenerators) r.toNat :=
  fold_toNat longStepBV _ longStepBV_toNat data r

/-- The arbitrary-precision long recurrence stays within its 75-bit register. -/
theorem longPolymod_lt (data : List Symbol) : longPolymod data < 2^75 := by
  change data.foldl (step 70 0x3fffffffffffffffff longGenerators)
    (BitVec.ofNat 75 initResidue).toNat < 2^75
  rw [← longFold_toNat]
  exact BitVec.isLt _
/-- The corresponding unconditional residue identity for the long checksum. -/
theorem longPolymod_createLong (data : List Symbol) :
    longPolymod (data ++ createLong data) = longConstant := by
  let r : BitVec 75 := (data.map (fun v => BitVec.ofNat 75 v.val)).foldl longStepBV
    (BitVec.ofNat 75 initResidue)
  have hr : r.toNat = longPolymod data := by
    exact longFold_toNat data (BitVec.ofNat 75 initResidue)
  have hz : ((List.replicate 15 0).foldl longStepBV r).toNat =
      longPolymod (data ++ List.replicate 15 (Symbol.ofNat 0)) := by
    have h := longFold_toNat (List.replicate 15 (Symbol.ofNat 0)) r
    simpa only [List.map_replicate, hr, longPolymod, List.foldl_append,
      show BitVec.ofNat 75 (Symbol.ofNat 0).val = (0 : BitVec 75) by decide] using h
  have hc : (createLong data).map (fun v => BitVec.ofNat 75 v.val) =
      extractBV 15 ((List.replicate 15 0).foldl longStepBV r ^^^
        BitVec.ofNat 75 longConstant) := by
    have h := map_extractBV (by decide : 32 ≤ 2^75) 15
      ((List.replicate 15 0).foldl longStepBV r ^^^ BitVec.ofNat 75 longConstant)
    simpa only [createLong, BitVec.toNat_xor, hz, BitVec.toNat_ofNat,
      show longConstant % 2^75 = longConstant by decide] using h
  have h := longFold_toNat (createLong data) r
  rw [hc, longSuffixBV] at h
  simpa only [BitVec.toNat_ofNat, show longConstant % 2^75 = longConstant by decide,
    hr, longPolymod, List.foldl_append] using h.symm

/-- Every regular checksum produced within its period verifies. -/
theorem verifyRegular_createRegular (data : List Symbol) (h : data.length ≤ 75) :
    verifyRegular (data ++ createRegular data) = true := by
  simp [verifyRegular, regularPolymod_createRegular]
  omega

/-- Every long checksum produced within its period verifies. -/
theorem verifyLong_createLong (data : List Symbol) (h : data.length ≤ 1003) :
    verifyLong (data ++ createLong data) = true := by
  simp [verifyLong, longPolymod_createLong]
  omega

/-- The executable constructor always produces a checksum accepted by the
executable verifier, including the required choice of regular/long variant. -/
theorem verify_create (data checksum : List Symbol)
    (h : create data = .ok checksum) : verify (data ++ checksum) = true := by
  unfold create at h
  split at h
  · unfold createBounded at h
    split at h
    · cases h
      have hl : checksumLength (data ++ createRegular data).length = some 13 := by
        apply (checksumLength_regular_iff _).2
        simp only [List.length_append, createRegular_length]
        omega
      simp only [verify, hl]
      exact verifyRegular_createRegular data (by omega)
    · cases h
      have hl : checksumLength (data ++ createLong data).length = some 15 := by
        apply (checksumLength_long_iff _).2
        simp only [List.length_append, createLong_length]
        omega
      simp only [verify, hl]
      exact verifyLong_createLong data (by omega)
  · cases h

end Codex32.Checksum
