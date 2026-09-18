import Codex32Proofs.Bch
import Codex32Proofs.Poly

/-!
Burst-erasure uniqueness for the BCH checksums: two strings of equal length
with equal polymod residues that agree outside a consecutive window of at most
13 (regular) or 15 (long) symbols are identical. The proof bridge shows the
polymod register recurrence performs polynomial reduction modulo the generator,
so an equal residue makes the generator divide the difference polynomial; a
burst-shaped difference is `xˢ·W` with `W` shorter than the generator, forcing
`W = 0` through the monic-product support theorem.
-/

namespace Codex32

open Field Poly

set_option maxHeartbeats 0

private theorem getD_unpack (n : Nat) (r : Nat) (i : Nat) (hi : i < n) :
    (unpack n r).getD i 0 = Symbol.ofNat ((r >>> (5 * i)) &&& 31) := by
  rw [unpack, List.getD, List.getElem?_map, List.getElem?_range hi]
  rfl

private theorem getD_singleton (v : Symbol) (i : Nat) :
    [v].getD i 0 = if i = 0 then v else 0 := by
  cases i with
  | zero => rfl
  | succ i => rfl

private theorem getD_eq_getElem (p : List Symbol) (i : Nat) (h : i < p.length) :
    p.getD i 0 = p[i] := by
  rw [List.getD, List.getElem?_eq_getElem h, Option.getD_some]

private theorem getD_drop (s : Nat) (p : List Symbol) (i : Nat) :
    (p.drop s).getD i 0 = p.getD (s + i) 0 := by
  induction s generalizing p i with
  | zero => rw [List.drop_zero, Nat.zero_add]
  | succ s ih =>
    cases p with
    | nil => simp
    | cons a as =>
      have h : s + 1 + i = (s + i) + 1 := by omega
      rw [List.drop_succ_cons, h, List.getD_cons_succ, ih as i]

private theorem getD_reverse (p : List Symbol) (i : Nat) :
    p.reverse.getD i 0 = if i < p.length then p.getD (p.length - 1 - i) 0 else 0 := by
  rw [List.getD]
  by_cases h : i < p.length
  · rw [ite_eq_left h, List.getElem?_reverse h]
    have h2 : p.length - 1 - i < p.length := by omega
    rw [List.getElem?_eq_getElem h2, Option.getD_some]
    rw [List.getD, List.getElem?_eq_getElem h2, Option.getD_some]
  · rw [ite_eq_right h]
    have h2 : p.reverse.length ≤ i := by simp [List.length_reverse]; omega
    rw [List.getElem?_eq_none h2]
    rfl

private theorem getD_zipWith (f : Symbol → Symbol → Symbol) (A B : List Symbol) (i : Nat) :
    (List.zipWith f A B).getD i 0 =
      if i < min A.length B.length then f (A.getD i 0) (B.getD i 0) else 0 := by
  induction A generalizing B i with
  | nil => simp [List.zipWith]
  | cons a as ih =>
    cases B with
    | nil => simp [List.zipWith]
    | cons b bs =>
      rw [List.zipWith_cons_cons]
      cases i with
      | zero => simp
      | succ i =>
        rw [List.getD_cons_succ, ih]
        simp only [List.getD_cons_succ, List.length_cons]
        by_cases h : i < min as.length bs.length
        · rw [ite_eq_left h, ite_eq_left (show i + 1 < min (as.length + 1) (bs.length + 1) from by omega)]
        · rw [ite_eq_right h, ite_eq_right (show ¬ (i + 1 < min (as.length + 1) (bs.length + 1)) from by omega)]

private theorem getD_zipWith_of_length (f : Symbol → Symbol → Symbol) (A B : List Symbol)
    (h : A.length = B.length) (i : Nat) :
    (List.zipWith f A B).getD i 0 =
      if i < A.length then f (A.getD i 0) (B.getD i 0) else 0 := by
  rw [getD_zipWith, ← h, Nat.min_self]

/-- A chunk recurrence gives the single-step polynomial identity for any
positive register width and its monic generator `low ++ [1]`. -/
private theorem step_poly_getD_g (width : Nat) (hwidth : 0 < width)
    (low : List Symbol) (hlen : low.length = width) (r next : Nat) (v : Symbol)
    (hchunk : ∀ j : Fin width,
      Symbol.ofNat ((next >>> (5 * j.val)) &&& 31) =
        add (if j.val = 0 then v else Symbol.ofNat ((r >>> (5 * (j.val - 1))) &&& 31))
          (mul (Symbol.ofNat (r >>> (5 * (width - 1))))
            (low[j.val]'(by rw [hlen]; exact j.isLt)))) (i : Nat) :
    (pAdd (pShift 1 (unpack width r)) [v]).getD i 0 =
      (pAdd (unpack width next)
        (pScale (Symbol.ofNat (r >>> (5 * (width - 1)))) (low ++ [1]))).getD i 0 := by
  have htop : Symbol.ofNat ((r >>> (5 * (width - 1))) &&& 31) =
      Symbol.ofNat (r >>> (5 * (width - 1))) := by
    rw [Nat.and_two_pow_sub_one_eq_mod _ 5]
    exact Fin.ext (Nat.mod_mod _ _)
  have hgi : ∀ j < width, (low ++ [1]).getD j 0 = low.getD j 0 := by
    intro j hj
    rw [List.getD, List.getD, List.getElem?_append_left (by omega)]
  have hgwidth : (low ++ [1]).getD width 0 = 1 := by
    simp [List.getD, hlen]
  have hgout : ∀ j > width, (low ++ [1]).getD j 0 = 0 := by
    intro j hj
    apply Poly.getD_eq_zero_of_le
    simp only [List.length_append, hlen, List.length_singleton]
    omega
  rw [getD_pAdd, getD_pAdd, getD_pShift, getD_pScale]
  by_cases h0 : i = 0
  · subst i
    rw [ite_eq_left (by decide : 0 < 1), getD_singleton, ite_eq_left rfl, Field.zero_add,
      getD_unpack width _ 0 hwidth, hgi 0 hwidth, hchunk ⟨0, hwidth⟩]
    simp only [↓reduceIte]
    rw [getD_eq_getElem low 0 (by omega), add_assoc, add_self, Field.add_zero]
  · by_cases hi : i < width
    · rw [ite_eq_right (by omega), getD_singleton, ite_eq_right h0, Field.add_zero,
        getD_unpack width _ i hi, getD_unpack width _ (i - 1) (by omega), hgi i hi,
        hchunk ⟨i, hi⟩]
      simp only [h0, ↓reduceIte]
      rw [getD_eq_getElem low i (by omega), add_assoc, add_self, Field.add_zero]
    · by_cases hiwidth : i = width
      · subst i
        rw [ite_eq_right (by omega), getD_singleton, ite_eq_right (by omega : width ≠ 0),
          Field.add_zero, getD_unpack width _ (width - 1) (by omega),
          Poly.getD_eq_zero_of_le (unpack width next) width (by simp [unpack]),
          hgwidth, Field.zero_add, Field.mul_one, htop]
      · have hout1 : (unpack width next).getD i 0 = 0 :=
          Poly.getD_eq_zero_of_le _ i (by simp [unpack]; omega)
        have hout2 : (unpack width r).getD (i - 1) 0 = 0 :=
          Poly.getD_eq_zero_of_le _ (i - 1) (by simp [unpack]; omega)
        rw [ite_eq_right (by omega), getD_singleton, ite_eq_right h0, Field.add_zero,
          hout1, hout2, hgout i (by omega), Field.zero_add, Field.mul_zero]

/-- A bounded register recurrence with the single-step polynomial identity
reduces the word polynomial modulo its generator. -/
private theorem bridge_g (width shift : Nat) (step : Nat → Symbol → Nat)
    (generator : List Symbol) (hne : generator ≠ [])
    (step_bound : ∀ r v, step r v < 2 ^ (5 * width))
    (step_poly : ∀ r v, r < 2 ^ (5 * width) → ∀ i,
      (pAdd (pShift 1 (unpack width r)) [v]).getD i 0 =
        (pAdd (unpack width (step r v))
          (pScale (Symbol.ofNat (r >>> shift)) generator)).getD i 0)
    (vs : List Symbol) (r : Nat) (hr : r < 2 ^ (5 * width)) :
    ∃ T : List Symbol, T.length = vs.length ∧ ∀ i,
      (pAdd vs.reverse (pShift vs.length (unpack width r))).getD i 0 =
        (pAdd (unpack width (vs.foldl step r)) (pMul generator T)).getD i 0 := by
  induction vs generalizing r with
  | nil =>
    refine ⟨[], rfl, fun i => ?_⟩
    simp only [List.reverse_nil, List.foldl_nil, List.length_nil, pShift_zero, pMul_nil,
      pAdd_nil_left, pAdd_nil_right]
  | cons v vs ih =>
    obtain ⟨T, hTlen, hT⟩ := ih (step r v) (step_bound r v)
    refine ⟨T ++ [Symbol.ofNat (r >>> shift)], by simp [hTlen], fun i => ?_⟩
    have hsnoc : pAdd vs.reverse (pShift vs.length [v]) = vs.reverse ++ [v] :=
      pAdd_pShift_singleton v vs.length vs.reverse List.length_reverse
    have hstep : (pShift vs.length (pAdd (pShift 1 (unpack width r)) [v])).getD i 0 =
        (pShift vs.length (pAdd (unpack width (step r v))
          (pScale (Symbol.ofNat (r >>> shift)) generator))).getD i 0 := by
      rw [getD_pShift, getD_pShift]
      split
      · rfl
      · exact step_poly r v hr (i - vs.length)
    rw [← pAdd_pShift, ← pAdd_pShift, getD_pAdd, getD_pAdd, getD_pShift_shift] at hstep
    rw [List.reverse_cons, List.foldl_cons, List.length_cons, getD_pAdd, getD_pAdd,
      ← hsnoc, getD_pAdd, pMul_snoc generator hne _ T, getD_pAdd, hTlen]
    have hi := hT i
    rw [getD_pAdd, getD_pAdd] at hi
    calc
      _ = add (vs.reverse.getD i 0)
          (add ((pShift (vs.length + 1) (unpack width r)).getD i 0)
            ((pShift vs.length [v]).getD i 0)) := by ac_rfl
      _ = add (vs.reverse.getD i 0)
          (add ((pShift vs.length (unpack width (step r v))).getD i 0)
            ((pShift vs.length (pScale (Symbol.ofNat (r >>> shift)) generator)).getD i 0)) := by
        rw [hstep]
      _ = add (add (vs.reverse.getD i 0)
          ((pShift vs.length (unpack width (step r v))).getD i 0))
          ((pShift vs.length (pScale (Symbol.ofNat (r >>> shift)) generator)).getD i 0) := by ac_rfl
      _ = _ := by rw [hi]; ac_rfl

/-- Processing a regular-checksum word gives its polynomial plus the shifted
start register, modulo a multiple of the generator. -/
theorem regular_bridge (vs : List Symbol) (r : Nat) (hr : r < 2 ^ 65) :
    ∃ T : List Symbol, T.length = vs.length ∧ ∀ i,
      (pAdd vs.reverse (pShift vs.length (unpack 13 r))).getD i 0 =
        (pAdd (unpack 13 (vs.foldl (Checksum.step 60 0x0fffffffffffffff
            Checksum.regularGenerators) r))
          (pMul GF1024.regularGenerator T)).getD i 0 :=
  bridge_g 13 60 (Checksum.step 60 0x0fffffffffffffff Checksum.regularGenerators)
    GF1024.regularGenerator (by decide) GF1024.regular_step_bound
    (fun r v hr => step_poly_getD_g 13 (by decide) regularLow rfl r _ v
      (GF1024.regular_step_chunk r v hr)) vs r hr

/-- Processing a long-checksum word gives its polynomial plus the shifted
start register, modulo a multiple of the generator. -/
theorem long_bridge (vs : List Symbol) (r : Nat) (hr : r < 2 ^ 75) :
    ∃ T : List Symbol, T.length = vs.length ∧ ∀ i,
      (pAdd vs.reverse (pShift vs.length (unpack 15 r))).getD i 0 =
        (pAdd (unpack 15 (vs.foldl (Checksum.step 70 0x3fffffffffffffffff
            Checksum.longGenerators) r))
          (pMul GF1024.longGenerator T)).getD i 0 :=
  bridge_g 15 70 (Checksum.step 70 0x3fffffffffffffffff Checksum.longGenerators)
    GF1024.longGenerator (by decide) GF1024.long_step_bound
    (fun r v hr => step_poly_getD_g 15 (by decide) longLow rfl r _ v
      (GF1024.long_step_chunk r v hr)) vs r hr

private theorem zipWith_add_reverse' (c1 c2 : List Symbol) (hlen : c1.length = c2.length) :
    List.zipWith Field.add c1.reverse c2.reverse = (List.zipWith Field.add c1 c2).reverse := by
  induction c1 generalizing c2 with
  | nil => cases c2 <;> simp_all
  | cons a as ih =>
    cases c2 with
    | nil => simp at hlen
    | cons b bs =>
      have hlen' : as.length = bs.length := by simpa using hlen
      rw [List.reverse_cons, List.reverse_cons,
        List.zipWith_append (by rw [List.length_reverse, List.length_reverse, hlen']),
        List.zipWith_cons_cons, List.zipWith_cons_cons, List.reverse_cons, ih bs hlen']
      have hz : add a b :: List.zipWith Field.add [] [] = [add a b] := rfl
      rw [hz]

private theorem getD_zipWith_add_reverse (c1 c2 : List Symbol) (hlen : c1.length = c2.length)
    (i : Nat) :
    (List.zipWith Field.add c1 c2).reverse.getD i 0 =
      add (c1.reverse.getD i 0) (c2.reverse.getD i 0) := by
  rw [← zipWith_add_reverse' c1 c2 hlen, getD_zipWith_of_length _ _ _
    (by rw [List.length_reverse, List.length_reverse, hlen])]
  by_cases hi : i < c1.reverse.length
  · rw [ite_eq_left hi]
  · rw [ite_eq_right hi]
    rw [List.length_reverse] at hi
    have h1 : c1.reverse.getD i 0 = 0 :=
      Poly.getD_eq_zero_of_le _ _ (by rw [List.length_reverse]; omega)
    have h2 : c2.reverse.getD i 0 = 0 :=
      Poly.getD_eq_zero_of_le _ _ (by rw [List.length_reverse, ← hlen]; omega)
    rw [h1, h2, add_self]

private theorem getD_take (j : Nat) (p : List Symbol) (i : Nat) (h : i < j) :
    (p.take j).getD i 0 = p.getD i 0 := by
  rw [List.getD, List.getD, List.getElem?_take, ite_eq_left h]

/-- A checksum bridge with the same start register turns equal residues into
polynomial divisibility. -/
private theorem polymod_eq_divisible_g (width initial : Nat) (generator : List Symbol)
    (polymod : List Symbol → Nat)
    (hbridge : ∀ vs, ∃ T : List Symbol, T.length = vs.length ∧ ∀ i,
      (pAdd vs.reverse (pShift vs.length (unpack width initial))).getD i 0 =
        (pAdd (unpack width (polymod vs)) (pMul generator T)).getD i 0)
    (c1 c2 : List Symbol) (hlen : c1.length = c2.length) (hpoly : polymod c1 = polymod c2) :
    ∃ T : List Symbol, ∀ i,
      (List.zipWith Field.add c1 c2).reverse.getD i 0 = (pMul generator T).getD i 0 := by
  obtain ⟨T1, -, hT1⟩ := hbridge c1
  obtain ⟨T2, -, hT2⟩ := hbridge c2
  refine ⟨pAdd T1 T2, fun i => ?_⟩
  have hsum := congr (congrArg Field.add (hT1 i)) (hT2 i)
  simp only [getD_pAdd, hpoly, ← hlen] at hsum
  rw [add_pair, add_self, Field.add_zero, add_pair, add_self, Field.zero_add] at hsum
  rw [getD_zipWith_add_reverse c1 c2 hlen i, hsum, ← getD_pAdd, ← getD_pMul_add_right]

/-- A difference supported in a window no longer than the generator degree
vanishes whenever the generator divides it. -/
private theorem burst_g (generator : List Symbol) (degree : Nat)
    (hg0 : generator.getD 0 0 ≠ 0) (hg : generator.getD degree 0 = 1)
    (hzero : ∀ n > degree, generator.getD n 0 = 0)
    (c1 c2 : List Symbol) (hlen : c1.length = c2.length)
    (hdiv : ∃ T : List Symbol, ∀ i,
      (List.zipWith Field.add c1 c2).reverse.getD i 0 = (pMul generator T).getD i 0)
    (j w : Nat) (hw : w ≤ degree) (hjw : j + w ≤ c1.length)
    (hfront : c1.take j = c2.take j) (hback : c1.drop (j + w) = c2.drop (j + w)) :
    c1 = c2 := by
  obtain ⟨T, hT⟩ := hdiv
  have hlenz : (List.zipWith Field.add c1 c2).length = c1.length := by
    rw [List.length_zipWith, hlen, Nat.min_self]
  have hD : ∀ p, p < j ∨ j + w ≤ p → (List.zipWith Field.add c1 c2).getD p 0 = 0 := by
    intro p hp
    by_cases hp2 : p < c1.length
    · have heq : c1.getD p 0 = c2.getD p 0 := by
        rcases hp with hp | hp
        · have h1 : (c1.take j).getD p 0 = (c2.take j).getD p 0 := by rw [hfront]
          rwa [getD_take j c1 p hp, getD_take j c2 p hp] at h1
        · have h1 : (c1.drop (j + w)).getD (p - (j + w)) 0 =
              (c2.drop (j + w)).getD (p - (j + w)) 0 := by rw [hback]
          rw [getD_drop, getD_drop] at h1
          have h2 : j + w + (p - (j + w)) = p := by omega
          rwa [h2] at h1
      rw [getD_zipWith_of_length Field.add c1 c2 hlen p, ite_eq_left hp2, heq, add_self]
    · rw [getD_zipWith_of_length Field.add c1 c2 hlen p, ite_eq_right hp2]
  generalize hs_def : c1.length - (j + w) = s
  have hrev : ∀ e, e < s ∨ s + w ≤ e → (List.zipWith Field.add c1 c2).reverse.getD e 0 = 0 := by
    intro e he
    rw [getD_reverse]
    by_cases he2 : e < (List.zipWith Field.add c1 c2).length
    · rw [ite_eq_left he2]
      apply hD
      rw [hlenz] at he2
      rcases he with he | he
      · right; omega
      · left; omega
    · rw [ite_eq_right he2]
  have hTlow : ∀ i < s, T.getD i 0 = 0 := by
    apply entries_eq_zero_of_pMul_low_zero generator T hg0 s
    intro i hi
    rw [← hT i]
    exact hrev i (Or.inl hi)
  generalize hT'_def : T.drop s = T'
  have hTshift : ∀ i, T.getD i 0 = (pShift s T').getD i 0 := by
    intro i
    rw [getD_pShift]
    by_cases hi : i < s
    · rw [ite_eq_left hi, hTlow i hi]
    · rw [ite_eq_right hi, ← hT'_def, getD_drop]
      have h : s + (i - s) = i := by omega
      rw [h]
  have hmain : ∀ m ≥ w, (pMul generator T').getD m 0 = 0 := by
    intro m hm
    have h1 := hT (s + m)
    have h2 : (pMul generator T).getD (s + m) 0 =
        (pMul generator T').getD m 0 := by
      rw [getD_pMul_congr generator T (pShift s T') hTshift (s + m),
        getD_pMul_shift, getD_pShift, ite_eq_right (by omega : ¬ s + m < s)]
      have h3 : s + m - s = m := by omega
      rw [h3]
    rw [h2] at h1
    have h4 := hrev (s + m) (Or.inr (by omega))
    rw [h4] at h1
    exact h1.symm
  have hT'zero : ∀ i, T'.getD i 0 = 0 := by
    apply entries_eq_zero_of_pMul_high_zero generator T' degree hg hzero
    · intro m hm
      exact hmain m (by omega)
  have hDrev : ∀ e, (List.zipWith Field.add c1 c2).reverse.getD e 0 = 0 := by
    intro e
    rw [hT e, getD_pMul_congr generator T (pShift s T') hTshift,
      getD_pMul_shift, getD_pShift]
    by_cases he : e < s
    · rw [ite_eq_left he]
    · rw [ite_eq_right he, getD_pMul_of_entries_zero generator T' hT'zero]
  have hDzero : ∀ p, (List.zipWith Field.add c1 c2).getD p 0 = 0 := by
    intro p
    by_cases hp : p < (List.zipWith Field.add c1 c2).length
    · have h1 := hDrev ((List.zipWith Field.add c1 c2).length - 1 - p)
      have h2 : (List.zipWith Field.add c1 c2).getD p 0 =
          (List.zipWith Field.add c1 c2).reverse.getD
            ((List.zipWith Field.add c1 c2).length - 1 - p) 0 := by
        have hrev2 := getD_reverse (List.zipWith Field.add c1 c2).reverse p
        rw [List.reverse_reverse, List.length_reverse, ite_eq_left hp] at hrev2
        exact hrev2
      rw [h2]
      exact h1
    · exact Poly.getD_eq_zero_of_le _ _ (by omega)
  apply List.ext_getElem hlen
  intro i h1 h2
  have h3 := hDzero i
  rw [getD_zipWith_of_length Field.add c1 c2 hlen i, ite_eq_left h1,
    getD_eq_getElem c1 i h1, getD_eq_getElem c2 i (by omega)] at h3
  exact (Field.add_eq_zero _ _).mp h3

/-- Equal polymod residues make the generator divide the difference
polynomial: the register recurrence performs reduction modulo `g`. -/
theorem regular_polymod_eq_divisible (c1 c2 : List Symbol) (hlen : c1.length = c2.length)
    (hpoly : Checksum.regularPolymod c1 = Checksum.regularPolymod c2) :
    ∃ T : List Symbol, ∀ i,
      (List.zipWith Field.add c1 c2).reverse.getD i 0 =
        (pMul GF1024.regularGenerator T).getD i 0 := by
  exact polymod_eq_divisible_g 13 Checksum.initResidue GF1024.regularGenerator
    Checksum.regularPolymod (fun vs => regular_bridge vs Checksum.initResidue (by decide))
    c1 c2 hlen hpoly

/-- Burst-erasure uniqueness for the regular checksum: two equal-length
strings with equal polymod residues agreeing outside a consecutive window of
at most thirteen symbols are identical. -/
theorem regular_burst (c1 c2 : List Symbol) (hlen : c1.length = c2.length)
    (hpoly : Checksum.regularPolymod c1 = Checksum.regularPolymod c2)
    (j w : Nat) (hw : w ≤ 13) (hjw : j + w ≤ c1.length)
    (hfront : c1.take j = c2.take j) (hback : c1.drop (j + w) = c2.drop (j + w)) :
    c1 = c2 := by
  apply burst_g GF1024.regularGenerator 13 (by decide) (by decide)
    (fun n hn => Poly.getD_eq_zero_of_le _ n (by change 14 ≤ n; omega))
    c1 c2 hlen (regular_polymod_eq_divisible c1 c2 hlen hpoly) j w hw hjw hfront hback

/-- Burst uniqueness packaged for the executable regular verifier. -/
theorem regular_burst_valid (c1 c2 : List Symbol) (hlen : c1.length = c2.length)
    (_hbound : 5 + c1.length ≤ 93)
    (h1 : Checksum.verifyRegular c1 = true) (h2 : Checksum.verifyRegular c2 = true)
    (j w : Nat) (hw : w ≤ 13) (hjw : j + w ≤ c1.length)
    (hfront : c1.take j = c2.take j) (hback : c1.drop (j + w) = c2.drop (j + w)) :
    c1 = c2 := by
  simp only [Checksum.verifyRegular, Bool.and_eq_true, beq_iff_eq] at h1 h2
  exact regular_burst c1 c2 hlen (by rw [h1.2, h2.2]) j w hw hjw hfront hback


/-- Equal polymod residues make the generator divide the difference
polynomial: the register recurrence performs reduction modulo `g`. -/
theorem long_polymod_eq_divisible (c1 c2 : List Symbol) (hlen : c1.length = c2.length)
    (hpoly : Checksum.longPolymod c1 = Checksum.longPolymod c2) :
    ∃ T : List Symbol, ∀ i,
      (List.zipWith Field.add c1 c2).reverse.getD i 0 =
        (pMul GF1024.longGenerator T).getD i 0 := by
  exact polymod_eq_divisible_g 15 Checksum.initResidue GF1024.longGenerator
    Checksum.longPolymod (fun vs => long_bridge vs Checksum.initResidue (by decide))
    c1 c2 hlen hpoly

/-- Burst-erasure uniqueness for the long checksum: two equal-length
strings with equal polymod residues agreeing outside a consecutive window of
at most fifteen symbols are identical. -/
theorem long_burst (c1 c2 : List Symbol) (hlen : c1.length = c2.length)
    (hpoly : Checksum.longPolymod c1 = Checksum.longPolymod c2)
    (j w : Nat) (hw : w ≤ 15) (hjw : j + w ≤ c1.length)
    (hfront : c1.take j = c2.take j) (hback : c1.drop (j + w) = c2.drop (j + w)) :
    c1 = c2 := by
  apply burst_g GF1024.longGenerator 15 (by decide) (by decide)
    (fun n hn => Poly.getD_eq_zero_of_le _ n (by change 16 ≤ n; omega))
    c1 c2 hlen (long_polymod_eq_divisible c1 c2 hlen hpoly) j w hw hjw hfront hback

/-- Burst uniqueness packaged for the executable long verifier. -/
theorem long_burst_valid (c1 c2 : List Symbol) (hlen : c1.length = c2.length)
    (_hbound : 5 + c1.length ≤ 1023)
    (h1 : Checksum.verifyLong c1 = true) (h2 : Checksum.verifyLong c2 = true)
    (j w : Nat) (hw : w ≤ 15) (hjw : j + w ≤ c1.length)
    (hfront : c1.take j = c2.take j) (hback : c1.drop (j + w) = c2.drop (j + w)) :
    c1 = c2 := by
  simp only [Checksum.verifyLong, Bool.and_eq_true, beq_iff_eq] at h1 h2
  exact long_burst c1 c2 hlen (by rw [h1.2, h2.2]) j w hw hjw hfront hback

end Codex32
