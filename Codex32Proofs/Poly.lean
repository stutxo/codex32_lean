import Codex32Proofs.Field

/-!
GF(32) polynomials as coefficient lists, trailing-first (the head is the
constant coefficient). All reasoning is entrywise through `List.getD`, so no
normalization pass is needed: a polynomial is zero when every entry is zero.
The key results are the monic-product support theorem (the top nonzero entry
moves up by exactly the degree) and its corollaries used for the BCH
burst-erasure and checksum-counting theorems.
-/

namespace Codex32.Poly

open Field

set_option maxHeartbeats 0

instance : Std.Associative (α := Symbol) Field.add := ⟨Field.add_assoc⟩
instance : Std.Commutative (α := Symbol) Field.add := ⟨Field.add_comm⟩

@[simp] private theorem getD_nil (i : Nat) : ([] : List Symbol).getD i 0 = 0 := by
  cases i <;> rfl

/-- Padded pointwise addition of coefficient lists. -/
def pAdd : List Symbol → List Symbol → List Symbol
  | a :: as, b :: bs => add a b :: pAdd as bs
  | as, [] => as
  | [], bs => bs

@[simp] theorem pAdd_nil_left (p : List Symbol) : pAdd [] p = p := by
  cases p <;> rfl

@[simp] theorem pAdd_nil_right (p : List Symbol) : pAdd p [] = p := by
  cases p with
  | nil => rfl
  | cons a as => rfl

theorem pAdd_cons (a b : Symbol) (as bs : List Symbol) :
    pAdd (a :: as) (b :: bs) = add a b :: pAdd as bs := rfl

@[simp] theorem getD_pAdd (p q : List Symbol) (i : Nat) :
    (pAdd p q).getD i 0 = add (p.getD i 0) (q.getD i 0) := by
  induction p generalizing q i with
  | nil => simp [Field.zero_add]
  | cons a as ih =>
    cases q with
    | nil => simp [Field.add_zero]
    | cons b bs =>
      cases i with
      | zero => rfl
      | succ i => exact ih bs i

@[simp] theorem length_pAdd (p q : List Symbol) :
    (pAdd p q).length = max p.length q.length := by
  induction p generalizing q with
  | nil => simp
  | cons a as ih =>
    cases q with
    | nil => simp [pAdd]
    | cons b bs => simp only [pAdd_cons, List.length_cons, ih]; omega

theorem pAdd_comm (p q : List Symbol) : pAdd p q = pAdd q p := by
  induction p generalizing q with
  | nil => simp
  | cons a as ih =>
    cases q with
    | nil => simp
    | cons b bs => rw [pAdd_cons, pAdd_cons, add_comm a b, ih]

theorem pAdd_assoc (p q r : List Symbol) : pAdd (pAdd p q) r = pAdd p (pAdd q r) := by
  induction p generalizing q r with
  | nil => simp
  | cons a as ih =>
    cases q with
    | nil => simp
    | cons b bs =>
      cases r with
      | nil => simp
      | cons c cs => rw [pAdd_cons, pAdd_cons, pAdd_cons, pAdd_cons, add_assoc, ih]

@[simp] theorem getD_pAdd_self (p : List Symbol) (i : Nat) : (pAdd p p).getD i 0 = 0 := by
  rw [getD_pAdd, add_self]

theorem pAdd_singleton_zero_cons (a : Symbol) (as : List Symbol) :
    pAdd (a :: as) [0] = a :: as := by
  rw [pAdd_cons, Field.add_zero, pAdd_nil_right]

theorem pAdd_cons_zero (p q : List Symbol) :
    pAdd (0 :: p) (0 :: q) = 0 :: pAdd p q := by
  rw [pAdd_cons, Field.add_self]

/-- Scalar multiplication of every coefficient. -/
def pScale (c : Symbol) (p : List Symbol) : List Symbol := p.map (mul c)

theorem pScale_nil (c : Symbol) : pScale c [] = [] := rfl

theorem pScale_cons (c a : Symbol) (as : List Symbol) :
    pScale c (a :: as) = mul c a :: pScale c as := rfl

@[simp] theorem getD_pScale (c : Symbol) (p : List Symbol) (i : Nat) :
    (pScale c p).getD i 0 = mul c (p.getD i 0) := by
  induction p generalizing i with
  | nil => simp [pScale, Field.mul_zero]
  | cons a as ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

@[simp] theorem length_pScale (c : Symbol) (p : List Symbol) :
    (pScale c p).length = p.length := by
  simp [pScale]

@[simp] theorem getD_pScale_zero (p : List Symbol) (i : Nat) :
    (pScale 0 p).getD i 0 = 0 := by
  rw [getD_pScale, Field.zero_mul]

theorem pScale_add (c : Symbol) (p q : List Symbol) :
    pScale c (pAdd p q) = pAdd (pScale c p) (pScale c q) := by
  induction p generalizing q with
  | nil => simp [pScale]
  | cons a as ih =>
    cases q with
    | nil => simp [pScale]
    | cons b bs => rw [pAdd_cons, pScale_cons, pScale_cons, pScale_cons, pAdd_cons,
      mul_add, ih]

/-- Multiplication by `xⁿ`: prepend `n` zero coefficients. -/
def pShift (n : Nat) (p : List Symbol) : List Symbol := List.replicate n 0 ++ p

theorem pShift_zero (p : List Symbol) : pShift 0 p = p := rfl

theorem pShift_succ (n : Nat) (p : List Symbol) : pShift (n + 1) p = 0 :: pShift n p := by
  simp [pShift, List.replicate_succ]

@[simp] theorem length_pShift (n : Nat) (p : List Symbol) :
    (pShift n p).length = n + p.length := by
  simp [pShift]

@[simp] theorem getD_pShift (n : Nat) (p : List Symbol) (i : Nat) :
    (pShift n p).getD i 0 = if i < n then 0 else p.getD (i - n) 0 := by
  induction n generalizing i with
  | zero => simp [pShift]
  | succ n ih =>
    rw [pShift_succ]
    cases i with
    | zero => simp
    | succ i =>
      rw [List.getD_cons_succ, ih]
      by_cases h : i < n
      · rw [ite_eq_left h, ite_eq_left (by omega)]
      · rw [ite_eq_right h, ite_eq_right (by omega), Nat.succ_sub_succ]

theorem pAdd_pShift (n : Nat) (p q : List Symbol) :
    pAdd (pShift n p) (pShift n q) = pShift n (pAdd p q) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pShift_succ, pShift_succ, pShift_succ, pAdd_cons, ih, Field.add_self]

theorem pAdd_pShift_singleton (v : Symbol) (n : Nat) (p : List Symbol) (h : p.length = n) :
    pAdd p (pShift n [v]) = p ++ [v] := by
  induction p generalizing n with
  | nil =>
    cases n with
    | zero => rfl
    | succ n => simp at h
  | cons a as ih =>
    cases n with
    | zero => simp at h
    | succ n =>
      rw [pShift_succ, pAdd_cons, Field.add_zero, List.cons_append]
      rw [ih n (by simpa using h)]

/-- Full product by convolution, recursing on the right factor. -/
def pMul (g : List Symbol) : List Symbol → List Symbol
  | [] => []
  | c :: q => pAdd (pScale c g) (0 :: pMul g q)

theorem pMul_nil (g : List Symbol) : pMul g [] = [] := rfl

theorem pMul_cons_eq (g : List Symbol) (c : Symbol) (q : List Symbol) :
    pMul g (c :: q) = pAdd (pScale c g) (0 :: pMul g q) := rfl

/-- A pointwise-zero right factor gives a pointwise-zero product. -/
theorem getD_pMul_of_entries_zero (g q : List Symbol) (h : ∀ i, q.getD i 0 = 0) :
    ∀ i, (pMul g q).getD i 0 = 0 := by
  induction q with
  | nil => intro i; rfl
  | cons c qs ih =>
    intro i
    have hc : c = 0 := h 0
    rw [pMul_cons_eq, getD_pAdd, hc, getD_pScale_zero, Field.zero_add]
    cases i with
    | zero => rfl
    | succ i => exact ih (fun j => h (j + 1)) i

/-- Any list with a nonzero entry has a greatest nonzero index. -/
theorem exists_top (q : List Symbol) (h : ∃ j, q.getD j 0 ≠ 0) :
    ∃ i, q.getD i 0 ≠ 0 ∧ ∀ n > i, q.getD n 0 = 0 := by
  induction q with
  | nil => obtain ⟨j, hj⟩ := h; simp at hj
  | cons c qs ih =>
    by_cases hqs : ∃ j, qs.getD j 0 ≠ 0
    · obtain ⟨i, hi, habove⟩ := ih hqs
      refine ⟨i + 1, hi, fun n hn => ?_⟩
      cases n with
      | zero => omega
      | succ n => exact habove n (by omega)
    · have hz : ∀ j, qs.getD j 0 = 0 := by
        intro j
        apply Classical.byContradiction
        intro hn
        exact hqs ⟨j, hn⟩
      refine ⟨0, ?_, fun n hn => ?_⟩
      · obtain ⟨j, hj⟩ := h
        cases j with
        | zero => exact hj
        | succ j => exact absurd (hz j) hj
      · cases n with
        | zero => omega
        | succ n => exact hz n

/-- Multiplication by a monic degree-`d` polynomial moves the top nonzero
entry up by exactly `d` and leaves nothing above it. -/
theorem getD_pMul_top (g q : List Symbol) (d i : Nat)
    (hg : g.getD d 0 = 1) (hzero : ∀ n > d, g.getD n 0 = 0)
    (htop : q.getD i 0 ≠ 0) (habove : ∀ n > i, q.getD n 0 = 0) :
    (pMul g q).getD (d + i) 0 ≠ 0 ∧ ∀ n > d + i, (pMul g q).getD n 0 = 0 := by
  induction q generalizing i with
  | nil => exact absurd htop (by simp)
  | cons c qs ih =>
    by_cases hqs : ∃ j, qs.getD j 0 ≠ 0
    · have hi : i ≠ 0 := by
        intro hzero_i
        obtain ⟨j, hj⟩ := hqs
        have hjl : j + 1 > i := by omega
        have hthis := habove (j + 1) hjl
        simp only [List.getD_cons_succ] at hthis
        exact hj hthis
      have htop' : qs.getD (i - 1) 0 ≠ 0 := by
        have h1 : i = (i - 1) + 1 := by omega
        rw [h1] at htop
        simpa only [List.getD_cons_succ] using htop
      have habove' : ∀ n > i - 1, qs.getD n 0 = 0 := by
        intro n hn
        have h1 : i = (i - 1) + 1 := by omega
        have h2 := habove (n + 1) (by omega)
        simpa only [List.getD_cons_succ] using h2
      obtain ⟨h1, h2⟩ := ih (i - 1) htop' habove'
      have hdi : d + i = (d + (i - 1)) + 1 := by omega
      constructor
      · rw [hdi, pMul_cons_eq, getD_pAdd, List.getD_cons_succ]
        have hgone : g.getD (d + (i - 1) + 1) 0 = 0 := hzero _ (by omega)
        rw [getD_pScale, hgone, Field.mul_zero, Field.zero_add]
        have hsucc : d + (i - 1) = d + (i - 1) := rfl
        exact h1
      · intro n hn
        rw [pMul_cons_eq, getD_pAdd]
        have hgone : g.getD n 0 = 0 := hzero n (by omega)
        rw [getD_pScale, hgone, Field.mul_zero, Field.zero_add]
        cases n with
        | zero => omega
        | succ n =>
          rw [List.getD_cons_succ]
          exact h2 n (by omega)
    · have hz : ∀ j, qs.getD j 0 = 0 := by
        intro j
        apply Classical.byContradiction
        intro hn
        exact hqs ⟨j, hn⟩
      have hi0 : i = 0 := by
        cases i with
        | zero => rfl
        | succ i => exact absurd (hz i) (by simpa only [List.getD_cons_succ] using htop)
      subst hi0
      have hc : c ≠ 0 := by simpa using htop
      have hmul : ∀ j, (pMul g qs).getD j 0 = 0 := getD_pMul_of_entries_zero g qs hz
      constructor
      · rw [pMul_cons_eq, getD_pAdd, getD_pScale, Nat.add_zero, hg, Field.mul_one]
        cases d with
        | zero =>
          rw [List.getD_cons_zero, Field.add_zero]
          exact hc
        | succ d =>
          rw [List.getD_cons_succ, hmul, Field.add_zero]
          exact hc
      · intro n hn
        rw [pMul_cons_eq, getD_pAdd]
        have hgone : g.getD n 0 = 0 := hzero n (by omega)
        rw [getD_pScale, hgone, Field.mul_zero, Field.zero_add]
        cases n with
        | zero => omega
        | succ n =>
          rw [List.getD_cons_succ, hmul]

/-- A product with a monic degree-`d` polynomial that vanishes at every
position `≥ d` has a pointwise-zero right factor. -/
theorem entries_eq_zero_of_pMul_high_zero (g q : List Symbol) (d : Nat)
    (hg : g.getD d 0 = 1) (hzero : ∀ n > d, g.getD n 0 = 0)
    (h : ∀ n ≥ d, (pMul g q).getD n 0 = 0) : ∀ i, q.getD i 0 = 0 := by
  apply Classical.byContradiction
  intro hne
  have hne' : ∃ j, q.getD j 0 ≠ 0 := Classical.not_forall.mp hne
  obtain ⟨i, hi, habove⟩ := exists_top q hne'
  obtain ⟨h1, -⟩ := getD_pMul_top g q d i hg hzero hi habove
  exact h1 (h (d + i) (by omega))

/-- If the product with a polynomial having nonzero constant term vanishes
below `s`, so does the right factor. -/
theorem entries_eq_zero_of_pMul_low_zero (g q : List Symbol)
    (hg0 : g.getD 0 0 ≠ 0) (s : Nat)
    (h : ∀ i < s, (pMul g q).getD i 0 = 0) : ∀ i < s, q.getD i 0 = 0 := by
  induction s generalizing q with
  | zero => intro i hi; omega
  | succ s ih =>
    cases q with
    | nil => intro i hi; rfl
    | cons c qs =>
      have h0 : (pMul g (c :: qs)).getD 0 0 = 0 := h 0 (by omega)
      have hc : c = 0 := by
        rw [pMul_cons_eq, getD_pAdd, getD_pScale, List.getD_cons_zero,
          Field.add_zero] at h0
        rcases (Field.mul_eq_zero c (g.getD 0 0)).mp h0 with hcl | hcr
        · exact hcl
        · exact absurd hcr hg0
      intro i hi
      cases i with
      | zero => exact hc
      | succ i =>
        have hrest : ∀ j < s, (pMul g qs).getD j 0 = 0 := by
          intro j hj
          have h1 := h (j + 1) (by omega)
          rw [pMul_cons_eq, getD_pAdd, List.getD_cons_succ, hc, getD_pScale_zero,
            Field.zero_add] at h1
          exact h1
        exact ih qs hrest i (by omega)

/-- Shifting the right factor shifts the product. -/
theorem getD_pMul_shift (g : List Symbol) (n : Nat) (q : List Symbol) (i : Nat) :
    (pMul g (pShift n q)).getD i 0 = (pShift n (pMul g q)).getD i 0 := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    rw [pShift_succ, pShift_succ, pMul_cons_eq, getD_pAdd, getD_pScale, Field.zero_mul,
      Field.zero_add]
    cases i with
    | zero => rfl
    | succ i => rw [List.getD_cons_succ, List.getD_cons_succ]; exact ih i

/-- The snoc form of the convolution: appending one more coefficient. -/
theorem pMul_snoc (g : List Symbol) (hg : g ≠ []) (t : Symbol) (q : List Symbol) :
    pMul g (q ++ [t]) = pAdd (pMul g q) (pShift q.length (pScale t g)) := by
  induction q with
  | nil =>
    simp only [List.nil_append, pMul_cons_eq, pMul_nil, List.length_nil, pShift_zero,
      pAdd_nil_left]
    cases g with
    | nil => exact absurd rfl hg
    | cons b bs =>
      rw [pScale_cons]
      exact pAdd_singleton_zero_cons _ _
  | cons c qs ih =>
    rw [List.cons_append, pMul_cons_eq, pMul_cons_eq, ih, List.length_cons, pShift_succ]
    rw [show (0 :: pAdd (pMul g qs) (pShift qs.length (pScale t g))) =
        pAdd (0 :: pMul g qs) (0 :: pShift qs.length (pScale t g)) from
      (pAdd_cons_zero _ _).symm]
    rw [← pAdd_assoc]

/-- Two shifts compose into one. -/
theorem getD_pShift_shift (m n : Nat) (p : List Symbol) (i : Nat) :
    (pShift m (pShift n p)).getD i 0 = (pShift (m + n) p).getD i 0 := by
  have h1 : (pShift m (pShift n p)).getD i 0 =
      if i < m then 0 else (pShift n p).getD (i - m) 0 := getD_pShift m (pShift n p) i
  have h2 : (pShift (m + n) p).getD i 0 =
      if i < m + n then 0 else p.getD (i - (m + n)) 0 := getD_pShift (m + n) p i
  rw [h1, h2]
  by_cases h : i < m
  · rw [ite_eq_left h, ite_eq_left (by omega)]
  · rw [ite_eq_right h, getD_pShift]
    by_cases h3 : i - m < n
    · rw [ite_eq_left h3, ite_eq_left (by omega)]
    · rw [ite_eq_right h3, ite_eq_right (by omega)]
      have h4 : i - m - n = i - (m + n) := by omega
      rw [h4]

/-- Scalar multiplication by a sum splits. -/
theorem pScale_add_coe (a b : Symbol) (p : List Symbol) :
    pScale (add a b) p = pAdd (pScale a p) (pScale b p) := by
  induction p with
  | nil => rfl
  | cons c cs ih =>
    rw [pScale_cons, pScale_cons, pScale_cons, pAdd_cons, ih]
    have h : mul (add a b) c = add (mul a c) (mul b c) := by
      rw [mul_comm, mul_add, mul_comm b c, mul_comm a c]
    rw [h]

/-- A zero entry beyond the list length. -/
theorem getD_eq_zero_of_le (p : List Symbol) (i : Nat) (h : p.length ≤ i) :
    p.getD i 0 = 0 := by
  have hnone : p[i]? = none := List.getElem?_eq_none h
  simp [List.getD, hnone]

/-- The convolution is additive in the right factor. -/
theorem getD_pMul_add_right (g p q : List Symbol) (i : Nat) :
    (pMul g (pAdd p q)).getD i 0 = (pAdd (pMul g p) (pMul g q)).getD i 0 := by
  induction p generalizing q i with
  | nil => simp [pMul_nil]
  | cons a as ih =>
    cases q with
    | nil => simp [pMul_nil]
    | cons b bs =>
      simp only [pAdd_cons, pMul_cons_eq, getD_pAdd, getD_pScale, pScale_add_coe]
      cases i with
      | zero =>
        simp only [List.getD_cons_zero, Field.add_zero]
      | succ i =>
        rw [List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ, ih bs i,
          getD_pAdd]
        ac_rfl

/-- The convolution depends only on the entries of the right factor. -/
theorem getD_pMul_congr (g : List Symbol) (q1 q2 : List Symbol)
    (h : ∀ i, q1.getD i 0 = q2.getD i 0) :
    ∀ i, (pMul g q1).getD i 0 = (pMul g q2).getD i 0 := by
  induction q1 generalizing q2 with
  | nil =>
    intro i
    have hz : ∀ j, q2.getD j 0 = 0 := fun j => (h j).symm
    rw [pMul_nil, getD_nil]
    exact (getD_pMul_of_entries_zero g q2 hz i).symm
  | cons a as ih =>
    cases q2 with
    | nil =>
      intro i
      have hz : ∀ j, (a :: as).getD j 0 = 0 := fun j => h j
      rw [getD_pMul_of_entries_zero g (a :: as) hz i]
      rfl
    | cons b bs =>
      have hab : a = b := h 0
      intro i
      rw [pMul_cons_eq, pMul_cons_eq, getD_pAdd, getD_pAdd, getD_pScale, getD_pScale, hab]
      cases i with
      | zero => rfl
      | succ i =>
        rw [List.getD_cons_succ, List.getD_cons_succ]
        exact congrArg _ (ih bs (fun j => h (j + 1)) i)

end Codex32.Poly
