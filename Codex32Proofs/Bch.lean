import Codex32Proofs.GF1024
import Codex32.Checksum

set_option maxHeartbeats 0

/-!
The bridge between the executable polymod recurrences and the BCH codes of the
BIP 93 appendix, and the resulting error-detection theorems.

After evaluation at any `x : GF1024`, the register after one polymod step
equals `x·R + v + top·g`, and after `n` symbols it equals
`xⁿ·init + M + g·Q` for some `Q`. Equal-length valid strings therefore agree at
every root of `g`, and the BCH bound (`sparse_zero`) forces any equal-length pair of valid
strings differing in at most eight symbols to be identical. This is the BIP's
"guarantees detection of any error changing at most 8 symbols" claim, proved
rather than assumed. All finite generator/chunk calculations use the kernel's
`decide`. Shared lemmas handle register updates, the recurrence, and the BCH
bound; the regular and long theorems instantiate these with their concrete
constants and retain their existing interfaces.
-/

namespace Codex32

/-- The regular generating polynomial without its leading term, trailing-first. -/
def regularLow : List Symbol := [16, 16, 24, 27, 31, 25, 25, 25, 0, 8, 17, 27, 25]

/-- The long generating polynomial without its leading term, trailing-first. -/
def longLow : List Symbol := [23, 4, 22, 5, 6, 21, 23, 6, 21, 25, 9, 26, 25, 10, 15]

theorem regularGenerator_eq : GF1024.regularGenerator = regularLow ++ [1] := rfl

theorem longGenerator_eq : GF1024.longGenerator = longLow ++ [1] := rfl

/-- Read the polynomial of the register: chunk `i` is the coefficient of `xⁱ`. -/
def unpack (n : Nat) (r : Nat) : List Symbol :=
  (List.range n).map fun i => Symbol.ofNat ((r >>> (5 * i)) &&& 31)

/-- Chunk `j` of a generator constant is `xʲ` times the corresponding
coefficient of `g`; this is what makes the polymod step a polynomial reduction
modulo `g`. Both finite tables are kernel computations. -/
theorem regular_generator_chunks (i : Fin 5) (j : Fin 13) :
    Symbol.ofNat ((Checksum.regularGenerators[i.val]! >>> (5 * j.val)) &&& 31) =
      Field.mul (Symbol.ofNat (2 ^ i.val)) regularLow[j.val] := by
  decide +revert +kernel

theorem long_generator_chunks (i : Fin 5) (j : Fin 15) :
    Symbol.ofNat ((Checksum.longGenerators[i.val]! >>> (5 * j.val)) &&& 31) =
      Field.mul (Symbol.ofNat (2 ^ i.val)) longLow[j.val] := by
  decide +revert +kernel

/-- Field multiplication as a fold over the bits of the left operand, matching
the shape of the step's generator fold. Exhaustively kernel-checked. -/
theorem mul_eq_fold_bits (a b : Symbol) :
    Field.mul a b = ((List.range 5).foldl (fun s i =>
      if (a.val >>> i) &&& 1 == 1 then Field.add s (Field.mul (Symbol.ofNat (2 ^ i)) b) else s) 0) := by
  decide +revert +kernel

namespace GF1024

/-- The regular generator vanishes at every listed power of `β`. -/
theorem evalF_regularGenerator_zero (i : Nat) (h : i ∈ regularRoots) :
    evalF (pow beta i) regularGenerator = zero := by
  have hmem : pow beta i ∈ (regularRoots.map (pow beta)) :=
    List.mem_map.mpr ⟨i, h, rfl⟩
  have hzero := evalG_roots_product_zero (pow beta i) (regularRoots.map (pow beta)) hmem
  rw [regular_generator_rederived, evalG_map_embed] at hzero
  exact hzero

/-- The long generator vanishes at every listed power of `γ`. -/
theorem evalF_longGenerator_zero (i : Nat) (h : i ∈ longRoots) :
    evalF (pow gamma i) longGenerator = zero := by
  have hmem : pow gamma i ∈ (longRoots.map (pow gamma)) :=
    List.mem_map.mpr ⟨i, h, rfl⟩
  have hzero := evalG_roots_product_zero (pow gamma i) (longRoots.map (pow gamma)) hmem
  rw [long_generator_rederived, evalG_map_embed] at hzero
  exact hzero

theorem beta_inj_below {a b : Nat} (ha : a < 93) (hb : b < 93)
    (h : pow beta a = pow beta b) : a = b :=
  pow_inj beta 93 (by decide) beta_pow_period beta_proper_divisor beta_ne_zero ha hb h

theorem gamma_inj_below {a b : Nat} (ha : a < 1023) (hb : b < 1023)
    (h : pow gamma a = pow gamma b) : a = b :=
  pow_inj gamma 1023 (by decide) gamma_pow_period gamma_proper_divisor gamma_ne_zero ha hb h

theorem evalF_append (x : GF1024) (p q : List Symbol) :
    evalF x (p ++ q) = add (evalF x p) (mul (pow x p.length) (evalF x q)) := by
  induction p with
  | nil => simp [evalF, pow_zero, one_mul]
  | cons c cs ih =>
    simp only [List.cons_append, evalF_cons, ih, List.length_cons, pow_succ]
    rw [mul_add, mul_left_comm x (pow x cs.length) (evalF x q), mul_assoc, add_assoc]

theorem evalF_zipAdd (x : GF1024) (p q : List Symbol) (h : p.length = q.length) :
    evalF x (p.zipWith Field.add q) = add (evalF x p) (evalF x q) := by
  induction p generalizing q with
  | nil => cases q with
    | nil => simp [evalF]
    | cons => simp at h
  | cons c cs ih =>
    cases q with
    | nil => simp at h
    | cons d ds =>
      simp only [List.zipWith_cons_cons, evalF_cons, List.length_cons] at *
      rw [ih ds (by omega), embed_add, mul_add]
      ac_rfl

theorem evalF_map_scalar (x : GF1024) (p : List Symbol) (t : Symbol) :
    evalF x (p.map (Field.mul t)) = mul (embed t) (evalF x p) := by
  induction p with
  | nil => simp [evalF, mul_zero]
  | cons c cs ih =>
    simp only [List.map_cons, evalF_cons, ih, embed_mul, mul_add, mul_left_comm]

/-- Chunking respects XOR: the `j`-th chunk of a bitwise XOR is the field sum
of the chunks. -/
private theorem chunk_xor (a b : Nat) (j : Nat) :
    Symbol.ofNat (((a ^^^ b) >>> (5 * j)) &&& 31) =
      Field.add (Symbol.ofNat ((a >>> (5 * j)) &&& 31)) (Symbol.ofNat ((b >>> (5 * j)) &&& 31)) := by
  have h31 : (31 : Nat) = 2 ^ 5 - 1 := by decide
  have hval : ∀ x : Nat, (Symbol.ofNat ((x >>> (5 * j)) &&& 31)).val = (x >>> (5 * j)) &&& 31 := by
    intro x
    simp only [Symbol.ofNat]
    exact Nat.mod_eq_of_lt (Nat.and_lt_two_pow _ (show (31 : Nat) < 2 ^ 5 by decide))
  have hxor : ∀ x y : Symbol, (Field.add x y).val = x.val ^^^ y.val := by
    intro x y
    simp only [Field.add, Symbol.ofNat]
    exact Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (n := 5) x.isLt y.isLt)
  apply Fin.ext
  rw [hval, hxor, hval, hval]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_xor, Nat.testBit_xor,
    Nat.testBit_and, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_shiftRight,
    h31, Nat.testBit_two_pow_sub_one]
  by_cases h : i < 5 <;> simp [h]

/-- The chunk of a left-shifted register: zero at `j = 0`, the previous chunk
otherwise. -/
private theorem chunk_shiftLeft (x : Nat) (j : Nat) :
    Symbol.ofNat (((x <<< 5) >>> (5 * j)) &&& 31) =
      if j = 0 then 0 else Symbol.ofNat ((x >>> (5 * (j - 1))) &&& 31) := by
  have h31 : (31 : Nat) = 2 ^ 5 - 1 := by decide
  by_cases hj0 : j = 0
  · subst hj0
    simp only [Nat.mul_zero, Nat.shiftRight_zero, ite_true]
    apply Fin.ext
    have hb : (x <<< 5) &&& 31 = 0 := by
      apply Nat.eq_of_testBit_eq
      intro i
      by_cases hi : i < 5
      · rw [Nat.testBit_and, Nat.testBit_shiftLeft, h31, Nat.testBit_two_pow_sub_one]
        simp only [hi, decide_true, Bool.and_true]
        have h5 : ¬(5 ≤ i) := by omega
        simp [h5]
      · have hi5 : 5 ≤ i := by omega
        rw [Nat.testBit_and, h31, Nat.testBit_two_pow_sub_one]
        simp [hi5]
    rw [hb]
    rfl
  · simp only [hj0, ite_false]
    apply Fin.ext
    have hb : ((x <<< 5) >>> (5 * j)) &&& 31 = (x >>> (5 * (j - 1))) &&& 31 := by
      apply Nat.eq_of_testBit_eq
      intro i
      by_cases hi : i < 5
      · rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_shiftLeft,
          Nat.testBit_and, Nat.testBit_shiftRight, h31, Nat.testBit_two_pow_sub_one]
        simp only [hi, decide_true, Bool.and_true]
        have h5 : 5 ≤ 5 * j + i := by omega
        simp only [h5, decide_true, Bool.true_and]
        have he : 5 * j + i - 5 = 5 * (j - 1) + i := by omega
        rw [he]
      · have hi5 : 5 ≤ i := by omega
        rw [Nat.testBit_and, Nat.testBit_and, h31, Nat.testBit_two_pow_sub_one]
        simp [hi]
    rw [hb]

/-- Chunks of a value symbol vanish above position zero. -/
private theorem chunk_val (v : Symbol) (j : Nat) :
    Symbol.ofNat ((v.val >>> (5 * j)) &&& 31) = if j = 0 then v else 0 := by
  by_cases hj0 : j = 0
  · subst hj0
    simp only [Nat.mul_zero, Nat.shiftRight_zero, ite_true]
    apply Fin.ext
    have hb : v.val &&& 31 = v.val := by
      rw [show (31 : Nat) = 2 ^ 5 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod,
        Nat.mod_eq_of_lt v.isLt]
    rw [hb]
    exact Nat.mod_eq_of_lt v.isLt
  · simp only [hj0, ite_false]
    apply Fin.ext
    have hb : (v.val >>> (5 * j)) &&& 31 = 0 := by
      have h0 : v.val >>> (5 * j) = 0 := by
        rw [Nat.shiftRight_eq_div_pow]
        apply Nat.div_eq_of_lt
        have h32 : v.val < 32 := v.isLt
        have hj1 : 1 ≤ j := by omega
        calc v.val < 32 := h32
          _ = 2 ^ 5 := by decide
          _ ≤ 2 ^ (5 * j) := Nat.pow_le_pow_right (by decide) (by omega)
      rw [h0]
      rfl
    rw [hb]
    rfl

/-- The chunk of a fold of conditional XORs equals the conditional fold of the
chunks. -/
private theorem chunk_fold (top : Nat) (j : Nat) (l : List (Nat × Nat)) (next : Nat) :
    Symbol.ofNat (((l.foldl (fun acc p =>
        if ((top >>> p.2) &&& 1 == 1) then acc ^^^ p.1 else acc) next) >>> (5 * j)) &&& 31) =
      l.foldl (fun s p =>
        if ((top >>> p.2) &&& 1 == 1) then Field.add s (Symbol.ofNat ((p.1 >>> (5 * j)) &&& 31)) else s)
        (Symbol.ofNat ((next >>> (5 * j)) &&& 31)) := by
  induction l generalizing next with
  | nil => rfl
  | cons p ps ih =>
    rw [List.foldl_cons]
    show Symbol.ofNat ((List.foldl (fun acc p =>
          if (top >>> p.snd &&& 1 == 1) = true then acc ^^^ p.fst else acc)
          (if (top >>> p.snd &&& 1 == 1) = true then next ^^^ p.fst else next) ps >>> (5 * j)) &&& 31) =
        List.foldl (fun s p =>
          if (top >>> p.snd &&& 1 == 1) = true then
            Field.add s (Symbol.ofNat ((p.fst >>> (5 * j)) &&& 31)) else s)
          (if (top >>> p.snd &&& 1 == 1) = true then
            Field.add (Symbol.ofNat ((next >>> (5 * j)) &&& 31))
              (Symbol.ofNat ((p.fst >>> (5 * j)) &&& 31))
          else (Symbol.ofNat ((next >>> (5 * j)) &&& 31))) ps
    split
    · rename_i hc
      rw [ih, chunk_xor]
    · rename_i hc
      rw [ih]

/-- The five regular generator constants, chunked at position `j`, equal the
corresponding powers of `x` times the generator coefficients. Each is a finite
kernel calculation. -/
theorem regular_chunk_0 (j : Fin 13) :
    Symbol.ofNat ((0x19dc500ce73fde210 >>> (5 * j.val)) &&& 31) = Field.mul (Symbol.ofNat (2 ^ 0)) (regularLow.getD j.val 0) := by
  decide +revert +kernel

theorem regular_chunk_1 (j : Fin 13) :
    Symbol.ofNat ((0x1bfae00def77fe529 >>> (5 * j.val)) &&& 31) = Field.mul (Symbol.ofNat (2 ^ 1)) (regularLow.getD j.val 0) := by
  decide +revert +kernel

theorem regular_chunk_2 (j : Fin 13) :
    Symbol.ofNat ((0x1fbd920fffe7bee52 >>> (5 * j.val)) &&& 31) = Field.mul (Symbol.ofNat (2 ^ 2)) (regularLow.getD j.val 0) := by
  decide +revert +kernel

theorem regular_chunk_3 (j : Fin 13) :
    Symbol.ofNat ((0x1739640bdeee3fdad >>> (5 * j.val)) &&& 31) = Field.mul (Symbol.ofNat (2 ^ 3)) (regularLow.getD j.val 0) := by
  decide +revert +kernel

theorem regular_chunk_4 (j : Fin 13) :
    Symbol.ofNat ((0x07729a039cfc75f5a >>> (5 * j.val)) &&& 31) = Field.mul (Symbol.ofNat (2 ^ 4)) (regularLow.getD j.val 0) := by
  decide +revert +kernel

/-- The five long generator constants, chunked. -/
theorem long_chunk_0 (j : Fin 15) :
    Symbol.ofNat ((0x3d59d273535ea62d897 >>> (5 * j.val)) &&& 31) = Field.mul (Symbol.ofNat (2 ^ 0)) (longLow.getD j.val 0) := by
  decide +revert +kernel

theorem long_chunk_1 (j : Fin 15) :
    Symbol.ofNat ((0x7a9becb6361c6c51507 >>> (5 * j.val)) &&& 31) = Field.mul (Symbol.ofNat (2 ^ 1)) (longLow.getD j.val 0) := by
  decide +revert +kernel

theorem long_chunk_2 (j : Fin 15) :
    Symbol.ofNat ((0x543f9b7e6c38d8a2a0e >>> (5 * j.val)) &&& 31) = Field.mul (Symbol.ofNat (2 ^ 2)) (longLow.getD j.val 0) := by
  decide +revert +kernel

theorem long_chunk_3 (j : Fin 15) :
    Symbol.ofNat ((0x0c577eaeccf1990d13c >>> (5 * j.val)) &&& 31) = Field.mul (Symbol.ofNat (2 ^ 3)) (longLow.getD j.val 0) := by
  decide +revert +kernel

theorem long_chunk_4 (j : Fin 15) :
    Symbol.ofNat ((0x1887f74f8dc71b10651 >>> (5 * j.val)) &&& 31) = Field.mul (Symbol.ofNat (2 ^ 4)) (longLow.getD j.val 0) := by
  decide +revert +kernel


/-- The mask-chunk lemma, generic over the shift width: mask-covered chunks
agree with the register. -/
private theorem chunk_mask_g (shift : Nat) (r : Nat) (j : Nat) (hj : 5 * j + 4 < shift) :
    Symbol.ofNat (((r &&& (2 ^ shift - 1)) >>> (5 * j)) &&& 31) =
      Symbol.ofNat ((r >>> (5 * j)) &&& 31) := by
  have h31 : (31 : Nat) = 2 ^ 5 - 1 := by decide
  apply Fin.ext
  have hb : ((r &&& (2 ^ shift - 1)) >>> (5 * j)) &&& 31 = (r >>> (5 * j)) &&& 31 := by
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < 5
    · rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_and, Nat.testBit_and,
        Nat.testBit_shiftRight, h31, Nat.testBit_two_pow_sub_one]
      have hk : 5 * j + i < shift := by omega
      rw [Nat.testBit_two_pow_sub_one,
        show decide (5 * j + i < shift) = true from by simp [hk],
        show decide (i < 5) = true from by simp [hi]]
      simp
    · have hi5 : 5 ≤ i := by omega
      rw [Nat.testBit_and, Nat.testBit_and, h31, Nat.testBit_two_pow_sub_one]
      simp [hi]
  rw [hb]

/-- The `next` chunk, generic over the shift width. -/
private theorem next_chunk_g (shift : Nat) (r : Nat) (v : Symbol) (j : Nat) (hj : j ≠ 0 → 5 * (j - 1) + 4 < shift) :
    Symbol.ofNat (((((r &&& (2 ^ shift - 1)) <<< 5) ^^^ v.val) >>> (5 * j)) &&& 31) =
      if j = 0 then v else Symbol.ofNat ((r >>> (5 * (j - 1))) &&& 31) := by
  rw [chunk_xor, chunk_shiftLeft, chunk_val]
  by_cases hj0 : j = 0
  · subst hj0
    simp [Field.zero_add]
  · have hj1 : 1 ≤ j := by omega
    simp only [hj0, ite_false]
    rw [Field.add_zero, chunk_mask_g shift r (j - 1) (hj hj0)]

/-- A bound on the shifted-out top of the register, generic over the shift. -/
private theorem top_lt_g (shift : Nat) (r : Nat) (hr : r < 2 ^ (shift + 5)) : r >>> shift < 32 := by
  rw [Nat.shiftRight_eq_div_pow]
  have h : 2 ^ (shift + 5) = 2 ^ shift * 32 := by rw [Nat.pow_add]
  rw [h] at hr
  exact Nat.div_lt_of_lt_mul hr

/-- The top symbol of the register, as a field element. -/
private theorem top_val_g (shift : Nat) (r : Nat) (hr : r < 2 ^ (shift + 5)) :
    (Symbol.ofNat (r >>> shift)).val = r >>> shift := by
  simp only [Symbol.ofNat]
  exact Nat.mod_eq_of_lt (top_lt_g shift r hr)

/-- `foldl` from a nonzero starting accumulator splits off the start. -/
private theorem foldl_add_start (l : List α) (g : α → GF1024) (S : GF1024) :
    l.foldl (fun s p => add s (g p)) S = add S (l.foldl (fun s p => add s (g p)) zero) := by
  induction l generalizing S with
  | nil => simp [add_zero]
  | cons p ps ih =>
    simp only [List.foldl_cons]
    rw [ih (add S (g p)), ih (add zero (g p)), zero_add, add_assoc]

/-- The conditional-add form of the generator fold. -/
private theorem foldl_add_start' (l : List (Nat × Nat)) (c : Nat × Nat → Bool) (f : Nat × Nat → Symbol)
    (S : Symbol) :
    l.foldl (fun s p => if c p then Field.add s (f p) else s) S =
      Field.add S (l.foldl (fun s p => if c p then Field.add s (f p) else s) 0) := by
  induction l generalizing S with
  | nil => simp [Field.add_zero]
  | cons p ps ih =>
    rw [List.foldl_cons, List.foldl_cons]
    by_cases hc : c p = true
    · rw [ite_eq_left hc, ite_eq_left hc, ih (Field.add S (f p)), ih (Field.add 0 (f p)),
      Field.zero_add, Field.add_assoc]
    · rw [ite_eq_right hc, ite_eq_right hc, ih S, ih 0, Field.zero_add]

/-- The chunk form of a step, generic over the shift width, the generator
constants, and the low generator polynomial. The five chunk hypotheses pin
each generator constant to its `xⁱ` multiple of `g`. -/
theorem step_chunk (shift : Nat) (g0 g1 g2 g3 g4 : Nat) (low : List Symbol)
    (h0 : ∀ j : Nat, Symbol.ofNat ((g0 >>> (5 * j)) &&& 31) = Field.mul (Symbol.ofNat (2 ^ 0)) (low.getD j 0))
    (h1 : ∀ j : Nat, Symbol.ofNat ((g1 >>> (5 * j)) &&& 31) = Field.mul (Symbol.ofNat (2 ^ 1)) (low.getD j 0))
    (h2 : ∀ j : Nat, Symbol.ofNat ((g2 >>> (5 * j)) &&& 31) = Field.mul (Symbol.ofNat (2 ^ 2)) (low.getD j 0))
    (h3 : ∀ j : Nat, Symbol.ofNat ((g3 >>> (5 * j)) &&& 31) = Field.mul (Symbol.ofNat (2 ^ 3)) (low.getD j 0))
    (h4 : ∀ j : Nat, Symbol.ofNat ((g4 >>> (5 * j)) &&& 31) = Field.mul (Symbol.ofNat (2 ^ 4)) (low.getD j 0))
    (r : Nat) (v : Symbol) (hr : r < 2 ^ (shift + 5)) (j : Nat) (hj : j ≠ 0 → 5 * (j - 1) + 4 < shift) :
    Symbol.ofNat ((Checksum.step shift (2 ^ shift - 1) [g0, g1, g2, g3, g4] r v >>> (5 * j)) &&& 31) =
      Field.add (if j = 0 then v else Symbol.ofNat ((r >>> (5 * (j - 1))) &&& 31))
        (Field.mul (Symbol.ofNat (r >>> shift)) (low.getD j 0)) := by
  unfold Checksum.step
  rw [chunk_fold, next_chunk_g shift r v j hj, mul_eq_fold_bits,
    show List.range 5 = [0, 1, 2, 3, 4] from by decide, top_val_g shift r hr,
    foldl_add_start']
  simp only [List.zipIdx, List.foldl_cons, List.foldl_nil]
  rw [h0 j, h1 j, h2 j, h3 j, h4 j]

/-- Extend a finite generator-chunk identity to all positions. Both the
constant and the low polynomial vanish beyond the register width. -/
private theorem chunk_all (n i g : Nat) (low : List Symbol) (hlen : low.length = n)
    (hg : g < 2 ^ (5 * n))
    (hchunk : ∀ j : Fin n, Symbol.ofNat ((g >>> (5 * j.val)) &&& 31) =
      Field.mul (Symbol.ofNat (2 ^ i)) (low.getD j.val 0)) (j : Nat) :
    Symbol.ofNat ((g >>> (5 * j)) &&& 31) =
      Field.mul (Symbol.ofNat (2 ^ i)) (low.getD j 0) := by
  by_cases hj : j < n
  · exact hchunk ⟨j, hj⟩
  · have hzero : g >>> (5 * j) = 0 := by
      rw [Nat.shiftRight_eq_div_pow]
      apply Nat.div_eq_of_lt
      exact Nat.lt_of_lt_of_le hg (Nat.pow_le_pow_right (by decide) (by omega))
    have hnone : low[j]? = none := by
      rw [List.getElem?_eq_none]
      omega
    simp [hzero, List.getD, hnone, Field.mul_zero, Symbol.ofNat]

/-- The regular generator constants as literal arguments. -/
theorem regular_step_chunk (r : Nat) (v : Symbol) (hr : r < 2 ^ 65) (j : Fin 13) :
    Symbol.ofNat ((Checksum.step 60 0x0fffffffffffffff Checksum.regularGenerators r v >>> (5 * j.val)) &&& 31) =
      Field.add (if j.val = 0 then v else Symbol.ofNat ((r >>> (5 * (j.val - 1))) &&& 31))
        (Field.mul (Symbol.ofNat (r >>> 60)) regularLow[j.val]) := by
  have hmask : (0x0fffffffffffffff : Nat) = 2 ^ 60 - 1 := by decide
  have hgens : Checksum.regularGenerators =
      [0x19dc500ce73fde210, 0x1bfae00def77fe529, 0x1fbd920fffe7bee52,
       0x1739640bdeee3fdad, 0x07729a039cfc75f5a] := by decide
  have hj : j.val ≠ 0 → 5 * (j.val - 1) + 4 < 60 := by
    intro h
    have := j.isLt
    omega
  have h := step_chunk 60 0x19dc500ce73fde210 0x1bfae00def77fe529 0x1fbd920fffe7bee52
    0x1739640bdeee3fdad 0x07729a039cfc75f5a regularLow
    (chunk_all 13 0 0x19dc500ce73fde210 regularLow rfl (by decide) regular_chunk_0)
    (chunk_all 13 1 0x1bfae00def77fe529 regularLow rfl (by decide) regular_chunk_1)
    (chunk_all 13 2 0x1fbd920fffe7bee52 regularLow rfl (by decide) regular_chunk_2)
    (chunk_all 13 3 0x1739640bdeee3fdad regularLow rfl (by decide) regular_chunk_3)
    (chunk_all 13 4 0x07729a039cfc75f5a regularLow rfl (by decide) regular_chunk_4)
    r v (by rw [hmask] at *; exact hr) j.val hj
  rw [hmask, hgens]
  have hget : regularLow.getD j.val 0 = regularLow[j.val] := by
    simp only [List.getD, List.getElem?_eq_getElem (l := regularLow) j.isLt, Option.getD_some]
    rfl
  rw [hget] at h
  exact h

/-- The long step chunk, instantiated. -/
theorem long_step_chunk (r : Nat) (v : Symbol) (hr : r < 2 ^ 75) (j : Fin 15) :
    Symbol.ofNat ((Checksum.step 70 0x3fffffffffffffffff Checksum.longGenerators r v >>> (5 * j.val)) &&& 31) =
      Field.add (if j.val = 0 then v else Symbol.ofNat ((r >>> (5 * (j.val - 1))) &&& 31))
        (Field.mul (Symbol.ofNat (r >>> 70)) longLow[j.val]) := by
  have hmask : (0x3fffffffffffffffff : Nat) = 2 ^ 70 - 1 := by decide
  have hgens : Checksum.longGenerators =
      [0x3d59d273535ea62d897, 0x7a9becb6361c6c51507, 0x543f9b7e6c38d8a2a0e,
       0x0c577eaeccf1990d13c, 0x1887f74f8dc71b10651] := by decide
  have hj : j.val ≠ 0 → 5 * (j.val - 1) + 4 < 70 := by
    intro h
    have := j.isLt
    omega
  have h := step_chunk 70 0x3d59d273535ea62d897 0x7a9becb6361c6c51507 0x543f9b7e6c38d8a2a0e
    0x0c577eaeccf1990d13c 0x1887f74f8dc71b10651 longLow
    (chunk_all 15 0 0x3d59d273535ea62d897 longLow rfl (by decide) long_chunk_0)
    (chunk_all 15 1 0x7a9becb6361c6c51507 longLow rfl (by decide) long_chunk_1)
    (chunk_all 15 2 0x543f9b7e6c38d8a2a0e longLow rfl (by decide) long_chunk_2)
    (chunk_all 15 3 0x0c577eaeccf1990d13c longLow rfl (by decide) long_chunk_3)
    (chunk_all 15 4 0x1887f74f8dc71b10651 longLow rfl (by decide) long_chunk_4)
    r v (by rw [hmask] at *; exact hr) j.val hj
  rw [hmask, hgens]
  have hget : longLow.getD j.val 0 = longLow[j.val] := by
    simp only [List.getD, List.getElem?_eq_getElem (l := longLow) j.isLt, Option.getD_some]
    rfl
  rw [hget] at h
  exact h

/-- A masked shift and bounded generator XORs preserve the register width. -/
private theorem step_bound (shift mask : Nat) (gens : List Nat)
    (hmask : mask < 2 ^ shift) (hgens : ∀ g ∈ gens, g < 2 ^ (shift + 5))
    (r : Nat) (v : Symbol) :
    Checksum.step shift mask gens r v < 2 ^ (shift + 5) := by
  have hshift : (r &&& mask) <<< 5 < 2 ^ (shift + 5) := by
    rw [Nat.shiftLeft_eq, Nat.pow_add]
    exact Nat.mul_lt_mul_of_pos_right (Nat.lt_of_le_of_lt Nat.and_le_right hmask)
      (by decide : 0 < 2 ^ 5)
  have hv : v.val < 2 ^ (shift + 5) :=
    Nat.lt_of_lt_of_le (show v.val < 2 ^ 5 from v.isLt) (Nat.pow_le_pow_right (by decide) (by omega))
  have hfold : ∀ (l : List (Nat × Nat)) (init : Nat), init < 2 ^ (shift + 5) →
      (∀ p ∈ l, p.1 < 2 ^ (shift + 5)) →
      l.foldl (fun acc p => if ((r >>> shift >>> p.2) &&& 1 == 1) then acc ^^^ p.1 else acc)
        init < 2 ^ (shift + 5) := by
    intro l
    induction l with
    | nil => intro init hi _; exact hi
    | cons p ps ih =>
      intro init hi hmem
      rw [List.foldl_cons]
      apply ih
      · split
        · exact Nat.xor_lt_two_pow hi (hmem p (by simp))
        · exact hi
      · intro q hq
        exact hmem q (by simp [hq])
  unfold Checksum.step
  apply hfold _ _ (Nat.xor_lt_two_pow hshift hv)
  intro p hp
  obtain ⟨_, _, heq⟩ := List.mem_zipIdx hp
  rw [heq]
  exact hgens _ (List.getElem_mem _)

/-- The step map stays within its register. -/
theorem regular_step_bound (r : Nat) (v : Symbol) :
    Checksum.step 60 0x0fffffffffffffff Checksum.regularGenerators r v < 2 ^ 65 :=
  step_bound 60 _ _ (by decide) (by decide) r v

/-- The long step map stays within its register. -/
theorem long_step_bound (r : Nat) (v : Symbol) :
    Checksum.step 70 0x3fffffffffffffffff Checksum.longGenerators r v < 2 ^ 75 :=
  step_bound 70 _ _ (by decide) (by decide) r v

/-- Assemble a register update from its chunk identities. -/
private theorem step_unpack (n shift next r : Nat) (v : Symbol) (low : List Symbol)
    (hlen : low.length = n + 1)
    (hchunk : ∀ j : Fin (n + 1),
      Symbol.ofNat ((next >>> (5 * j.val)) &&& 31) =
        Field.add (if j.val = 0 then v else Symbol.ofNat ((r >>> (5 * (j.val - 1))) &&& 31))
          (Field.mul (Symbol.ofNat (r >>> shift)) (low.getD j.val 0))) :
    unpack (n + 1) next = List.zipWith Field.add (v :: (unpack (n + 1) r).take n)
      (low.map (Field.mul (Symbol.ofNat (r >>> shift)))) := by
  apply List.ext_getElem
  · simp [unpack, hlen]
  · intro j h1 h2
    have hj : j < n + 1 := by simpa [unpack] using h1
    have hc := hchunk ⟨j, hj⟩
    have hget : low.getD j 0 = low[j]'(by omega) := by
      simp [List.getD, List.getElem?_eq_getElem (by omega : j < low.length)]
    rw [hget] at hc
    cases j with
    | zero =>
      simp only [unpack, List.getElem_map, List.getElem_range, List.getElem_zipWith,
        List.getElem_cons_zero]
      simpa using hc
    | succ j =>
      simp only [unpack, List.getElem_map, List.getElem_range, List.getElem_zipWith,
        List.getElem_cons_succ, List.getElem_take]
      simpa using hc

/-- The list form of one regular step: the register after the step is the
shifted register XOR the top symbol times the low generator polynomial. -/
theorem regular_step_unpack (r : Nat) (v : Symbol) (hr : r < 2 ^ 65) :
    unpack 13 (Checksum.step 60 0x0fffffffffffffff Checksum.regularGenerators r v) =
      List.zipWith Field.add (v :: (unpack 13 r).take 12)
        (regularLow.map (Field.mul (Symbol.ofNat (r >>> 60)))) := by
  apply step_unpack 12 60 _ r v regularLow rfl
  intro j
  have hget : regularLow.getD j.val 0 = regularLow[j.val] := by
    simp only [List.getD, List.getElem?_eq_getElem (l := regularLow) j.isLt, Option.getD_some]
    rfl
  rw [hget]
  exact regular_step_chunk r v hr j

/-- The list form of one long step. -/
theorem long_step_unpack (r : Nat) (v : Symbol) (hr : r < 2 ^ 75) :
    unpack 15 (Checksum.step 70 0x3fffffffffffffffff Checksum.longGenerators r v) =
      List.zipWith Field.add (v :: (unpack 15 r).take 14)
        (longLow.map (Field.mul (Symbol.ofNat (r >>> 70)))) := by
  apply step_unpack 14 70 _ r v longLow rfl
  intro j
  have hget : longLow.getD j.val 0 = longLow[j.val] := by
    simp only [List.getD, List.getElem?_eq_getElem (l := longLow) j.isLt, Option.getD_some]
    rfl
  rw [hget]
  exact long_step_chunk r v hr j

/-- Evaluate a register update using its shifted-register decomposition and a
monic generator. The final chunk supplies the generator's leading term. -/
private theorem step_eval (n next r : Nat) (v : Symbol) (low : List Symbol)
    (hlen : low.length = n + 1) (hr : r < 2 ^ (5 * n + 5))
    (hstep : unpack (n + 1) next =
      List.zipWith Field.add (v :: (unpack (n + 1) r).take n)
        (low.map (Field.mul (Symbol.ofNat (r >>> (5 * n)))))) (x : GF1024) :
    evalF x (unpack (n + 1) next) =
      add (add (mul x (evalF x (unpack (n + 1) r))) (embed v))
        (mul (embed (Symbol.ofNat (r >>> (5 * n)))) (evalF x (low ++ [1]))) := by
  have hzip : (v :: (unpack (n + 1) r).take n).length =
      (low.map (Field.mul (Symbol.ofNat (r >>> (5 * n))))).length := by
    simp [unpack, hlen]
  have heval : evalF x (unpack (n + 1) r) =
      add (evalF x ((unpack (n + 1) r).take n))
        (mul (pow x n) (embed (Symbol.ofNat (r >>> (5 * n))))) := by
    have hreg : (unpack (n + 1) r).length = n + 1 := by simp [unpack]
    have hdrop : evalF x ((unpack (n + 1) r).drop n) =
        embed (Symbol.ofNat (r >>> (5 * n))) := by
      rw [← List.getElem_cons_drop, List.drop_eq_nil_of_le (by omega : (unpack (n + 1) r).length ≤ n + 1)]
      simp only [unpack, List.getElem_map, List.getElem_range,
        evalF_cons, evalF_nil, mul_zero, add_zero]
      rw [show (31 : Nat) = 2 ^ 5 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod,
        Nat.mod_eq_of_lt (top_lt_g (5 * n) r hr)]
      omega
    have hsplit := congrArg (evalF x) (List.take_append_drop n (unpack (n + 1) r)).symm
    rw [evalF_append] at hsplit
    rw [hsplit, hdrop]
    simp [unpack, List.length_take]
  have htake : mul x (evalF x ((unpack (n + 1) r).take n)) =
      add (mul x (evalF x (unpack (n + 1) r)))
        (mul (embed (Symbol.ofNat (r >>> (5 * n)))) (pow x (n + 1))) := by
    rw [heval, mul_add]
    rw [show mul x (mul (pow x n) (embed (Symbol.ofNat (r >>> (5 * n))))) =
        mul (embed (Symbol.ofNat (r >>> (5 * n)))) (pow x (n + 1)) from by
      rw [← mul_assoc, mul_comm x (pow x n), ← pow_succ,
        mul_comm (pow x (n + 1)) (embed (Symbol.ofNat (r >>> (5 * n))))]]
    rw [add_assoc, add_self, add_zero]
  have hgen : evalF x (low ++ [1]) = add (evalF x low) (pow x (n + 1)) := by
    rw [evalF_append, hlen]
    simp only [evalF_cons, evalF_nil, mul_zero, add_zero, embed_one, mul_one]
  rw [hstep, evalF_zipAdd x _ _ hzip, evalF_cons, evalF_map_scalar, htake, hgen, mul_add]
  ac_rfl

/-- After evaluation at any `x : GF1024`, the register after one regular step
equals `x·R + v + top·g`. -/
theorem regular_step_eval (r : Nat) (v : Symbol) (hr : r < 2 ^ 65) (x : GF1024) :
    evalF x (unpack 13 (Checksum.step 60 0x0fffffffffffffff Checksum.regularGenerators r v)) =
      add (add (mul x (evalF x (unpack 13 r))) (embed v))
        (mul (embed (Symbol.ofNat (r >>> 60))) (evalF x GF1024.regularGenerator)) :=
  step_eval 12 _ r v regularLow rfl hr (regular_step_unpack r v hr) x

/-- After evaluation at any `x : GF1024`, the register after one long step
equals `x·R + v + top·g`. -/
theorem long_step_eval (r : Nat) (v : Symbol) (hr : r < 2 ^ 75) (x : GF1024) :
    evalF x (unpack 15 (Checksum.step 70 0x3fffffffffffffffff Checksum.longGenerators r v)) =
      add (add (mul x (evalF x (unpack 15 r))) (embed v))
        (mul (embed (Symbol.ofNat (r >>> 70))) (evalF x GF1024.longGenerator)) :=
  step_eval 14 _ r v longLow rfl hr (long_step_unpack r v hr) x

end GF1024

end Codex32

namespace Codex32

namespace GF1024

/-- The folded multiple-of-`g` contribution accumulated by the telescoped
recurrence, for either checksum generator. -/
private def qsFold_g (generator : List Symbol) (x : GF1024)
    (qs : List (Symbol × Nat)) : GF1024 :=
  qs.foldl (fun s p => add s (mul (embed p.1) (mul (pow x p.2) (evalF x generator)))) zero

private theorem qsFold_g_cons (generator : List Symbol) (x : GF1024)
    (p : Symbol × Nat) (qs : List (Symbol × Nat)) :
    qsFold_g generator x (p :: qs) =
      add (mul (embed p.1) (mul (pow x p.2) (evalF x generator)))
        (qsFold_g generator x qs) := by
  rw [qsFold_g, List.foldl_cons, zero_add]
  exact foldl_add_start _ _ _

private theorem qsFold_g_shift (generator : List Symbol) (x : GF1024)
    (qs : List (Symbol × Nat)) :
    qsFold_g generator x (qs.map (fun p => (p.1, p.2 + 1))) =
      mul x (qsFold_g generator x qs) := by
  induction qs with
  | nil => simp [qsFold_g]
  | cons p ps ih =>
    rw [List.map_cons, qsFold_g_cons, qsFold_g_cons, ih]
    rw [mul_add]
    congr 1
    rw [pow_succ, mul_assoc (pow x p.2) x (evalF x generator),
      mul_left_comm (pow x p.2) x (evalF x generator),
      mul_left_comm x (embed p.1) (mul (pow x p.2) (evalF x generator))]

private theorem qsFold_g_zero (generator : List Symbol) (x : GF1024)
    (qs : List (Symbol × Nat)) (h : evalF x generator = zero) :
    qsFold_g generator x qs = zero := by
  induction qs with
  | nil => rfl
  | cons p qs ih =>
    rw [qsFold_g_cons, h, mul_zero, mul_zero, zero_add]
    exact ih

private def qsFold := qsFold_g regularGenerator

private def qsFoldLong := qsFold_g longGenerator

private theorem qsFold_zero (x : GF1024) (qs : List (Symbol × Nat))
    (h : evalF x regularGenerator = zero) : qsFold x qs = zero :=
  qsFold_g_zero regularGenerator x qs h

private theorem qsFoldLong_zero (x : GF1024) (qs : List (Symbol × Nat))
    (h : evalF x longGenerator = zero) : qsFoldLong x qs = zero :=
  qsFold_g_zero longGenerator x qs h

/-- Any bounded register recurrence with the one-step polynomial identity
has the same telescoped form. Width counts five-bit symbols; shift locates
the outgoing coefficient. -/
private theorem telescope_g (width shift : Nat) (step : Nat → Symbol → Nat)
    (generator : List Symbol) (initial : Nat)
    (initial_bound : initial < 2 ^ (5 * width))
    (step_bound : ∀ r v, step r v < 2 ^ (5 * width))
    (step_eval : ∀ r v, r < 2 ^ (5 * width) → ∀ x : GF1024,
      evalF x (unpack width (step r v)) =
        add (add (mul x (evalF x (unpack width r))) (embed v))
          (mul (embed (Symbol.ofNat (r >>> shift))) (evalF x generator)))
    (vs : List Symbol) :
    ∃ qs : List (Symbol × Nat), ∀ x : GF1024,
      evalF x (unpack width (vs.reverse.foldl step initial)) =
        add (mul (pow x vs.length) (evalF x (unpack width initial)))
          (add (evalF x vs.reverse.reverse) (qsFold_g generator x qs)) := by
  have hbound : ∀ l : List Symbol,
      l.reverse.foldl step initial < 2 ^ (5 * width) := by
    intro l
    induction l with
    | nil => exact initial_bound
    | cons v vs ih =>
      rw [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact step_bound _ _
  induction vs with
  | nil =>
    refine ⟨[], fun x => ?_⟩
    show evalF x (unpack width initial) = _
    simp only [List.reverse_nil, List.length_nil, pow_zero]
    rw [one_mul, evalF_nil, zero_add,
      show qsFold_g generator x [] = zero from rfl, add_zero]
  | cons v vs ih =>
    obtain ⟨qs, hq⟩ := ih
    refine ⟨(Symbol.ofNat ((vs.reverse.foldl step initial) >>> shift), 0) ::
      qs.map (fun p => (p.1, p.2 + 1)), fun x => ?_⟩
    rw [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [step_eval _ _ (hbound _) x, hq]
    rw [qsFold_g_cons, qsFold_g_shift, pow_zero, one_mul]
    have hexpand : mul x (add (mul (pow x vs.length) (evalF x (unpack width initial)))
        (add (evalF x vs.reverse.reverse) (qsFold_g generator x qs))) =
        add (mul (pow x (vs.length + 1)) (evalF x (unpack width initial)))
          (add (mul x (evalF x vs.reverse.reverse)) (mul x (qsFold_g generator x qs))) := by
      rw [mul_add, mul_add, ← mul_assoc, mul_comm x (pow x vs.length), ← pow_succ]
    rw [hexpand, List.length_cons, List.reverse_append, List.reverse_singleton,
      List.reverse_reverse, show [v] ++ vs = v :: vs from rfl, evalF_cons]
    ac_rfl

/-- The telescoped recurrence for the regular checksum: after `n` symbols,
the register evaluates to `xⁿ·init + M + g·Q` at every `x : GF1024`, with the
multiple-of-`g` contribution collected in `qsFold`. -/
theorem telescope (vs : List Symbol) :
    ∃ qs : List (Symbol × Nat), ∀ x : GF1024,
      evalF x (unpack 13 (vs.reverse.foldl (Checksum.step 60 0x0fffffffffffffff Checksum.regularGenerators) Checksum.initResidue)) =
        add (mul (pow x vs.length) (evalF x (unpack 13 Checksum.initResidue)))
          (add (evalF x vs.reverse.reverse) (qsFold x qs)) :=
  telescope_g 13 60 (Checksum.step 60 0x0fffffffffffffff Checksum.regularGenerators)
    regularGenerator Checksum.initResidue (by decide) regular_step_bound regular_step_eval vs

/-- The final statement in forward order. -/
theorem telescope_forward (vs : List Symbol) :
    ∃ qs : List (Symbol × Nat), ∀ x : GF1024,
      evalF x (unpack 13 (vs.foldl (Checksum.step 60 0x0fffffffffffffff Checksum.regularGenerators) Checksum.initResidue)) =
        add (mul (pow x vs.length) (evalF x (unpack 13 Checksum.initResidue)))
          (add (evalF x vs.reverse) (qsFold x qs)) := by
  obtain ⟨qs, hq⟩ := telescope vs.reverse
  refine ⟨qs, fun x => ?_⟩
  rw [List.reverse_reverse] at hq
  rw [hq]
  simp [List.length_reverse]

/-- The telescoped recurrence for the long checksum: after `n` symbols,
the register evaluates to `xⁿ·init + M + g·Q` at every `x : GF1024`, with the
multiple-of-`g` contribution collected in `qsFoldLong`. -/
theorem telescope_long (vs : List Symbol) :
    ∃ qs : List (Symbol × Nat), ∀ x : GF1024,
      evalF x (unpack 15 (vs.reverse.foldl (Checksum.step 70 0x3fffffffffffffffff Checksum.longGenerators) Checksum.initResidue)) =
        add (mul (pow x vs.length) (evalF x (unpack 15 Checksum.initResidue)))
          (add (evalF x vs.reverse.reverse) (qsFoldLong x qs)) :=
  telescope_g 15 70 (Checksum.step 70 0x3fffffffffffffffff Checksum.longGenerators)
    longGenerator Checksum.initResidue (by decide) long_step_bound long_step_eval vs

/-- The long telescope in forward order. -/
theorem telescope_long_forward (vs : List Symbol) :
    ∃ qs : List (Symbol × Nat), ∀ x : GF1024,
      evalF x (unpack 15 (vs.foldl (Checksum.step 70 0x3fffffffffffffffff Checksum.longGenerators) Checksum.initResidue)) =
        add (mul (pow x vs.length) (evalF x (unpack 15 Checksum.initResidue)))
          (add (evalF x vs.reverse) (qsFoldLong x qs)) := by
  obtain ⟨qs, hq⟩ := telescope_long vs.reverse
  refine ⟨qs, fun x => ?_⟩
  rw [List.reverse_reverse] at hq
  rw [hq]
  simp [List.length_reverse]

end GF1024

end Codex32

namespace Codex32

namespace GF1024

private theorem zipWith_add_eq_map (c1 c2 : List Symbol) :
    List.zipWith Field.add c1 c2 = (c1.zip c2).map fun p => Field.add p.1 p.2 := by
  induction c1 generalizing c2 with
  | nil => cases c2 with
    | nil => rfl
    | cons => rfl
  | cons a as ih =>
    cases c2 with
    | nil => rfl
    | cons b bs => simp only [List.zipWith_cons_cons, List.zip_cons_cons, List.map_cons, ih]

private theorem zipWith_add_reverse (c1 c2 : List Symbol) (hlen : c1.length = c2.length) :
    List.zipWith Field.add c1.reverse c2.reverse = (List.zipWith Field.add c1 c2).reverse := by
  induction c1 generalizing c2 with
  | nil => cases c2 with
    | nil => rfl
    | cons => simp at hlen
  | cons a as ih =>
    cases c2 with
    | nil => simp at hlen
    | cons b bs =>
      have hlen' : as.length = bs.length := by simp only [List.length_cons] at hlen; omega
      have hlenr : as.reverse.length = bs.reverse.length := by
        rw [List.length_reverse, List.length_reverse, hlen']
      rw [List.reverse_cons, List.reverse_cons, List.zipWith_cons_cons,
        List.zipWith_append hlenr, ih bs hlen', List.reverse_cons]
      rfl

/-- The BCH bound depends only on agreement at eight consecutive root powers. -/
private theorem detection_of_evaluations (root : GF1024) (period start : Nat)
    (hroot : root ≠ zero)
    (hinj : ∀ a b, a < period → b < period → pow root a = pow root b → a = b)
    (c1 c2 : List Symbol) (hlen : c1.length = c2.length)
    (hbound : c1.length ≤ period)
    (hwt : ((c1.zip c2).filter (fun p => p.1 ≠ p.2)).length ≤ 8)
    (heval : ∀ i < 8, evalF (pow root (start + i)) c1.reverse =
      evalF (pow root (start + i)) c2.reverse) : c1 = c2 := by
  have hDwt : ((List.zipWith Field.add c1.reverse c2.reverse).filter (· ≠ 0)).length ≤ 8 := by
    have h1 : (List.zipWith Field.add c1.reverse c2.reverse).filter (· ≠ 0) =
        (((c1.zip c2).filter (fun p => p.1 ≠ p.2)).map (fun p => Field.add p.1 p.2)).reverse := by
      rw [zipWith_add_reverse c1 c2 hlen, List.filter_reverse, zipWith_add_eq_map,
        List.filter_map]
      apply congrArg List.reverse
      apply congrArg (List.map (fun (p : Symbol × Symbol) => Field.add p.1 p.2))
      apply List.filter_congr
      intro (p : Symbol × Symbol) hp
      show ((fun x => decide (x ≠ 0)) ∘ fun p => Field.add p.1 p.2) p = decide (p.1 ≠ p.2)
      show decide (Field.add p.1 p.2 ≠ 0) = decide (p.1 ≠ p.2)
      exact decide_eq_decide.mpr (not_congr (Field.add_eq_zero p.1 p.2))
    rw [h1, List.length_reverse, List.length_map]
    exact hwt
  have hDlen : (List.zipWith Field.add c1.reverse c2.reverse).length ≤ period := by
    simp [List.length_zipWith, List.length_reverse, hlen]
    omega
  have hvan : ∀ i < 8, evalF (pow root (start + i))
      (List.zipWith Field.add c1.reverse c2.reverse) = zero := by
    intro i hi
    rw [evalF_zipAdd _ _ _ (by simp [List.length_reverse, hlen]), heval i hi]
    exact add_self _
  have hzero := sparse_zero (List.zipWith Field.add c1.reverse c2.reverse) root period start
    hroot hinj hDwt hDlen hvan
  have hrev : c1.reverse = c2.reverse := by
    apply List.ext_getElem (by simp [List.length_reverse, hlen])
    intro j h1' h2'
    have hDj := hzero ((List.zipWith Field.add c1.reverse c2.reverse)[j]'(by
      simp [List.length_zipWith, List.length_reverse, hlen] at h1' h2' ⊢; omega)) (List.getElem_mem _)
    simp only [List.getElem_zipWith] at hDj
    exact (Field.add_eq_zero _ _).mp hDj
  exact List.reverse_inj.mp hrev

/-- The BCH error-detection theorem for the regular checksum. Equal-length
valid regular strings that differ in at most eight symbols are identical. -/
theorem regular_detection (c1 c2 : List Symbol) (hlen : c1.length = c2.length)
    (hbound : 5 + c1.length ≤ 93) (hpoly : Checksum.regularPolymod c1 = Checksum.regularPolymod c2)
    (hwt : ((c1.zip c2).filter (fun p => p.1 ≠ p.2)).length ≤ 8) : c1 = c2 := by
  obtain ⟨qs, hq⟩ := telescope_forward c1
  obtain ⟨qs2, hq2⟩ := telescope_forward c2
  apply detection_of_evaluations beta 93 77 beta_ne_zero
    (fun a b ha hb h => beta_inj_below ha hb h) c1 c2 hlen (by omega) hwt
  intro i hi
  have hroot : 77 + i ∈ regularRoots :=
    regular_consecutive_roots (77 + i) (by simp [List.mem_range', hi])
  have hz := evalF_regularGenerator_zero (77 + i) hroot
  have h1 := hq (pow beta (77 + i))
  have h2 := hq2 (pow beta (77 + i))
  rw [qsFold_zero (pow beta (77 + i)) qs hz, add_zero] at h1
  rw [qsFold_zero (pow beta (77 + i)) qs2 hz, add_zero] at h2
  have hpoly' : unpack 13 (Checksum.regularPolymod c1) = unpack 13 (Checksum.regularPolymod c2) :=
    congrArg (unpack 13) hpoly
  simp only [Checksum.regularPolymod] at hpoly'
  have hpoly'' := congrArg (evalF (pow beta (77 + i))) hpoly'
  rw [h1, h2, hlen] at hpoly''
  have hce : evalF (pow beta (77 + i)) c1.reverse = evalF (pow beta (77 + i)) c2.reverse := by
    have h4 := congrArg (add (mul (pow (pow beta (77 + i)) c2.length) (evalF (pow beta (77 + i)) (unpack 13 Checksum.initResidue)))) hpoly''
    rw [add_cancel_left, add_cancel_left] at h4
    exact h4
  exact hce

/-- The BCH error-detection theorem for the long checksum. -/
theorem long_detection (c1 c2 : List Symbol) (hlen : c1.length = c2.length)
    (hbound : 5 + c1.length ≤ 1023) (hpoly : Checksum.longPolymod c1 = Checksum.longPolymod c2)
    (hwt : ((c1.zip c2).filter (fun p => p.1 ≠ p.2)).length ≤ 8) : c1 = c2 := by
  obtain ⟨qs, hq⟩ := telescope_long_forward c1
  obtain ⟨qs2, hq2⟩ := telescope_long_forward c2
  apply detection_of_evaluations gamma 1023 1019 gamma_ne_zero
    (fun a b ha hb h => gamma_inj_below ha hb h) c1 c2 hlen (by omega) hwt
  intro i hi
  have hroot : 1019 + i ∈ longRoots :=
    long_consecutive_roots (1019 + i) (by simp [List.mem_range', hi])
  have hz := evalF_longGenerator_zero (1019 + i) hroot
  have h1 := hq (pow gamma (1019 + i))
  have h2 := hq2 (pow gamma (1019 + i))
  rw [qsFoldLong_zero (pow gamma (1019 + i)) qs hz, add_zero] at h1
  rw [qsFoldLong_zero (pow gamma (1019 + i)) qs2 hz, add_zero] at h2
  have hpoly' : unpack 15 (Checksum.longPolymod c1) = unpack 15 (Checksum.longPolymod c2) :=
    congrArg (unpack 15) hpoly
  simp only [Checksum.longPolymod] at hpoly'
  have hpoly'' := congrArg (evalF (pow gamma (1019 + i))) hpoly'
  rw [h1, h2, hlen] at hpoly''
  have hce : evalF (pow gamma (1019 + i)) c1.reverse = evalF (pow gamma (1019 + i)) c2.reverse := by
    have h4 := congrArg (add (mul (pow (pow gamma (1019 + i)) c2.length)
        (evalF (pow gamma (1019 + i)) (unpack 15 Checksum.initResidue)))) hpoly''
    rw [add_cancel_left, add_cancel_left] at h4
    exact h4
  exact hce

/-- Packaged as an assertion about the executable regular verifier. -/
theorem verifyRegular_detects (c1 c2 : List Symbol) (hlen : c1.length = c2.length)
    (h1 : Checksum.verifyRegular c1 = true) (h2 : Checksum.verifyRegular c2 = true)
    (hwt : ((c1.zip c2).filter (fun p => p.1 ≠ p.2)).length ≤ 8) : c1 = c2 := by
  simp only [Checksum.verifyRegular, Bool.and_eq_true, beq_iff_eq] at h1 h2
  obtain ⟨hb1, hp1⟩ := h1
  obtain ⟨hb2, hp2⟩ := h2
  exact regular_detection c1 c2 hlen (of_decide_eq_true hb1) (hp1.trans hp2.symm) hwt

/-- Packaged for the long verifier. -/
theorem verifyLong_detects (c1 c2 : List Symbol) (hlen : c1.length = c2.length)
    (h1 : Checksum.verifyLong c1 = true) (h2 : Checksum.verifyLong c2 = true)
    (hwt : ((c1.zip c2).filter (fun p => p.1 ≠ p.2)).length ≤ 8) : c1 = c2 := by
  simp only [Checksum.verifyLong, Bool.and_eq_true, beq_iff_eq] at h1 h2
  obtain ⟨hb1, hp1⟩ := h1
  obtain ⟨hb2, hp2⟩ := h2
  exact long_detection c1 c2 hlen (of_decide_eq_true hb1) (hp1.trans hp2.symm) hwt


/-- The indices where two equal-length symbol lists differ. -/
private def diffIndices (c1 c2 : List Symbol) : List Nat :=
  (((c1.zip c2).zipIdx).filter (fun p => p.1.1 ≠ p.1.2)).map Prod.snd

private theorem zip_filter_ne_length_comm (a b : List Symbol) :
    ((a.zip b).filter (fun p => p.1 ≠ p.2)).length =
    ((b.zip a).filter (fun p => p.1 ≠ p.2)).length := by
  induction a generalizing b with
  | nil => simp
  | cons x xs ih =>
    cases b with
    | nil => simp
    | cons y ys =>
      simp only [List.zip_cons_cons]
      by_cases hxy : x = y
      · subst hxy
        rw [List.filter_cons_of_neg (by simp), List.filter_cons_of_neg (by simp)]
        exact ih ys
      · have hyx : ¬y = x := fun h => hxy h.symm
        rw [List.filter_cons_of_pos (by simp [hxy]), List.filter_cons_of_pos (by simp [hyx]),
          List.length_cons, List.length_cons, ih ys]

private theorem diffIndices_nodup (c1 c2 : List Symbol) : (diffIndices c1 c2).Nodup := by
  have h : (((c1.zip c2).zipIdx).map Prod.snd).Nodup := by
    rw [zipIdx_map_snd]
    exact nodup_map_add_range (c1.zip c2).length 0
  have hsub : List.Sublist
      ((((c1.zip c2).zipIdx).filter (fun p => p.1.1 ≠ p.1.2)).map Prod.snd)
      (((c1.zip c2).zipIdx).map Prod.snd) := by
    apply List.Sublist.map
    exact List.filter_sublist
  exact List.Sublist.nodup hsub h

private theorem diffIndices_length (c1 c2 : List Symbol) :
    (diffIndices c1 c2).length = ((c1.zip c2).filter (fun p => p.1 ≠ p.2)).length := by
  rw [diffIndices, List.length_map, zipIdx_filter_length (c1.zip c2) 0 (fun x => decide (x.1 ≠ x.2))]

private theorem mem_diffIndices (c1 c2 : List Symbol) (hlen : c1.length = c2.length)
    (i : Nat) (hi : i < c1.length)
    (hdiff : c1[i]'hi ≠ c2[i]'(by omega)) : i ∈ diffIndices c1 c2 := by
  have hziplen : (c1.zip c2).length = c1.length := by
    rw [List.length_zip, hlen, Nat.min_self]
  have hmem : ((c1.zip c2)[i]'(by omega), i) ∈ (c1.zip c2).zipIdx := by
    have h := mem_zipIdx_of_getElem (c1.zip c2) i (by omega) 0
    simp only [Nat.zero_add] at h
    exact h
  rw [diffIndices, List.mem_map]
  refine ⟨((c1.zip c2)[i]'(by omega), i), ?_, rfl⟩
  apply List.mem_filter.mpr
  constructor
  · exact hmem
  · simp only [List.getElem_zip]
    exact decide_eq_true hdiff

/-- The triangle bound for symbol differences, independent of checksum variant. -/
private theorem substitutions_weight (received c1 c2 : List Symbol)
    (hlen1 : received.length = c1.length) (hlen2 : received.length = c2.length)
    (hd1 : ((received.zip c1).filter (fun p => p.1 ≠ p.2)).length ≤ 4)
    (hd2 : ((received.zip c2).filter (fun p => p.1 ≠ p.2)).length ≤ 4) :
    ((c1.zip c2).filter (fun p => p.1 ≠ p.2)).length ≤ 8 := by
  have hsub : ∀ x ∈ diffIndices c1 c2, x ∈ diffIndices c1 received ++ diffIndices received c2 := by
    intro x hx
    rw [diffIndices] at hx ⊢
    rw [List.mem_append]
    obtain ⟨p, hp, hpx⟩ := List.mem_map.mp hx
    have hpf := (List.mem_filter.mp hp).2
    have hpm := (List.mem_filter.mp hp).1
    obtain ⟨_, hlt, heq⟩ := List.mem_zipIdx hpm
    rw [List.getElem_zip] at heq
    have hc12 : c1.length = c2.length := by omega
    have hz : (c1.zip c2).length = c1.length := by
      rw [List.length_zip, hc12, Nat.min_self]
    have hilt : p.2 < c1.length := by omega
    simp only [Nat.sub_zero] at heq
    have h11 : p.1.1 = c1[p.2]'hilt := by
      rw [heq]
    have h12 : p.1.2 = c2[p.2]'(by omega) := by
      rw [heq]
    have hd : c1[p.2]'hilt ≠ c2[p.2]'(by omega) := by
      rw [h11, h12] at hpf
      exact of_decide_eq_true hpf
    by_cases hcr : c1[p.2]'hilt = received[p.2]'(by omega)
    · right
      apply mem_diffIndices _ _ hlen2
      · show received[x]'(by omega) ≠ c2[x]'(by omega)
        simp only [← hpx]
        rw [hcr] at hd
        exact hd
    · left
      apply mem_diffIndices _ _ hlen1.symm
      · show c1[x]'(by omega) ≠ received[x]'(by omega)
        simp only [← hpx]
        exact hcr
  have hle := (diffIndices_nodup _ _).length_le_of_subset hsub
  rw [List.length_append] at hle
  simp only [diffIndices_length] at hle
  rw [zip_filter_ne_length_comm c1 received] at hle
  omega

/-- Four-substitution correction is unique: any two valid strings within
distance four of a received string are identical. -/
theorem regular_substitutions_unique (received c1 c2 : List Symbol)
    (hlen1 : received.length = c1.length) (hlen2 : received.length = c2.length)
    (hbound : 5 + c1.length ≤ 93)
    (h1 : Checksum.verifyRegular c1 = true) (h2 : Checksum.verifyRegular c2 = true)
    (hd1 : ((received.zip c1).filter (fun p => p.1 ≠ p.2)).length ≤ 4)
    (hd2 : ((received.zip c2).filter (fun p => p.1 ≠ p.2)).length ≤ 4) : c1 = c2 := by
  simp only [Checksum.verifyRegular, Bool.and_eq_true, beq_iff_eq] at h1 h2
  obtain ⟨hb1, hp1⟩ := h1
  obtain ⟨hb2, hp2⟩ := h2
  exact regular_detection c1 c2 (by omega) hbound (by rw [hp1, hp2])
    (substitutions_weight received c1 c2 hlen1 hlen2 hd1 hd2)

/-- Long-checksum four-substitution uniqueness. -/
theorem long_substitutions_unique (received c1 c2 : List Symbol)
    (hlen1 : received.length = c1.length) (hlen2 : received.length = c2.length)
    (hbound : 5 + c1.length ≤ 1023)
    (h1 : Checksum.verifyLong c1 = true) (h2 : Checksum.verifyLong c2 = true)
    (hd1 : ((received.zip c1).filter (fun p => p.1 ≠ p.2)).length ≤ 4)
    (hd2 : ((received.zip c2).filter (fun p => p.1 ≠ p.2)).length ≤ 4) : c1 = c2 := by
  simp only [Checksum.verifyLong, Bool.and_eq_true, beq_iff_eq] at h1 h2
  obtain ⟨hb1, hp1⟩ := h1
  obtain ⟨hb2, hp2⟩ := h2
  exact long_detection c1 c2 (by omega) hbound (by rw [hp1, hp2])
    (substitutions_weight received c1 c2 hlen1 hlen2 hd1 hd2)

/-- Differences are confined to the erased positions. -/
private theorem erasures_weight (c1 c2 : List Symbol) (E : List Nat)
    (hlen : c1.length = c2.length) (hE : E.length ≤ 8)
    (hagree : ∀ i : Nat, ∀ hi : i < c1.length, i ∉ E →
      c1[i]'hi = c2[i]'(by omega)) :
    ((c1.zip c2).filter (fun p => p.1 ≠ p.2)).length ≤ 8 := by
  have hsub : ∀ x ∈ diffIndices c1 c2, x ∈ E := by
    intro x hx
    rw [diffIndices] at hx
    obtain ⟨p, hp, hpx⟩ := List.mem_map.mp hx
    have hpf := (List.mem_filter.mp hp).2
    have hpm := (List.mem_filter.mp hp).1
    obtain ⟨_, hlt, heq⟩ := List.mem_zipIdx hpm
    rw [List.getElem_zip] at heq
    have hz : (c1.zip c2).length = c1.length := by
      rw [List.length_zip, hlen, Nat.min_self]
    have hilt : p.2 < c1.length := by omega
    simp only [Nat.sub_zero] at heq
    have h11 : p.1.1 = c1[p.2]'hilt := by
      rw [heq]
    have h12 : p.1.2 = c2[p.2]'(by omega) := by
      rw [heq]
    apply Classical.byContradiction
    intro hxE
    have hd : c1[p.2]'hilt ≠ c2[p.2]'(by omega) := by
      rw [h11, h12] at hpf
      exact of_decide_eq_true hpf
    exact hd (hagree p.2 hilt (by rw [hpx]; exact hxE))
  have hle := (diffIndices_nodup _ _).length_le_of_subset hsub
  rw [diffIndices_length] at hle
  omega

/-- Erasure correction is unique: two valid strings agreeing at every
non-erased position are identical when at most eight positions are erased. -/
theorem regular_erasures_unique (c1 c2 : List Symbol) (E : List Nat)
    (hlen : c1.length = c2.length) (hbound : 5 + c1.length ≤ 93)
    (h1 : Checksum.verifyRegular c1 = true) (h2 : Checksum.verifyRegular c2 = true)
    (hE : E.length ≤ 8)
    (hagree : ∀ i : Nat, ∀ hi : i < c1.length, i ∉ E →
      c1[i]'hi = c2[i]'(by omega)) : c1 = c2 := by
  simp only [Checksum.verifyRegular, Bool.and_eq_true, beq_iff_eq] at h1 h2
  obtain ⟨hb1, hp1⟩ := h1
  obtain ⟨hb2, hp2⟩ := h2
  exact regular_detection c1 c2 (by omega) hbound (by rw [hp1, hp2])
    (erasures_weight c1 c2 E hlen hE hagree)

/-- Long-checksum erasure uniqueness. -/
theorem long_erasures_unique (c1 c2 : List Symbol) (E : List Nat)
    (hlen : c1.length = c2.length) (hbound : 5 + c1.length ≤ 1023)
    (h1 : Checksum.verifyLong c1 = true) (h2 : Checksum.verifyLong c2 = true)
    (hE : E.length ≤ 8)
    (hagree : ∀ i : Nat, ∀ hi : i < c1.length, i ∉ E →
      c1[i]'hi = c2[i]'(by omega)) : c1 = c2 := by
  simp only [Checksum.verifyLong, Bool.and_eq_true, beq_iff_eq] at h1 h2
  obtain ⟨hb1, hp1⟩ := h1
  obtain ⟨hb2, hp2⟩ := h2
  exact long_detection c1 c2 (by omega) hbound (by rw [hp1, hp2])
    (erasures_weight c1 c2 E hlen hE hagree)

end GF1024

end Codex32
