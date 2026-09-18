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
`decide`.
-/

namespace Codex32

/-- The regular generating polynomial without its leading term, trailing-first. -/
def regularLow : List Symbol := [16, 16, 24, 27, 31, 25, 25, 25, 0, 8, 17, 27, 25]

/-- The long generating polynomial without its leading term, trailing-first. -/
def longLow : List Symbol := [23, 4, 22, 5, 6, 21, 23, 6, 21, 25, 9, 26, 25, 10, 15]

theorem regularGenerator_eq : GF1024.regularGenerator = regularLow ++ [1] := rfl

theorem longGenerator_eq : GF1024.longGenerator = longLow ++ [1] := rfl

/-- The initial residue of both polymod recurrences. -/
def initResidue : Nat := 0x23181b3

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

/-- Chunking a conditional XOR. -/
private theorem chunk_ite (c : Bool) (a g : Nat) (j : Nat) :
    Symbol.ofNat (((if c then a ^^^ g else a) >>> (5 * j)) &&& 31) =
      Field.add (Symbol.ofNat ((a >>> (5 * j)) &&& 31))
        (if c then Symbol.ofNat ((g >>> (5 * j)) &&& 31) else 0) := by
  cases c
  · simp [Field.add_zero]
  · simp [chunk_xor]

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

/-- Chunks of the mask-covered part agree with the register below the mask. -/
private theorem chunk_mask (r : Nat) (j : Nat) (hj : j < 12) :
    Symbol.ofNat (((r &&& 0x0fffffffffffffff) >>> (5 * j)) &&& 31) =
      Symbol.ofNat ((r >>> (5 * j)) &&& 31) := by
  have hmask : (0x0fffffffffffffff : Nat) = 2 ^ 60 - 1 := by decide
  have h31 : (31 : Nat) = 2 ^ 5 - 1 := by decide
  apply Fin.ext
  have hb : ((r &&& 0x0fffffffffffffff) >>> (5 * j)) &&& 31 = (r >>> (5 * j)) &&& 31 := by
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < 5
    · rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_and, Nat.testBit_and,
        Nat.testBit_shiftRight, h31, Nat.testBit_two_pow_sub_one]
      simp only [hi, decide_true, Bool.and_true]
      rw [hmask, Nat.testBit_two_pow_sub_one]
      have hk : 5 * j + i < 60 := by omega
      simp [hk]
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

/-- The chunk of the `next` part of a step: the value symbol at `j = 0`, the
previous register chunk otherwise. -/
private theorem next_chunk (r : Nat) (v : Symbol) (j : Nat) (hj : j < 13) :
    Symbol.ofNat (((((r &&& 0x0fffffffffffffff) <<< 5) ^^^ v.val) >>> (5 * j)) &&& 31) =
      if j = 0 then v else Symbol.ofNat ((r >>> (5 * (j - 1))) &&& 31) := by
  rw [chunk_xor, chunk_shiftLeft, chunk_val]
  by_cases hj0 : j = 0
  · subst hj0
    simp [Field.zero_add]
  · have hj1 : 1 ≤ j := by omega
    simp [hj0, Field.add_zero, chunk_mask r (j - 1) (by omega)]

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

/-- A generator constant vanishes in chunks above its width. -/
private theorem regular_chunk_outside (i g : Nat) (_hi : i < 5) (hg : g < 2 ^ 65)
    (j : Nat) (hj : 13 ≤ j) :
    Symbol.ofNat ((g >>> (5 * j)) &&& 31) = Field.mul (Symbol.ofNat (2 ^ i)) (regularLow.getD j 0) := by
  have hzero : g >>> (5 * j) = 0 := by
    rw [Nat.shiftRight_eq_div_pow]
    apply Nat.div_eq_of_lt
    calc g < 2 ^ 65 := hg
      _ ≤ 2 ^ (5 * j) := Nat.pow_le_pow_right (by decide) (by omega)
  have hget : regularLow.getD j 0 = 0 := by
    have hnone : regularLow[j]? = none := by
      rw [List.getElem?_eq_none]
      simp [regularLow, hj]
    simp [List.getD, hnone]
  rw [hzero, hget]
  simp [Field.mul_zero]
  rfl

/-- A long generator constant vanishes in chunks above its width. -/
private theorem long_chunk_outside (i g : Nat) (_hi : i < 5) (hg : g < 2 ^ 75)
    (j : Nat) (hj : 15 ≤ j) :
    Symbol.ofNat ((g >>> (5 * j)) &&& 31) = Field.mul (Symbol.ofNat (2 ^ i)) (longLow.getD j 0) := by
  have hzero : g >>> (5 * j) = 0 := by
    rw [Nat.shiftRight_eq_div_pow]
    apply Nat.div_eq_of_lt
    calc g < 2 ^ 75 := hg
      _ ≤ 2 ^ (5 * j) := Nat.pow_le_pow_right (by decide) (by omega)
  have hget : longLow.getD j 0 = 0 := by
    have hnone : longLow[j]? = none := by
      rw [List.getElem?_eq_none]
      simp [longLow, hj]
    simp [List.getD, hnone]
  rw [hzero, hget]
  simp [Field.mul_zero]
  rfl

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
  have hout : ∀ (i g : Nat), i < 5 → g < 2 ^ 65 → ∀ j : Nat, 13 ≤ j →
      Symbol.ofNat ((g >>> (5 * j)) &&& 31) = Field.mul (Symbol.ofNat (2 ^ i)) (regularLow.getD j 0) :=
    regular_chunk_outside
  have h := step_chunk 60 0x19dc500ce73fde210 0x1bfae00def77fe529 0x1fbd920fffe7bee52
    0x1739640bdeee3fdad 0x07729a039cfc75f5a regularLow
    (fun j => by
      by_cases hjx : j < 13
      · exact regular_chunk_0 ⟨j, hjx⟩
      · exact hout 0 0x19dc500ce73fde210 (by decide) (by decide) j (by omega))
    (fun j => by
      by_cases hjx : j < 13
      · exact regular_chunk_1 ⟨j, hjx⟩
      · exact hout 1 0x1bfae00def77fe529 (by decide) (by decide) j (by omega))
    (fun j => by
      by_cases hjx : j < 13
      · exact regular_chunk_2 ⟨j, hjx⟩
      · exact hout 2 0x1fbd920fffe7bee52 (by decide) (by decide) j (by omega))
    (fun j => by
      by_cases hjx : j < 13
      · exact regular_chunk_3 ⟨j, hjx⟩
      · exact hout 3 0x1739640bdeee3fdad (by decide) (by decide) j (by omega))
    (fun j => by
      by_cases hjx : j < 13
      · exact regular_chunk_4 ⟨j, hjx⟩
      · exact hout 4 0x07729a039cfc75f5a (by decide) (by decide) j (by omega))
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
  have hout : ∀ (i g : Nat), i < 5 → g < 2 ^ 75 → ∀ j : Nat, 15 ≤ j →
      Symbol.ofNat ((g >>> (5 * j)) &&& 31) = Field.mul (Symbol.ofNat (2 ^ i)) (longLow.getD j 0) :=
    long_chunk_outside
  have h := step_chunk 70 0x3d59d273535ea62d897 0x7a9becb6361c6c51507 0x543f9b7e6c38d8a2a0e
    0x0c577eaeccf1990d13c 0x1887f74f8dc71b10651 longLow
    (fun j => by
      by_cases hjx : j < 15
      · exact long_chunk_0 ⟨j, hjx⟩
      · exact hout 0 0x3d59d273535ea62d897 (by decide) (by decide) j (by omega))
    (fun j => by
      by_cases hjx : j < 15
      · exact long_chunk_1 ⟨j, hjx⟩
      · exact hout 1 0x7a9becb6361c6c51507 (by decide) (by decide) j (by omega))
    (fun j => by
      by_cases hjx : j < 15
      · exact long_chunk_2 ⟨j, hjx⟩
      · exact hout 2 0x543f9b7e6c38d8a2a0e (by decide) (by decide) j (by omega))
    (fun j => by
      by_cases hjx : j < 15
      · exact long_chunk_3 ⟨j, hjx⟩
      · exact hout 3 0x0c577eaeccf1990d13c (by decide) (by decide) j (by omega))
    (fun j => by
      by_cases hjx : j < 15
      · exact long_chunk_4 ⟨j, hjx⟩
      · exact hout 4 0x1887f74f8dc71b10651 (by decide) (by decide) j (by omega))
    r v (by rw [hmask] at *; exact hr) j.val hj
  rw [hmask, hgens]
  have hget : longLow.getD j.val 0 = longLow[j.val] := by
    simp only [List.getD, List.getElem?_eq_getElem (l := longLow) j.isLt, Option.getD_some]
    rfl
  rw [hget] at h
  exact h

/-- The step map stays within its register. -/
theorem regular_step_bound (r : Nat) (v : Symbol) :
    Checksum.step 60 0x0fffffffffffffff Checksum.regularGenerators r v < 2 ^ 65 := by
  have hnext : (((r &&& 0x0fffffffffffffff) <<< 5) ^^^ v.val) < 2 ^ 65 := by
    have h1 : (r &&& 0x0fffffffffffffff) <<< 5 < 2 ^ 65 := by
      rw [Nat.shiftLeft_eq]
      have hlt : r &&& 0x0fffffffffffffff < 2 ^ 60 := by
        calc r &&& 0x0fffffffffffffff ≤ 0x0fffffffffffffff := Nat.and_le_right
          _ < 2 ^ 60 := by decide
      have hmul : (r &&& 0x0fffffffffffffff) * 2 ^ 5 < 2 ^ 60 * 2 ^ 5 :=
        Nat.mul_lt_mul_of_pos_right hlt (by decide : 0 < 2 ^ 5)
      have h2 : 2 ^ 60 * 2 ^ 5 = 2 ^ 65 := by decide
      rw [h2] at hmul
      exact hmul
    exact Nat.xor_lt_two_pow h1 (by have := v.isLt; omega)
  have hg : ∀ g ∈ Checksum.regularGenerators, g < 2 ^ 65 := by decide
  have hfold : ∀ (l : List (Nat × Nat)) (init : Nat), init < 2 ^ 65 →
      (∀ p ∈ l, p.1 < 2 ^ 65) →
      (l.foldl (fun acc p => if ((r >>> 60 >>> p.2) &&& 1 == 1) = true then acc ^^^ p.1 else acc) init) < 2 ^ 65 := by
    intro l
    induction l with
    | nil => intro init hi _; exact hi
    | cons p ps ih =>
      intro init hi hmem
      rw [List.foldl_cons]
      show (List.foldl (fun acc p => if ((r >>> 60 >>> p.2) &&& 1 == 1) = true then acc ^^^ p.1 else acc)
          (if ((r >>> 60 >>> p.2) &&& 1 == 1) = true then init ^^^ p.1 else init) ps) < 2 ^ 65
      split
      · rename_i hc
        apply ih
        · exact Nat.xor_lt_two_pow hi (hmem p (by simp))
        · intro q hq
          exact hmem q (by simp [hq])
      · rename_i hc
        apply ih
        · exact hi
        · intro q hq
          exact hmem q (by simp [hq])
  unfold Checksum.step
  show (Checksum.regularGenerators.zipIdx.foldl (fun acc p =>
      if ((r >>> 60 >>> p.2) &&& 1 == 1) = true then acc ^^^ p.1 else acc)
      (((r &&& 0x0fffffffffffffff) <<< 5) ^^^ v.val)) < 2 ^ 65
  apply hfold _ _ hnext
  intro p hp
  have h2 := List.mem_zipIdx hp
  obtain ⟨_, _, heq⟩ := h2
  rw [heq]
  exact hg _ (List.getElem_mem _)

/-- The long step map stays within its register. -/
theorem long_step_bound (r : Nat) (v : Symbol) :
    Checksum.step 70 0x3fffffffffffffffff Checksum.longGenerators r v < 2 ^ 75 := by
  have hnext : (((r &&& 0x3fffffffffffffffff) <<< 5) ^^^ v.val) < 2 ^ 75 := by
    have h1 : (r &&& 0x3fffffffffffffffff) <<< 5 < 2 ^ 75 := by
      rw [Nat.shiftLeft_eq]
      have hlt : r &&& 0x3fffffffffffffffff < 2 ^ 70 := by
        calc r &&& 0x3fffffffffffffffff ≤ 0x3fffffffffffffffff := Nat.and_le_right
          _ < 2 ^ 70 := by decide
      have hmul : (r &&& 0x3fffffffffffffffff) * 2 ^ 5 < 2 ^ 70 * 2 ^ 5 :=
        Nat.mul_lt_mul_of_pos_right hlt (by decide : 0 < 2 ^ 5)
      have h2 : 2 ^ 70 * 2 ^ 5 = 2 ^ 75 := by decide
      rw [h2] at hmul
      exact hmul
    exact Nat.xor_lt_two_pow h1 (by have := v.isLt; omega)
  have hg : ∀ g ∈ Checksum.longGenerators, g < 2 ^ 75 := by decide
  have hfold : ∀ (l : List (Nat × Nat)) (init : Nat), init < 2 ^ 75 →
      (∀ p ∈ l, p.1 < 2 ^ 75) →
      (l.foldl (fun acc p => if ((r >>> 70 >>> p.2) &&& 1 == 1) = true then acc ^^^ p.1 else acc) init) < 2 ^ 75 := by
    intro l
    induction l with
    | nil => intro init hi _; exact hi
    | cons p ps ih =>
      intro init hi hmem
      rw [List.foldl_cons]
      show (List.foldl (fun acc p => if ((r >>> 70 >>> p.2) &&& 1 == 1) = true then acc ^^^ p.1 else acc)
          (if ((r >>> 70 >>> p.2) &&& 1 == 1) = true then init ^^^ p.1 else init) ps) < 2 ^ 75
      split
      · rename_i hc
        apply ih
        · exact Nat.xor_lt_two_pow hi (hmem p (by simp))
        · intro q hq
          exact hmem q (by simp [hq])
      · rename_i hc
        apply ih
        · exact hi
        · intro q hq
          exact hmem q (by simp [hq])
  unfold Checksum.step
  show (Checksum.longGenerators.zipIdx.foldl (fun acc p =>
      if ((r >>> 70 >>> p.2) &&& 1 == 1) = true then acc ^^^ p.1 else acc)
      (((r &&& 0x3fffffffffffffffff) <<< 5) ^^^ v.val)) < 2 ^ 75
  apply hfold _ _ hnext
  intro p hp
  have h2 := List.mem_zipIdx hp
  obtain ⟨_, _, heq⟩ := h2
  rw [heq]
  exact hg _ (List.getElem_mem _)

/-- The list form of one regular step: the register after the step is the
shifted register XOR the top symbol times the low generator polynomial. -/
theorem regular_step_unpack (r : Nat) (v : Symbol) (hr : r < 2 ^ 65) :
    unpack 13 (Checksum.step 60 0x0fffffffffffffff Checksum.regularGenerators r v) =
      List.zipWith Field.add (v :: (unpack 13 r).take 12)
        (regularLow.map (Field.mul (Symbol.ofNat (r >>> 60)))) := by
  apply List.ext_getElem
  · simp only [unpack, List.length_map, List.length_range, List.length_zipWith,
      List.length_cons, List.length_take, List.length_map, regularLow]
    omega
  · intro j h1 h2
    have hj : j < 13 := by simpa [unpack] using h1
    cases j with
    | zero =>
      have hc := regular_step_chunk r v hr ⟨0, by decide⟩
      simp only [unpack, List.getElem_map, List.getElem_range, List.getElem_zipWith,
        List.getElem_cons_zero, List.getElem_map]
      rw [hc]
      simp
    | succ j =>
      have hc := regular_step_chunk r v hr ⟨j + 1, by omega⟩
      simp only [unpack, List.getElem_map, List.getElem_range, List.getElem_zipWith,
        List.getElem_cons_succ, List.getElem_take, List.getElem_map]
      rw [hc]
      simp

/-- The list form of one long step. -/
theorem long_step_unpack (r : Nat) (v : Symbol) (hr : r < 2 ^ 75) :
    unpack 15 (Checksum.step 70 0x3fffffffffffffffff Checksum.longGenerators r v) =
      List.zipWith Field.add (v :: (unpack 15 r).take 14)
        (longLow.map (Field.mul (Symbol.ofNat (r >>> 70)))) := by
  apply List.ext_getElem
  · simp only [unpack, List.length_map, List.length_range, List.length_zipWith,
      List.length_cons, List.length_take, List.length_map, longLow]
    omega
  · intro j h1 h2
    have hj : j < 15 := by simpa [unpack] using h1
    cases j with
    | zero =>
      have hc := long_step_chunk r v hr ⟨0, by decide⟩
      simp only [unpack, List.getElem_map, List.getElem_range, List.getElem_zipWith,
        List.getElem_cons_zero, List.getElem_map]
      rw [hc]
      simp
    | succ j =>
      have hc := long_step_chunk r v hr ⟨j + 1, by omega⟩
      simp only [unpack, List.getElem_map, List.getElem_range, List.getElem_zipWith,
        List.getElem_cons_succ, List.getElem_take, List.getElem_map]
      rw [hc]
      simp

/-- After evaluation at any `x : GF1024`, the register after one regular step
equals `x·R + v + top·g`. -/
theorem regular_step_eval (r : Nat) (v : Symbol) (hr : r < 2 ^ 65) (x : GF1024) :
    evalF x (unpack 13 (Checksum.step 60 0x0fffffffffffffff Checksum.regularGenerators r v)) =
      add (add (mul x (evalF x (unpack 13 r))) (embed v))
        (mul (embed (Symbol.ofNat (r >>> 60))) (evalF x GF1024.regularGenerator)) := by
  have hlen : (v :: (unpack 13 r).take 12).length =
      (regularLow.map (Field.mul (Symbol.ofNat (r >>> 60)))).length := by
    simp [unpack, regularLow]
  have heval : evalF x (unpack 13 r) =
      add (evalF x ((unpack 13 r).take 12))
        (mul (pow x 12) (embed (Symbol.ofNat (r >>> 60)))) := by
    have hlen13 : (unpack 13 r).length = 13 := by simp [unpack]
    have hdrop : evalF x ((unpack 13 r).drop 12) = embed (Symbol.ofNat (r >>> 60)) := by
      rw [← List.getElem_cons_drop, List.drop_eq_nil_of_le (by omega : 13 ≤ 13)]
      simp only [unpack, List.getElem_map, List.getElem_range, Nat.reduceMul,
        evalF_cons, evalF_nil, mul_zero, add_zero]
      have hlt : r >>> 60 < 32 := top_lt_g 60 r hr
      rw [show (31 : Nat) = 2 ^ 5 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod,
        Nat.mod_eq_of_lt hlt]
      rw [hlen13]
      decide
    have hsplit := congrArg (evalF x) (List.take_append_drop 12 (unpack 13 r)).symm
    rw [evalF_append] at hsplit
    rw [hsplit, hdrop]
    have hlen : (List.take 12 (unpack 13 r)).length = 12 := by simp [unpack, List.length_take]
    rw [hlen]
  have htake2 : mul x (evalF x ((unpack 13 r).take 12)) =
      add (mul x (evalF x (unpack 13 r)))
        (mul (embed (Symbol.ofNat (r >>> 60))) (pow x 13)) := by
    rw [heval, mul_add]
    rw [show mul x (mul (pow x 12) (embed (Symbol.ofNat (r >>> 60)))) =
        mul (embed (Symbol.ofNat (r >>> 60))) (pow x 13) from by
      rw [← mul_assoc, mul_comm x (pow x 12), ← pow_succ,
        mul_comm (pow x 13) (embed (Symbol.ofNat (r >>> 60)))]]
    rw [add_assoc, add_self, add_zero]
  have hg13 : evalF x GF1024.regularGenerator = add (evalF x regularLow) (pow x 13) := by
    rw [regularGenerator_eq, evalF_append, show regularLow.length = 13 from by decide]
    simp only [evalF_cons, evalF_nil, mul_zero, add_zero, embed_one, mul_one]
  rw [regular_step_unpack r v hr, evalF_zipAdd x _ _ hlen, evalF_cons, evalF_map_scalar,
    htake2, hg13, mul_add]
  ac_rfl

/-- After evaluation at any `x : GF1024`, the register after one long step
equals `x·R + v + top·g`. -/
theorem long_step_eval (r : Nat) (v : Symbol) (hr : r < 2 ^ 75) (x : GF1024) :
    evalF x (unpack 15 (Checksum.step 70 0x3fffffffffffffffff Checksum.longGenerators r v)) =
      add (add (mul x (evalF x (unpack 15 r))) (embed v))
        (mul (embed (Symbol.ofNat (r >>> 70))) (evalF x GF1024.longGenerator)) := by
  have hlen : (v :: (unpack 15 r).take 14).length =
      (longLow.map (Field.mul (Symbol.ofNat (r >>> 70)))).length := by
    simp [unpack, longLow]
  have heval : evalF x (unpack 15 r) =
      add (evalF x ((unpack 15 r).take 14))
        (mul (pow x 14) (embed (Symbol.ofNat (r >>> 70)))) := by
    have hlen15 : (unpack 15 r).length = 15 := by simp [unpack]
    have hdrop : evalF x ((unpack 15 r).drop 14) = embed (Symbol.ofNat (r >>> 70)) := by
      rw [← List.getElem_cons_drop, List.drop_eq_nil_of_le (by omega : 15 ≤ 15)]
      simp only [unpack, List.getElem_map, List.getElem_range, Nat.reduceMul,
        evalF_cons, evalF_nil, mul_zero, add_zero]
      have hlt : r >>> 70 < 32 := top_lt_g 70 r hr
      rw [show (31 : Nat) = 2 ^ 5 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod,
        Nat.mod_eq_of_lt hlt]
      rw [hlen15]
      decide
    have hsplit := congrArg (evalF x) (List.take_append_drop 14 (unpack 15 r)).symm
    rw [evalF_append] at hsplit
    rw [hsplit, hdrop]
    have hlen : (List.take 14 (unpack 15 r)).length = 14 := by simp [unpack, List.length_take]
    rw [hlen]
  have htake2 : mul x (evalF x ((unpack 15 r).take 14)) =
      add (mul x (evalF x (unpack 15 r)))
        (mul (embed (Symbol.ofNat (r >>> 70))) (pow x 15)) := by
    rw [heval, mul_add]
    rw [show mul x (mul (pow x 14) (embed (Symbol.ofNat (r >>> 70)))) =
        mul (embed (Symbol.ofNat (r >>> 70))) (pow x 15) from by
      rw [← mul_assoc, mul_comm x (pow x 14), ← pow_succ,
        mul_comm (pow x 15) (embed (Symbol.ofNat (r >>> 70)))]]
    rw [add_assoc, add_self, add_zero]
  have hg15 : evalF x GF1024.longGenerator = add (evalF x longLow) (pow x 15) := by
    rw [longGenerator_eq, evalF_append, show longLow.length = 15 from by decide]
    simp only [evalF_cons, evalF_nil, mul_zero, add_zero, embed_one, mul_one]
  rw [long_step_unpack r v hr, evalF_zipAdd x _ _ hlen, evalF_cons, evalF_map_scalar,
    htake2, hg15, mul_add]
  ac_rfl

/-- A bound on the shifted-out top of the long register. -/
private theorem long_top_lt (r : Nat) (hr : r < 2 ^ 75) : r >>> 70 < 32 := by
  rw [Nat.shiftRight_eq_div_pow]
  have h : 2 ^ 75 = 2 ^ 70 * 32 := by decide
  rw [h] at hr
  exact Nat.div_lt_of_lt_mul hr

end GF1024

end Codex32

namespace Codex32

namespace GF1024

/-- The folded multiple-of-`g` contribution accumulated by the telescoped
recurrence. -/
private def qsFold (x : GF1024) (qs : List (Symbol × Nat)) : GF1024 :=
  qs.foldl (fun s p => add s (mul (embed p.1) (mul (pow x p.2) (evalF x regularGenerator)))) zero

private theorem qsFold_cons (x : GF1024) (p : Symbol × Nat) (qs : List (Symbol × Nat)) :
    qsFold x (p :: qs) =
      add (mul (embed p.1) (mul (pow x p.2) (evalF x regularGenerator))) (qsFold x qs) := by
  show qsFold x (p :: qs) = _
  rw [qsFold, List.foldl_cons, zero_add]
  exact foldl_add_start _ _ _

private theorem mul_foldl_add (u : GF1024) (l : List α) (g : α → GF1024) :
    ∀ init : GF1024, mul u (l.foldl (fun s p => add s (g p)) init) =
      l.foldl (fun s p => add s (mul u (g p))) (mul u init) := by
  induction l with
  | nil => intro init; rfl
  | cons p ps ih =>
    intro init
    simp only [List.foldl_cons]
    rw [ih (add init (g p)), mul_add]

private theorem qsFold_shift (x : GF1024) (qs : List (Symbol × Nat)) :
    qsFold x (qs.map (fun p => (p.1, p.2 + 1))) = mul x (qsFold x qs) := by
  induction qs with
  | nil => simp [qsFold]
  | cons p ps ih =>
    rw [List.map_cons, qsFold_cons, qsFold_cons, ih]
    show add (mul (embed (p.1, p.2 + 1).1) (mul (pow x (p.1, p.2 + 1).2) (evalF x regularGenerator)))
        (mul x (qsFold x ps)) =
        mul x (add (mul (embed p.1) (mul (pow x p.2) (evalF x regularGenerator))) (qsFold x ps))
    rw [mul_add,
      show mul (embed (p.1, p.2 + 1).1) (mul (pow x (p.1, p.2 + 1).2) (evalF x regularGenerator)) =
        mul x (mul (embed p.1) (mul (pow x p.2) (evalF x regularGenerator))) from by
      rw [pow_succ, mul_assoc (pow x p.2) x (evalF x regularGenerator),
        mul_left_comm (pow x p.2) x (evalF x regularGenerator),
        mul_left_comm x (embed p.1) (mul (pow x p.2) (evalF x regularGenerator))]]

private theorem qsFold_zero (x : GF1024) (qs : List (Symbol × Nat))
    (h : evalF x regularGenerator = zero) : qsFold x qs = zero := by
  induction qs with
  | nil => rfl
  | cons p qs ih =>
    rw [qsFold_cons, h, mul_zero, mul_zero, zero_add]
    exact ih
/-- The telescoped recurrence for the regular checksum: after `n` symbols,
the register evaluates to `xⁿ·init + M + g·Q` at every `x : GF1024`, with the
multiple-of-`g` contribution collected in `qsFold`. -/
theorem telescope (vs : List Symbol) :
    ∃ qs : List (Symbol × Nat), ∀ x : GF1024,
      evalF x (unpack 13 (vs.reverse.foldl (Checksum.step 60 0x0fffffffffffffff Checksum.regularGenerators) initResidue)) =
        add (mul (pow x vs.length) (evalF x (unpack 13 initResidue)))
          (add (evalF x vs.reverse.reverse) (qsFold x qs)) := by
  have hbound : ∀ l : List Symbol,
      l.reverse.foldl (Checksum.step 60 0x0fffffffffffffff Checksum.regularGenerators) initResidue <
        2 ^ 65 := by
    intro l
    induction l with
    | nil => decide
    | cons v vs ih =>
      rw [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact regular_step_bound _ _
  induction vs with
  | nil =>
    refine ⟨[], fun x => ?_⟩
    show evalF x (unpack 13 initResidue) = _
    simp only [List.reverse_nil, List.length_nil, pow_zero]
    rw [one_mul, evalF_nil, zero_add, show qsFold x [] = zero from rfl, add_zero]
  | cons v vs ih =>
    obtain ⟨qs, hq⟩ := ih
    refine ⟨(Symbol.ofNat ((vs.reverse.foldl (Checksum.step 60 0x0fffffffffffffff
        Checksum.regularGenerators) initResidue) >>> 60), 0) :: qs.map (fun p => (p.1, p.2 + 1)),
      fun x => ?_⟩
    rw [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [regular_step_eval _ _ (hbound _) x, hq]
    rw [qsFold_cons, qsFold_shift, pow_zero, one_mul]
    have hexpand : mul x (add (mul (pow x vs.length) (evalF x (unpack 13 initResidue)))
        (add (evalF x vs.reverse.reverse) (qsFold x qs))) =
        add (mul (pow x (vs.length + 1)) (evalF x (unpack 13 initResidue)))
          (add (mul x (evalF x vs.reverse.reverse)) (mul x (qsFold x qs))) := by
      rw [mul_add, mul_add, ← mul_assoc, mul_comm x (pow x vs.length), ← pow_succ]
    rw [hexpand, List.length_cons, List.reverse_append, List.reverse_singleton,
      List.reverse_reverse, show [v] ++ vs = v :: vs from rfl, evalF_cons]
    ac_rfl

/-- The final statement in forward order. -/
theorem telescope_forward (vs : List Symbol) :
    ∃ qs : List (Symbol × Nat), ∀ x : GF1024,
      evalF x (unpack 13 (vs.foldl (Checksum.step 60 0x0fffffffffffffff Checksum.regularGenerators) initResidue)) =
        add (mul (pow x vs.length) (evalF x (unpack 13 initResidue)))
          (add (evalF x vs.reverse) (qsFold x qs)) := by
  obtain ⟨qs, hq⟩ := telescope vs.reverse
  refine ⟨qs, fun x => ?_⟩
  rw [List.reverse_reverse] at hq
  rw [hq]
  simp [List.length_reverse]

private def qsFoldLong (x : GF1024) (qs : List (Symbol × Nat)) : GF1024 :=
  qs.foldl (fun s p => add s (mul (embed p.1) (mul (pow x p.2) (evalF x longGenerator)))) zero

private theorem qsFoldLong_cons (x : GF1024) (p : Symbol × Nat) (qs : List (Symbol × Nat)) :
    qsFoldLong x (p :: qs) =
      add (mul (embed p.1) (mul (pow x p.2) (evalF x longGenerator))) (qsFoldLong x qs) := by
  show qsFoldLong x (p :: qs) = _
  rw [qsFoldLong, List.foldl_cons, zero_add]
  exact foldl_add_start _ _ _

private theorem qsFoldLong_shift (x : GF1024) (qs : List (Symbol × Nat)) :
    qsFoldLong x (qs.map (fun p => (p.1, p.2 + 1))) = mul x (qsFoldLong x qs) := by
  induction qs with
  | nil => simp [qsFoldLong]
  | cons p ps ih =>
    rw [List.map_cons, qsFoldLong_cons, qsFoldLong_cons, ih]
    show add (mul (embed (p.1, p.2 + 1).1) (mul (pow x (p.1, p.2 + 1).2) (evalF x longGenerator)))
        (mul x (qsFoldLong x ps)) =
        mul x (add (mul (embed p.1) (mul (pow x p.2) (evalF x longGenerator))) (qsFoldLong x ps))
    rw [mul_add,
      show mul (embed (p.1, p.2 + 1).1) (mul (pow x (p.1, p.2 + 1).2) (evalF x longGenerator)) =
        mul x (mul (embed p.1) (mul (pow x p.2) (evalF x longGenerator))) from by
      rw [pow_succ, mul_assoc (pow x p.2) x (evalF x longGenerator),
        mul_left_comm (pow x p.2) x (evalF x longGenerator),
        mul_left_comm x (embed p.1) (mul (pow x p.2) (evalF x longGenerator))]]

private theorem qsFoldLong_zero (x : GF1024) (qs : List (Symbol × Nat))
    (h : evalF x longGenerator = zero) : qsFoldLong x qs = zero := by
  induction qs with
  | nil => rfl
  | cons p qs ih =>
    rw [qsFoldLong_cons, h, mul_zero, mul_zero, zero_add]
    exact ih

/-- The telescoped recurrence for the long checksum: after `n` symbols,
the register evaluates to `xⁿ·init + M + g·Q` at every `x : GF1024`, with the
multiple-of-`g` contribution collected in `qsFoldLong`. -/
theorem telescope_long (vs : List Symbol) :
    ∃ qs : List (Symbol × Nat), ∀ x : GF1024,
      evalF x (unpack 15 (vs.reverse.foldl (Checksum.step 70 0x3fffffffffffffffff Checksum.longGenerators) initResidue)) =
        add (mul (pow x vs.length) (evalF x (unpack 15 initResidue)))
          (add (evalF x vs.reverse.reverse) (qsFoldLong x qs)) := by
  have hbound : ∀ l : List Symbol,
      l.reverse.foldl (Checksum.step 70 0x3fffffffffffffffff Checksum.longGenerators) initResidue <
        2 ^ 75 := by
    intro l
    induction l with
    | nil => decide
    | cons v vs ih =>
      rw [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact long_step_bound _ _
  induction vs with
  | nil =>
    refine ⟨[], fun x => ?_⟩
    show evalF x (unpack 15 initResidue) = _
    simp only [List.reverse_nil, List.length_nil, pow_zero]
    rw [one_mul, evalF_nil, zero_add, show qsFoldLong x [] = zero from rfl, add_zero]
  | cons v vs ih =>
    obtain ⟨qs, hq⟩ := ih
    refine ⟨(Symbol.ofNat ((vs.reverse.foldl (Checksum.step 70 0x3fffffffffffffffff
        Checksum.longGenerators) initResidue) >>> 70), 0) :: qs.map (fun p => (p.1, p.2 + 1)),
      fun x => ?_⟩
    rw [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [long_step_eval _ _ (hbound _) x, hq]
    rw [qsFoldLong_cons, qsFoldLong_shift, pow_zero, one_mul]
    have hexpand : mul x (add (mul (pow x vs.length) (evalF x (unpack 15 initResidue)))
        (add (evalF x vs.reverse.reverse) (qsFoldLong x qs))) =
        add (mul (pow x (vs.length + 1)) (evalF x (unpack 15 initResidue)))
          (add (mul x (evalF x vs.reverse.reverse)) (mul x (qsFoldLong x qs))) := by
      rw [mul_add, mul_add, ← mul_assoc, mul_comm x (pow x vs.length), ← pow_succ]
    rw [hexpand, List.length_cons, List.reverse_append, List.reverse_singleton,
      List.reverse_reverse, show [v] ++ vs = v :: vs from rfl, evalF_cons]
    ac_rfl

/-- The long telescope in forward order. -/
theorem telescope_long_forward (vs : List Symbol) :
    ∃ qs : List (Symbol × Nat), ∀ x : GF1024,
      evalF x (unpack 15 (vs.foldl (Checksum.step 70 0x3fffffffffffffffff Checksum.longGenerators) initResidue)) =
        add (mul (pow x vs.length) (evalF x (unpack 15 initResidue)))
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

/-- The BCH error-detection theorem for the regular checksum. Equal-length
valid regular strings that differ in at most eight symbols are identical. -/
theorem regular_detection (c1 c2 : List Symbol) (hlen : c1.length = c2.length)
    (hbound : 5 + c1.length ≤ 93) (hpoly : Checksum.regularPolymod c1 = Checksum.regularPolymod c2)
    (hwt : ((c1.zip c2).filter (fun p => p.1 ≠ p.2)).length ≤ 8) : c1 = c2 := by
  obtain ⟨qs, hq⟩ := telescope_forward c1
  obtain ⟨qs2, hq2⟩ := telescope_forward c2
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
  have hDlen : (List.zipWith Field.add c1.reverse c2.reverse).length ≤ 93 := by
    simp [List.length_zipWith, List.length_reverse, hlen]
    omega
  have hvan : ∀ i < 8, evalF (pow beta (77 + i))
      (List.zipWith Field.add c1.reverse c2.reverse) = zero := by
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
    unfold initResidue at h1 h2
    have hpoly'' := congrArg (evalF (pow beta (77 + i))) hpoly'
    rw [h1, h2, hlen] at hpoly''
    have hce : evalF (pow beta (77 + i)) c1.reverse = evalF (pow beta (77 + i)) c2.reverse := by
      have h4 := congrArg (add (mul (pow (pow beta (77 + i)) c2.length) (evalF (pow beta (77 + i)) (unpack 13 36798899)))) hpoly''
      rw [add_cancel_left, add_cancel_left] at h4
      exact h4
    rw [evalF_zipAdd _ _ _ (by simp [List.length_reverse, hlen]), hce]
    exact add_self _
  have hzero := sparse_zero (List.zipWith Field.add c1.reverse c2.reverse) beta 93 77
    beta_ne_zero (fun a b ha hb h => beta_inj_below ha hb h) hDwt hDlen hvan
  have hrev : c1.reverse = c2.reverse := by
    apply List.ext_getElem (by simp [List.length_reverse, hlen])
    intro j h1' h2'
    have hDj := hzero ((List.zipWith Field.add c1.reverse c2.reverse)[j]'(by
      simp [List.length_zipWith, List.length_reverse, hlen] at h1' h2' ⊢; omega)) (List.getElem_mem _)
    simp only [List.getElem_zipWith] at hDj
    exact (Field.add_eq_zero _ _).mp hDj
  exact List.reverse_inj.mp hrev

/-- The BCH error-detection theorem for the long checksum. -/
theorem long_detection (c1 c2 : List Symbol) (hlen : c1.length = c2.length)
    (hbound : 5 + c1.length ≤ 1023) (hpoly : Checksum.longPolymod c1 = Checksum.longPolymod c2)
    (hwt : ((c1.zip c2).filter (fun p => p.1 ≠ p.2)).length ≤ 8) : c1 = c2 := by
  obtain ⟨qs, hq⟩ := telescope_long_forward c1
  obtain ⟨qs2, hq2⟩ := telescope_long_forward c2
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
  have hDlen : (List.zipWith Field.add c1.reverse c2.reverse).length ≤ 1023 := by
    simp [List.length_zipWith, List.length_reverse, hlen]
    omega
  have hvan : ∀ i < 8, evalF (pow gamma (1019 + i))
      (List.zipWith Field.add c1.reverse c2.reverse) = zero := by
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
    unfold initResidue at h1 h2
    have hpoly'' := congrArg (evalF (pow gamma (1019 + i))) hpoly'
    rw [h1, h2, hlen] at hpoly''
    have hce : evalF (pow gamma (1019 + i)) c1.reverse = evalF (pow gamma (1019 + i)) c2.reverse := by
      have h4 := congrArg (add (mul (pow (pow gamma (1019 + i)) c2.length)
          (evalF (pow gamma (1019 + i)) (unpack 15 36798899)))) hpoly''
      rw [add_cancel_left, add_cancel_left] at h4
      exact h4
    rw [evalF_zipAdd _ _ _ (by simp [List.length_reverse, hlen]), hce]
    exact add_self _
  have hzero := sparse_zero (List.zipWith Field.add c1.reverse c2.reverse) gamma 1023 1019
    gamma_ne_zero (fun a b ha hb h => gamma_inj_below ha hb h) hDwt hDlen hvan
  have hrev : c1.reverse = c2.reverse := by
    apply List.ext_getElem (by simp [List.length_reverse, hlen])
    intro j h1' h2'
    have hDj := hzero ((List.zipWith Field.add c1.reverse c2.reverse)[j]'(by
      simp [List.length_zipWith, List.length_reverse, hlen] at h1' h2' ⊢; omega)) (List.getElem_mem _)
    simp only [List.getElem_zipWith] at hDj
    exact (Field.add_eq_zero _ _).mp hDj
  exact List.reverse_inj.mp hrev

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


/-- A filtered list counts at most one element when all its members agree. -/
private theorem filter_const_length_le_one (l : List Nat) (a : Nat) (hnodup : l.Nodup)
    (h : ∀ x ∈ l, x = a) : l.length ≤ 1 := by
  cases l with
  | nil => simp
  | cons x xs =>
    have hx : x = a := h x (by simp)
    have hnotin : x ∉ xs := (List.nodup_cons.mp hnodup).1
    cases xs with
    | nil => simp
    | cons y ys =>
      have hy : y = a := h y (by simp)
      rw [hy, ← hx] at hnotin
      exact absurd List.mem_cons_self hnotin

/-- The filter/not-filter count split. -/
private theorem length_filter_split (l : List α) (p : α → Bool) :
    (l.filter p).length + (l.filter (fun a => !p a)).length = l.length := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    by_cases ha : p a = true
    · rw [List.filter_cons_of_pos ha, List.filter_cons_of_neg (by simp [ha])]
      simp only [List.length_cons]
      omega
    · rw [List.filter_cons_of_neg (by simp [ha]), List.filter_cons_of_pos (by simp [ha])]
      simp only [List.length_cons]
      omega

/-- A duplicate-free list of members of `E` is no longer than `E`. -/
private theorem nodup_length_le_of_all_mem (l E : List Nat) (hnodup : l.Nodup)
    (hmem : ∀ x ∈ l, x ∈ E) : l.length ≤ E.length := by
  induction E generalizing l with
  | nil =>
    have : l = [] := by
      cases l with
      | nil => rfl
      | cons x xs => exact absurd (hmem x (by simp)) (by simp)
    rw [this]
    exact Nat.le_refl _
  | cons e E' ih =>
    have hsplit : l.length = (l.filter (· == e)).length + (l.filter (fun x => !(x == e))).length :=
      (length_filter_split l (· == e)).symm
    have hle1 : (l.filter (· == e)).length ≤ 1 := by
      apply filter_const_length_le_one _ e
      · exact List.Sublist.nodup List.filter_sublist hnodup
      · intro x hx
        exact beq_iff_eq.mp (List.mem_filter.mp hx).2
    have hrest : (l.filter (fun x => !(x == e))).length ≤ E'.length := by
      apply ih (l.filter (fun x => !(x == e)))
      · exact List.Sublist.nodup List.filter_sublist hnodup
      · intro x hx
        have hxl := (List.mem_filter.mp hx).1
        have hxne : x ≠ e := by
          intro heq
          exact absurd ((List.mem_filter.mp hx).2) (by simp [heq])
        have hxe : x ∈ e :: E' := hmem x hxl
        rcases List.mem_cons.mp hxe with h | h
        · exact absurd h hxne
        · exact h
    have hlen : (e :: E').length = E'.length + 1 := by simp
    omega

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
  have hwt : ((c1.zip c2).filter (fun p => p.1 ≠ p.2)).length ≤ 8 := by
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
    have hle := nodup_length_le_of_all_mem _ _ (diffIndices_nodup _ _) hsub
    rw [List.length_append] at hle
    simp only [diffIndices_length] at hle
    rw [zip_filter_ne_length_comm c1 received] at hle
    omega
  exact regular_detection c1 c2 (by omega) hbound (by rw [hp1, hp2]) hwt

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
  have hwt : ((c1.zip c2).filter (fun p => p.1 ≠ p.2)).length ≤ 8 := by
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
    have hle := nodup_length_le_of_all_mem _ _ (diffIndices_nodup _ _) hsub
    rw [List.length_append] at hle
    simp only [diffIndices_length] at hle
    rw [zip_filter_ne_length_comm c1 received] at hle
    omega
  exact long_detection c1 c2 (by omega) hbound (by rw [hp1, hp2]) hwt

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
  have hwt : ((c1.zip c2).filter (fun p => p.1 ≠ p.2)).length ≤ 8 := by
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
    have hle := nodup_length_le_of_all_mem _ _ (diffIndices_nodup _ _) hsub
    rw [diffIndices_length] at hle
    omega
  exact regular_detection c1 c2 (by omega) hbound (by rw [hp1, hp2]) hwt

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
  have hwt : ((c1.zip c2).filter (fun p => p.1 ≠ p.2)).length ≤ 8 := by
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
    have hle := nodup_length_le_of_all_mem _ _ (diffIndices_nodup _ _) hsub
    rw [diffIndices_length] at hle
    omega
  exact long_detection c1 c2 (by omega) hbound (by rw [hp1, hp2]) hwt

end GF1024

end Codex32
