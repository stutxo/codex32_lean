import Codex32Proofs.Burst
import Codex32Proofs.Checksum
import Codex32Proofs.Uniform

/-!
Exact counts of valid strings. For every length `n ≥ 13` (regular) or
`n ≥ 15` (long), exactly `32^(n-13)` / `32^(n-15)` symbol strings have the
checksum residue: each prefix determines its tail uniquely (existence by the
constructor, uniqueness by the burst theorem). A uniformly random string is
therefore valid with probability exactly `2^-65` / `2^-75`, the exact form of
the BIP's "less than 3 in 10²⁰ / 10²³" failure-probability claims.
-/

namespace Codex32

open Field Poly Uniform

set_option maxHeartbeats 0

/-- A valid string of length at least thirteen is determined by its prefix:
two thirteen-symbol tails giving the same prefix a valid residue are equal. -/
theorem regular_tail_unique (p t1 t2 : List Symbol) (ht1 : t1.length = 13) (ht2 : t2.length = 13)
    (h1 : Checksum.regularPolymod (p ++ t1) = Checksum.regularConstant)
    (h2 : Checksum.regularPolymod (p ++ t2) = Checksum.regularConstant) : t1 = t2 := by
  have hburst := regular_burst (p ++ t1) (p ++ t2) (by simp [ht1, ht2]) (by rw [h1, h2])
    p.length 13 (by decide) (by simp [ht1])
    (by rw [List.take_left, List.take_left])
    (by rw [List.drop_eq_nil_of_le (by rw [List.length_append, ht1]; omega),
      List.drop_eq_nil_of_le (by rw [List.length_append, ht2]; omega)])
  exact List.append_cancel_left hburst

/-- A valid string of length at least fifteen is determined by its prefix. -/
theorem long_tail_unique (p t1 t2 : List Symbol) (ht1 : t1.length = 15) (ht2 : t2.length = 15)
    (h1 : Checksum.longPolymod (p ++ t1) = Checksum.longConstant)
    (h2 : Checksum.longPolymod (p ++ t2) = Checksum.longConstant) : t1 = t2 := by
  have hburst := long_burst (p ++ t1) (p ++ t2) (by simp [ht1, ht2]) (by rw [h1, h2])
    p.length 15 (by decide) (by simp [ht1])
    (by rw [List.take_left, List.take_left])
    (by rw [List.drop_eq_nil_of_le (by rw [List.length_append, ht1]; omega),
      List.drop_eq_nil_of_le (by rw [List.length_append, ht2]; omega)])
  exact List.append_cancel_left hburst

private theorem nodup_map_of_inj (l : List (List Symbol)) (f : List Symbol → List Symbol)
    (h : l.Nodup) (hinj : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) : (l.map f).Nodup := by
  apply List.pairwise_map.mpr
  exact h.imp_of_mem (fun ha hb hxy hfeq => hxy (hinj _ ha _ hb hfeq))

private theorem append_createRegular_inj (x y : List Symbol) (hlen : x.length = y.length)
    (h : x ++ Checksum.createRegular x = y ++ Checksum.createRegular y) : x = y := by
  have h1 := congrArg (List.take x.length) h
  rw [List.take_left, hlen, List.take_left] at h1
  exact h1

private theorem append_createLong_inj (x y : List Symbol) (hlen : x.length = y.length)
    (h : x ++ Checksum.createLong x = y ++ Checksum.createLong y) : x = y := by
  have h1 := congrArg (List.take x.length) h
  rw [List.take_left, hlen, List.take_left] at h1
  exact h1

/-- Exactly `32^(n-13)` strings of length `n` have the regular checksum
residue. -/
theorem regular_valid_count (n : Nat) (hn : 13 ≤ n) :
    ((Uniform.allWords n).filter (fun c =>
        decide (Checksum.regularPolymod c = Checksum.regularConstant))).length =
      32 ^ (n - 13) := by
  have hnodup1 : ((Uniform.allWords n).filter (fun c =>
        decide (Checksum.regularPolymod c = Checksum.regularConstant))).Nodup :=
    List.Sublist.nodup List.filter_sublist (Uniform.nodup_allWords n)
  have hnodup2 : ((Uniform.allWords (n - 13)).map fun p =>
        p ++ Checksum.createRegular p).Nodup :=
    nodup_map_of_inj _ _ (Uniform.nodup_allWords (n - 13)) (fun x hx y hy h =>
      append_createRegular_inj x y
        (by rw [(Uniform.mem_allWords _ x).mp hx, (Uniform.mem_allWords _ y).mp hy]) h)
  have hperm : ((Uniform.allWords n).filter (fun c =>
        decide (Checksum.regularPolymod c = Checksum.regularConstant))).Perm
      ((Uniform.allWords (n - 13)).map fun p => p ++ Checksum.createRegular p) := by
    apply (List.perm_ext_iff_of_nodup hnodup1 hnodup2).mpr
    intro c
    constructor
    · intro hc
      have hlen : c.length = n := (Uniform.mem_allWords n c).mp (List.mem_filter.mp hc).1
      have hp := (List.mem_filter.mp hc).2
      rw [decide_eq_true_eq] at hp
      refine List.mem_map.mpr ⟨c.take (n - 13), ?_, ?_⟩
      · apply (Uniform.mem_allWords (n - 13) _).mpr
        rw [List.length_take]
        omega
      · have htail : c.drop (n - 13) = Checksum.createRegular (c.take (n - 13)) := by
          apply regular_tail_unique (c.take (n - 13)) (c.drop (n - 13))
            (Checksum.createRegular (c.take (n - 13)))
          · rw [List.length_drop]
            omega
          · exact Checksum.createRegular_length _
          · rw [List.take_append_drop]
            exact hp
          · exact Checksum.regularPolymod_createRegular _
        rw [← htail, List.take_append_drop]
    · intro hc
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
      have hplen : p.length = n - 13 := (Uniform.mem_allWords (n - 13) p).mp hp
      apply List.mem_filter.mpr
      constructor
      · apply (Uniform.mem_allWords n _).mpr
        rw [List.length_append, hplen, Checksum.createRegular_length]
        omega
      · rw [decide_eq_true_eq]
        exact Checksum.regularPolymod_createRegular _
  have hlen := List.Perm.length_eq hperm
  rw [hlen, List.length_map, Uniform.length_allWords]

/-- Exactly `32^(n-15)` strings of length `n` have the long checksum residue. -/
theorem long_valid_count (n : Nat) (hn : 15 ≤ n) :
    ((Uniform.allWords n).filter (fun c =>
        decide (Checksum.longPolymod c = Checksum.longConstant))).length =
      32 ^ (n - 15) := by
  have hnodup1 : ((Uniform.allWords n).filter (fun c =>
        decide (Checksum.longPolymod c = Checksum.longConstant))).Nodup :=
    List.Sublist.nodup List.filter_sublist (Uniform.nodup_allWords n)
  have hnodup2 : ((Uniform.allWords (n - 15)).map fun p =>
        p ++ Checksum.createLong p).Nodup :=
    nodup_map_of_inj _ _ (Uniform.nodup_allWords (n - 15)) (fun x hx y hy h =>
      append_createLong_inj x y
        (by rw [(Uniform.mem_allWords _ x).mp hx, (Uniform.mem_allWords _ y).mp hy]) h)
  have hperm : ((Uniform.allWords n).filter (fun c =>
        decide (Checksum.longPolymod c = Checksum.longConstant))).Perm
      ((Uniform.allWords (n - 15)).map fun p => p ++ Checksum.createLong p) := by
    apply (List.perm_ext_iff_of_nodup hnodup1 hnodup2).mpr
    intro c
    constructor
    · intro hc
      have hlen : c.length = n := (Uniform.mem_allWords n c).mp (List.mem_filter.mp hc).1
      have hp := (List.mem_filter.mp hc).2
      rw [decide_eq_true_eq] at hp
      refine List.mem_map.mpr ⟨c.take (n - 15), ?_, ?_⟩
      · apply (Uniform.mem_allWords (n - 15) _).mpr
        rw [List.length_take]
        omega
      · have htail : c.drop (n - 15) = Checksum.createLong (c.take (n - 15)) := by
          apply long_tail_unique (c.take (n - 15)) (c.drop (n - 15))
            (Checksum.createLong (c.take (n - 15)))
          · rw [List.length_drop]
            omega
          · exact Checksum.createLong_length _
          · rw [List.take_append_drop]
            exact hp
          · exact Checksum.longPolymod_createLong _
        rw [← htail, List.take_append_drop]
    · intro hc
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
      have hplen : p.length = n - 15 := (Uniform.mem_allWords (n - 15) p).mp hp
      apply List.mem_filter.mpr
      constructor
      · apply (Uniform.mem_allWords n _).mpr
        rw [List.length_append, hplen, Checksum.createLong_length]
        omega
      · rw [decide_eq_true_eq]
        exact Checksum.longPolymod_createLong _
  have hlen := List.Perm.length_eq hperm
  rw [hlen, List.length_map, Uniform.length_allWords]

/-- The valid strings are exactly one `32^13`-th of all strings: a uniformly
random string passes regular checksum verification (is a valid codeword) with
probability exactly `2^-65 ≈ 2.7×10⁻²⁰` — the probability that a uniformly
random error goes undetected — below the BIP's "3 in 10²⁰" bound. -/
theorem regular_valid_fraction (n : Nat) (hn : 13 ≤ n) :
    (Uniform.allWords n).length =
      32 ^ 13 * ((Uniform.allWords n).filter (fun c =>
        decide (Checksum.regularPolymod c = Checksum.regularConstant))).length := by
  rw [regular_valid_count n hn, Uniform.length_allWords, ← Nat.pow_add]
  have h : 13 + (n - 13) = n := by omega
  rw [h]

/-- A uniformly random string passes long checksum verification (is a valid
codeword) with probability exactly `2^-75 ≈ 2.6×10⁻²³` — the probability that
a uniformly random error goes undetected — below the BIP's "3 in 10²³" bound. -/
theorem long_valid_fraction (n : Nat) (hn : 15 ≤ n) :
    (Uniform.allWords n).length =
      32 ^ 15 * ((Uniform.allWords n).filter (fun c =>
        decide (Checksum.longPolymod c = Checksum.longConstant))).length := by
  rw [long_valid_count n hn, Uniform.length_allWords, ← Nat.pow_add]
  have h : 15 + (n - 15) = n := by omega
  rw [h]

/-- The decimal form of the regular bound: `1/32^13 = 2⁻⁶⁵ < 3/10²⁰`. -/
theorem regular_failure_below_bip : 10 ^ 20 < 3 * 2 ^ 65 := by decide

/-- The decimal form of the long bound: `1/32^15 = 2⁻⁷⁵ < 3/10²³`. -/
theorem long_failure_below_bip : 10 ^ 23 < 3 * 2 ^ 75 := by decide

end Codex32
