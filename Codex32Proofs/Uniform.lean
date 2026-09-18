import Codex32Proofs.Field

/-!
Exact finite uniform sampling, expressed by lists of all possible entropy
matrices. Each matrix appears once. Permutation of the observation list gives
equality of every event count, with common denominator `32^(rows * cols)`.
This avoids an additional probability-library dependency.
-/

namespace Codex32.Uniform

set_option maxHeartbeats 0

/-- All words of a fixed length over a finite listed alphabet. -/
def allLists (alphabet : List α) : Nat → List (List α)
  | 0 => [[]]
  | n + 1 => alphabet.flatMap (fun a => (allLists alphabet n).map (a :: ·))

theorem mem_allLists (alphabet : List α) (n : Nat) (xs : List α) :
    xs ∈ allLists alphabet n ↔ xs.length = n ∧ ∀ x ∈ xs, x ∈ alphabet := by
  induction n generalizing xs with
  | zero => cases xs <;> simp [allLists]
  | succ n ih =>
    constructor
    · intro h
      obtain ⟨a, ha, htail⟩ := List.mem_flatMap.mp h
      obtain ⟨tails, ht, rfl⟩ := List.mem_map.mp htail
      obtain ⟨hlen, hall⟩ := (ih tails).mp ht
      refine ⟨by simp [hlen], ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ha
      · exact hall x hx
    · rintro ⟨hlen, hall⟩
      cases xs with
      | nil => simp at hlen
      | cons a tails =>
        apply List.mem_flatMap.mpr
        refine ⟨a, hall a (by simp), List.mem_map.mpr ⟨tails, ?_, rfl⟩⟩
        apply (ih tails).mpr
        exact ⟨by simpa using hlen, fun x hx => hall x (by simp [hx])⟩

theorem length_allLists (alphabet : List α) (n : Nat) :
    (allLists alphabet n).length = alphabet.length ^ n := by
  induction n with
  | zero => simp [allLists]
  | succ n ih =>
    simp [allLists, List.length_flatMap, ih, List.map_const', List.sum_replicate_nat,
      Nat.pow_succ, Nat.mul_comm]

theorem nodup_allLists (alphabet : List α) (distinct : alphabet.Nodup) (n : Nat) :
    (allLists alphabet n).Nodup := by
  induction n with
  | zero => simp [allLists]
  | succ n ih =>
    change List.Pairwise (· ≠ ·) (alphabet.flatMap _)
    apply List.pairwise_flatMap.mpr
    constructor
    · intro a ha
      apply List.pairwise_map.mpr
      exact ih.imp (by intro u v huv heq; exact huv (List.cons.inj heq).2)
    · apply distinct.imp
      intro a b hab xs hxs ys hys heq
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hxs
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hys
      exact hab (List.cons.inj heq).1

/-- All five-bit symbol words of length `n`. -/
def allWords (n : Nat) : List (List Symbol) := allLists (List.finRange 32) n

@[simp] theorem mem_allWords (n : Nat) (xs : List Symbol) :
    xs ∈ allWords n ↔ xs.length = n := by
  simp [allWords, mem_allLists]

@[simp] theorem length_allWords (n : Nat) : (allWords n).length = 32 ^ n := by
  simp [allWords, length_allLists]

theorem nodup_allWords (n : Nat) : (allWords n).Nodup :=
  nodup_allLists _ (List.nodup_finRange 32) n

/-- A rectangular entropy matrix; rows correspond to random shares. -/
def EntropyShape (rows cols : Nat) (e : List (List Symbol)) : Prop :=
  e.length = rows ∧ ∀ row ∈ e, row.length = cols

def allEntropy (rows cols : Nat) : List (List (List Symbol)) :=
  allLists (allWords cols) rows

@[simp] theorem mem_allEntropy (rows cols : Nat) (e : List (List Symbol)) :
    e ∈ allEntropy rows cols ↔ EntropyShape rows cols e := by
  simp [allEntropy, mem_allLists, EntropyShape]

@[simp] theorem length_allEntropy (rows cols : Nat) :
    (allEntropy rows cols).length = 32 ^ (rows * cols) := by
  rw [allEntropy, length_allLists, length_allWords, ← Nat.pow_mul, Nat.mul_comm]

theorem nodup_allEntropy (rows cols : Nat) : (allEntropy rows cols).Nodup :=
  nodup_allLists _ (nodup_allWords cols) rows

/-- Coordinatewise characteristic-two translation of a word. -/
def translateWords (mask xs : List Symbol) : List Symbol :=
  List.zipWith Field.add mask xs

theorem translateWords_length (mask xs : List Symbol) (hlen : mask.length = xs.length) :
    (translateWords mask xs).length = xs.length := by
  simp [translateWords, List.length_zipWith, hlen]

theorem translateWords_involutive (mask xs : List Symbol)
    (hlen : mask.length = xs.length) :
    translateWords mask (translateWords mask xs) = xs := by
  induction mask generalizing xs with
  | nil => cases xs <;> simp_all [translateWords]
  | cons m ms ih =>
    cases xs with
    | nil => simp at hlen
    | cons x xs =>
      simp only [translateWords, List.zipWith_cons_cons, Field.add_cancel_left]
      exact congrArg (x :: ·) (ih xs (by simpa using hlen))

/-- Coordinatewise translation of an entropy matrix. -/
def translateEntropy (masks e : List (List Symbol)) : List (List Symbol) :=
  List.zipWith translateWords masks e

theorem translateEntropy_shape (rows cols : Nat) (masks e : List (List Symbol))
    (hm : EntropyShape rows cols masks) (he : EntropyShape rows cols e) :
    EntropyShape rows cols (translateEntropy masks e) := by
  constructor
  · simp [translateEntropy, List.length_zipWith, hm.1, he.1]
  · intro row hrow
    rw [translateEntropy, ← List.map_uncurry_zip_eq_zipWith] at hrow
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hrow
    obtain ⟨hpm, hpe⟩ := List.of_mem_zip hp
    change (translateWords p.1 p.2).length = cols
    rw [translateWords_length _ _ ((hm.2 _ hpm).trans (he.2 _ hpe).symm), he.2 _ hpe]

theorem translateEntropy_involutive (rows cols : Nat) (masks e : List (List Symbol))
    (hm : EntropyShape rows cols masks) (he : EntropyShape rows cols e) :
    translateEntropy masks (translateEntropy masks e) = e := by
  have ht := translateEntropy_shape rows cols masks e hm he
  apply List.ext_getElem (by
    simp only [translateEntropy, List.length_zipWith, hm.1, he.1, Nat.min_self])
  intro i hi hj
  simp only [translateEntropy, List.getElem_zipWith]
  apply translateWords_involutive
  exact (hm.2 _ (List.getElem_mem _)).trans (he.2 _ (List.getElem_mem _)).symm

/-- A support-preserving involution permutes a duplicate-free finite sample
space. No assumption about the size of that sample space is needed. -/
theorem map_perm_of_involution (support : List α) (f : α → α)
    (distinct : support.Nodup)
    (closed : ∀ x ∈ support, f x ∈ support)
    (involutive : ∀ x ∈ support, f (f x) = x) :
    (support.map f).Perm support := by
  have hmap : (support.map f).Nodup := by
    apply List.pairwise_map.mpr
    apply distinct.imp_of_mem
    intro a b ha hb hab heq
    apply hab
    rw [← involutive a ha, ← involutive b hb, heq]
  apply (List.perm_ext_iff_of_nodup hmap distinct).mpr
  intro x
  constructor
  · intro hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    exact closed a ha
  · intro hx
    exact List.mem_map.mpr ⟨f x, closed x hx, involutive x hx⟩

theorem translateWords_perm (n : Nat) (mask : List Symbol) (hlen : mask.length = n) :
    ((allWords n).map (translateWords mask)).Perm (allWords n) := by
  apply map_perm_of_involution _ _ (nodup_allWords n)
  · intro xs hx
    apply (mem_allWords n _).mpr
    rw [translateWords_length _ _ (hlen.trans ((mem_allWords n xs).mp hx).symm)]
    exact (mem_allWords n xs).mp hx
  · intro xs hx
    exact translateWords_involutive mask xs (hlen.trans ((mem_allWords n xs).mp hx).symm)

theorem translateEntropy_perm (rows cols : Nat) (masks : List (List Symbol))
    (hm : EntropyShape rows cols masks) :
    ((allEntropy rows cols).map (translateEntropy masks)).Perm (allEntropy rows cols) := by
  apply map_perm_of_involution _ _ (nodup_allEntropy rows cols)
  · intro e he
    exact (mem_allEntropy rows cols _).mpr
      (translateEntropy_shape rows cols masks e hm ((mem_allEntropy rows cols e).mp he))
  · intro e he
    exact translateEntropy_involutive rows cols masks e hm ((mem_allEntropy rows cols e).mp he)

/-- Exact equality in distribution under independently uniform symbols: the
two observation lists contain every possible outcome with the same multiplicity.
The observations can have any type, without a decidable-equality requirement. -/
theorem observations_perm (rows cols : Nat) (masks : List (List Symbol))
    (hm : EntropyShape rows cols masks)
    (observeA observeB : List (List Symbol) → α)
    (agree : ∀ e, EntropyShape rows cols e →
      observeA (translateEntropy masks e) = observeB e) :
    ((allEntropy rows cols).map observeA).Perm ((allEntropy rows cols).map observeB) := by
  have hp := (translateEntropy_perm rows cols masks hm).map observeA
  have hmap : ((allEntropy rows cols).map (translateEntropy masks)).map observeA =
      (allEntropy rows cols).map observeB := by
    rw [List.map_map]
    apply List.map_congr_left
    intro e he
    exact agree e ((mem_allEntropy rows cols e).mp he)
  rw [hmap] at hp
  exact hp.symm

/-- Equality of the numerator of every Boolean event probability. Both sides
have the same positive finite sample-space denominator `32^(rows * cols)`. -/
theorem observations_countP_eq (rows cols : Nat) (masks : List (List Symbol))
    (hm : EntropyShape rows cols masks)
    (observeA observeB : List (List Symbol) → α)
    (agree : ∀ e, EntropyShape rows cols e →
      observeA (translateEntropy masks e) = observeB e) (event : α → Bool) :
    ((allEntropy rows cols).map observeA).countP event =
      ((allEntropy rows cols).map observeB).countP event :=
  (observations_perm rows cols masks hm observeA observeB agree).countP_eq event

end Codex32.Uniform
