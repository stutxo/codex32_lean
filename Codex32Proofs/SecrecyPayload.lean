import Codex32Proofs.Initialization
import Codex32Proofs.SecrecyAlgebra
import Codex32Proofs.Uniform

/-! Coordinate-wise payload translation for the secrecy proof. -/

namespace Codex32.Secrecy

set_option maxHeartbeats 0

/-- One payload column of indexed source rows. The default is immaterial for
the bounded columns used in the secrecy theorems. -/
def column (sources : List (Symbol × List Symbol)) (j : Nat) : List (Symbol × Symbol) :=
  sources.map fun p => (p.1, p.2[j]?.getD 0)

/-- Evaluate the secret-changing mask at every fixed initial share index,
independently in each payload column. -/
def masks (secret replacement : List Symbol) (observed : List Symbol) (rows : Nat) :
    List (List Symbol) :=
  (Proofs.initialIndices.take rows).map fun i =>
    (List.zipWith Field.add secret replacement).map fun delta =>
      Field.secrecyMask 16 delta observed i

private theorem zipWith_column (left right : List Symbol) (j : Nat)
    (leftBound : j < left.length) (rightBound : j < right.length) :
    (List.zipWith Field.add left right)[j]?.getD 0 =
      Field.add (left[j]?.getD 0) (right[j]?.getD 0) := by
  simp [List.getElem?_zipWith, List.getElem?_eq_getElem leftBound,
    List.getElem?_eq_getElem rightBound]

private theorem mask_column (deltas : List Symbol) (observed : List Symbol)
    (index : Symbol) (j : Nat) (bound : j < deltas.length) :
    (deltas.map (fun delta => Field.secrecyMask 16 delta observed index))[j]?.getD 0 =
      Field.secrecyMask 16 (deltas[j]?.getD 0) observed index := by
  simp [List.getElem?_map, List.getElem?_eq_getElem bound]

private theorem column_translate_by (indices : List Symbol)
    (entropy : List (List Symbol)) (deltas : List Symbol) (observed : List Symbol)
    (j : Nat) (enough : entropy.length ≤ indices.length)
    (lengths : ∀ row ∈ entropy, row.length = deltas.length) (bound : j < deltas.length) :
    column (indices.zip (List.zipWith (List.zipWith Field.add)
      ((indices.take entropy.length).map fun i =>
        deltas.map fun delta => Field.secrecyMask 16 delta observed i) entropy)) j =
      Field.shiftSamples (Field.secrecyMask 16 (deltas[j]?.getD 0) observed)
        (column (indices.zip entropy) j) := by
  induction entropy generalizing indices with
  | nil => simp [column, Field.shiftSamples]
  | cons row rest ih =>
    cases indices with
    | nil => simp at enough
    | cons index indices =>
      have rowLength := lengths row (by simp)
      have rowBound : j < row.length := by omega
      have maskBound : j < (deltas.map (fun delta =>
          Field.secrecyMask 16 delta observed index)).length := by simpa using bound
      have tail := ih indices (by simp only [List.length_cons] at enough; omega)
        (fun other member => lengths other (by simp [member]))
      simp only [List.length_cons, List.take_succ_cons, List.map_cons,
        List.zipWith_cons_cons, List.zip_cons_cons, column, List.map_cons,
        Field.shiftSamples] at tail ⊢
      rw [zipWith_column _ row j maskBound rowBound,
        mask_column deltas observed index j bound, Field.add_comm]
      congr 1

/-- The fixed-index masks have the same rectangular shape as the entropy
matrix whenever both secret payloads have the same length. -/
theorem masks_shape (secret replacement : List Symbol) (observed : List Symbol)
    (rows : Nat) (sameLength : secret.length = replacement.length) (enough : rows ≤ 9) :
    Uniform.EntropyShape rows secret.length (masks secret replacement observed rows) := by
  constructor
  · simp only [masks, List.length_map, List.length_take]
    have length : Proofs.initialIndices.length = 9 := rfl
    rw [length, Nat.min_eq_left enough]
  · intro row member
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
    simp only [List.length_map, List.length_zipWith, ← sameLength, Nat.min_self]

/-- Translating the random payload rows translates each source column by the
corresponding secrecy polynomial. This tail-only form also covers fresh
initialization, where every initial source row is random. -/
theorem column_shift_tail (secret replacement : List Symbol) (observed : List Symbol)
    (rows : Nat) (entropy : List (List Symbol))
    (shape : Uniform.EntropyShape rows secret.length entropy)
    (enough : rows ≤ 9) (sameLength : secret.length = replacement.length)
    (j : Nat) (bound : j < secret.length) :
    column (Proofs.initialIndices.zip
      (Uniform.translateEntropy (masks secret replacement observed rows) entropy)) j =
      Field.shiftSamples
        (Field.secrecyMask 16 (Field.add (secret[j]?.getD 0) (replacement[j]?.getD 0)) observed)
        (column (Proofs.initialIndices.zip entropy) j) := by
  have replacementBound : j < replacement.length := by omega
  have deltaLength : (List.zipWith Field.add secret replacement).length = secret.length := by
    simp only [List.length_zipWith, ← sameLength, Nat.min_self]
  have shifted := column_translate_by Proofs.initialIndices entropy
    (List.zipWith Field.add secret replacement) observed j
    (by rw [shape.1]; exact enough)
    (fun row member => (shape.2 row member).trans deltaLength.symm)
    (by rw [deltaLength]; exact bound)
  have translateEq : Uniform.translateWords = List.zipWith Field.add := rfl
  simpa only [masks, Uniform.translateEntropy, translateEq, shape.1,
    zipWith_column secret replacement j bound replacementBound] using shifted

/-- Changing the supplied secret and translating the random entropy rows is
exactly polynomial-mask translation in each bounded source column. -/
theorem column_shift (secret replacement : List Symbol) (observed : List Symbol)
    (rows : Nat) (entropy : List (List Symbol))
    (shape : Uniform.EntropyShape rows secret.length entropy)
    (enough : rows ≤ 9) (sameLength : secret.length = replacement.length)
    (j : Nat) (bound : j < secret.length) :
    column ((16, replacement) :: Proofs.initialIndices.zip
      (Uniform.translateEntropy (masks secret replacement observed rows) entropy)) j =
      Field.shiftSamples
        (Field.secrecyMask 16 (Field.add (secret[j]?.getD 0) (replacement[j]?.getD 0)) observed)
        (column ((16, secret) :: Proofs.initialIndices.zip entropy) j) := by
  change (16, replacement[j]?.getD 0) :: column _ j =
    Field.shiftSamples
      (Field.secrecyMask 16 (Field.add (secret[j]?.getD 0) (replacement[j]?.getD 0)) observed)
      ((16, secret[j]?.getD 0) :: column _ j)
  rw [Field.shiftSamples_change_secret,
    column_shift_tail secret replacement observed rows entropy shape enough sameLength j bound]

end Codex32.Secrecy
