import Codex32Proofs.SecrecyPayload

/-!
Perfect secrecy for complete messages produced by the sharing APIs. Randomness
is modeled by a finite uniform product of GF(32) symbols, including padding.
The statements compare exact outcome multiplicities, so they apply to every
event on the observed messages, not merely to individual payload coordinates.
-/

namespace Codex32.Secrecy

open Proofs

set_option maxHeartbeats 0

private theorem message_ext (a b : Message) (threshold : a.threshold = b.threshold)
    (identifier : a.identifier = b.identifier) (index : a.index = b.index)
    (payload : a.payload = b.payload) : a = b := by
  cases a
  cases b
  cases threshold
  cases identifier
  cases index
  cases payload
  rfl

/-- Complete public existing-secret initialization followed by checked share
evaluation. Errors remain part of the observation type. -/
def observeExisting (secret : Message) (entropy : List (List Symbol))
    (observed : List Symbol) : Except Error (List Message) := do
  let messages ← Shares.initializeExisting secret entropy
  let checked ← Shares.validate messages
  pure (observed.map checked.interpolate)

theorem messageColumn_data (messages : List Message) (j : Nat) :
    messageColumn messages j = column (messages.map fun m => (m.index, m.payload)) j := by
  simp only [messageColumn, column, List.map_map, Function.comp_def]

private theorem observeExisting_of_valid (secret : Message) (entropy : List (List Symbol))
    (observed : List Symbol) (checked : Shares.ValidatedShareSet)
    (initialized : Shares.initializeExisting secret entropy = .ok checked.messages)
    (validated : Shares.validate checked.messages = .ok checked) :
    observeExisting secret entropy observed = .ok (observed.map checked.interpolate) := by
  rw [observeExisting, initialized]
  change (do
    let source ← Shares.validate checked.messages
    pure (observed.map source.interpolate)) = .ok (observed.map checked.interpolate)
  rw [validated]
  rfl

theorem threshold_count_le_nine (threshold : Threshold) : threshold.count ≤ 9 := by
  cases threshold with
  | unshared => simp [Threshold.count]
  | shared k => have := k.isLt; simp [Threshold.count]; omega

/-- Translating every source column by a below-threshold mask leaves the full
messages at the observed indices unchanged. -/
theorem checked_observations_equal (a b : Shares.ValidatedShareSet)
    (observed : List Symbol) (delta : Nat → Symbol)
    (threshold : a.first.threshold = b.first.threshold)
    (identifier : a.first.identifier = b.first.identifier)
    (length : a.first.payload.length = b.first.payload.length)
    (secretNotObserved : (16 : Symbol) ∉ observed)
    (fewObserved : observed.length < a.messages.length)
    (shift : ∀ j, j < a.first.payload.length →
      messageColumn b.messages j =
        Field.shiftSamples (Field.secrecyMask 16 (delta j) observed)
          (messageColumn a.messages j)) :
    observed.map b.interpolate = observed.map a.interpolate := by
  apply List.map_congr_left
  intro x hx
  apply message_ext
  · simp only [checked_interpolate_threshold, threshold]
  · simp only [checked_interpolate_identifier, identifier]
  · simp only [checked_interpolate_index]
  · apply List.ext_getElem
    · simp only [checked_interpolate_length, length]
    · intro j hb ha
      have ja : j < a.first.payload.length := by
        simpa only [checked_interpolate_length] using ha
      have jb : j < b.first.payload.length := by omega
      have h := Field.interpolate_shift_secrecyMask_observed
        (messageColumn a.messages j)
        (by simpa only [messageColumn_indices] using a.distinctIndices)
        16 (delta j) observed secretNotObserved
        (by simpa only [messageColumn_length] using fewObserved) x hx
      rw [← shift j ja, ← checked_interpolate_column a x j ja,
        ← checked_interpolate_column b x j jb] at h
      simpa only [List.getElem?_eq_getElem ha, List.getElem?_eq_getElem hb,
        Option.getD_some] using h

/-- A bijective change of random inputs makes two supplied secrets produce
exactly the same complete observed messages. Initialization and validation
succeed from the stated input conditions, rather than being assumed. -/
theorem initializeExisting_observations_shift (secret replacement : Message)
    (observed : List Symbol) (entropy : List (List Symbol))
    (secretIndex : secret.index = 16) (replacementIndex : replacement.index = 16)
    (nonzero : secret.threshold.count ≠ 0)
    (threshold : secret.threshold = replacement.threshold)
    (identifier : secret.identifier = replacement.identifier)
    (length : secret.payload.length = replacement.payload.length)
    (secretNotObserved : (16 : Symbol) ∉ observed)
    (fewObserved : observed.length < secret.threshold.count)
    (shape : Uniform.EntropyShape (secret.threshold.count - 1) secret.payload.length entropy) :
    observeExisting replacement
      (Uniform.translateEntropy
        (masks secret.payload replacement.payload observed (secret.threshold.count - 1)) entropy)
      observed = observeExisting secret entropy observed := by
  have enough : secret.threshold.count - 1 ≤ 9 := by
    have := threshold_count_le_nine secret.threshold
    omega
  have shiftedShape := Uniform.translateEntropy_shape
    (secret.threshold.count - 1) secret.payload.length
    (masks secret.payload replacement.payload observed (secret.threshold.count - 1)) entropy
    (masks_shape secret.payload replacement.payload observed _ length enough) shape
  obtain ⟨a, initializedA, validatedA, firstA, dataA⟩ :=
    initializeExisting_valid secret entropy secretIndex nonzero
      (by have := shape.1; omega) shape.2
  obtain ⟨b, initializedB, validatedB, firstB, dataB⟩ :=
    initializeExisting_valid replacement _ replacementIndex
      (by simpa only [← threshold] using nonzero)
      (by rw [← threshold]; have := shiftedShape.1; omega)
      (fun p hp => (shiftedShape.2 p hp).trans length)
  rw [observeExisting_of_valid secret entropy observed a initializedA validatedA,
    observeExisting_of_valid replacement _ observed b initializedB validatedB]
  congr 1
  apply checked_observations_equal a b observed
    (fun j => Field.add (secret.payload[j]?.getD 0) (replacement.payload[j]?.getD 0))
    (by simpa only [firstA, firstB] using threshold)
    (by simpa only [firstA, firstB] using identifier)
    (by simpa only [firstA, firstB] using length) secretNotObserved
    (by simpa only [a.exactCount, firstA] using fewObserved)
  intro j hj
  rw [messageColumn_data, messageColumn_data, dataA, dataB]
  exact column_shift secret.payload replacement.payload observed _ entropy shape enough length j
    (by simpa only [firstA] using hj)

/-- Perfect secrecy for the actual existing-secret sharing API: for any two
secrets with identical public metadata and payload length, fewer than `k`
nonsecret shares have exactly the same distribution under `k-1` independently
uniform full-symbol random payloads. The outcome includes every message field
and all padding symbols; observations may include initial random-share indices.
No hypothesis about successful initialization or validation is required. -/
theorem initializeExisting_secrecy (secret replacement : Message)
    (observed : List Symbol)
    (secretIndex : secret.index = 16) (replacementIndex : replacement.index = 16)
    (nonzero : secret.threshold.count ≠ 0)
    (threshold : secret.threshold = replacement.threshold)
    (identifier : secret.identifier = replacement.identifier)
    (length : secret.payload.length = replacement.payload.length)
    (secretNotObserved : (16 : Symbol) ∉ observed)
    (fewObserved : observed.length < secret.threshold.count) :
    ((Uniform.allEntropy (secret.threshold.count - 1) secret.payload.length).map
      (fun entropy => observeExisting secret entropy observed)).Perm
    ((Uniform.allEntropy (secret.threshold.count - 1) secret.payload.length).map
      (fun entropy => observeExisting replacement entropy observed)) := by
  apply List.Perm.symm
  apply Uniform.observations_perm _ _
    (masks secret.payload replacement.payload observed (secret.threshold.count - 1))
    (masks_shape secret.payload replacement.payload observed _ length (by
      have := threshold_count_le_nine secret.threshold; omega))
  intro entropy shape
  exact initializeExisting_observations_shift secret replacement observed entropy
    secretIndex replacementIndex nonzero threshold identifier length secretNotObserved
    fewObserved shape

/-- Every event on the complete observed messages has the same probability
for either supplied secret: these equal numerators share the positive
denominator `32^((k-1)*payloadLength)`. -/
theorem initializeExisting_secrecy_event (secret replacement : Message)
    (observed : List Symbol)
    (secretIndex : secret.index = 16) (replacementIndex : replacement.index = 16)
    (nonzero : secret.threshold.count ≠ 0)
    (threshold : secret.threshold = replacement.threshold)
    (identifier : secret.identifier = replacement.identifier)
    (length : secret.payload.length = replacement.payload.length)
    (secretNotObserved : (16 : Symbol) ∉ observed)
    (fewObserved : observed.length < secret.threshold.count)
    (event : Except Error (List Message) → Bool) :
    ((Uniform.allEntropy (secret.threshold.count - 1) secret.payload.length).map
      (fun entropy => observeExisting secret entropy observed)).countP event =
    ((Uniform.allEntropy (secret.threshold.count - 1) secret.payload.length).map
      (fun entropy => observeExisting replacement entropy observed)).countP event :=
  (initializeExisting_secrecy secret replacement observed secretIndex replacementIndex
    nonzero threshold identifier length secretNotObserved fewObserved).countP_eq event

end Codex32.Secrecy
