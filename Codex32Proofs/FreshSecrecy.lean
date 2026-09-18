import Codex32Proofs.Secrecy
import Codex32Proofs.SecrecyPayload

/-!
Perfect secrecy for the actual fresh-share initializer. Under uniform,
independent full-symbol entropy, every desired secret payload has exactly the
same joint count with every event on fewer-than-threshold observed messages.
The secret payload includes padding; metadata and the observation indices are
held fixed. The result includes successful initialization and validation.
-/

namespace Codex32.Secrecy

open Proofs

set_option maxHeartbeats 0

/-- Run fresh initialization and validation, then expose the recovered secret
payload and the selected complete share messages. -/
def observeFresh (threshold : Threshold) (identifier : Identifier)
    (entropy : List (List Symbol)) (observed : List Symbol) :
    Except Error (List Symbol × List Message) := do
  let messages ← Shares.initializeFresh threshold identifier entropy
  let checked ← Shares.validate messages
  pure ((checked.interpolate 16).payload, observed.map checked.interpolate)

/-- Joint event: the recovered secret equals the requested payload and the
observed messages satisfy an arbitrary Boolean predicate. -/
def freshEvent (secret : List Symbol) (event : List Message → Bool) :
    Except Error (List Symbol × List Message) → Bool
  | .error _ => false
  | .ok (payload, views) => (payload == secret) && event views

private theorem observeFresh_of_valid (threshold : Threshold) (identifier : Identifier)
    (entropy : List (List Symbol)) (observed : List Symbol) (checked : Shares.ValidatedShareSet)
    (initialized : Shares.initializeFresh threshold identifier entropy = .ok checked.messages)
    (validated : Shares.validate checked.messages = .ok checked) :
    observeFresh threshold identifier entropy observed =
      .ok ((checked.interpolate 16).payload, observed.map checked.interpolate) := by
  rw [observeFresh, initialized]
  change (do
    let source ← Shares.validate checked.messages
    pure ((source.interpolate 16).payload, observed.map source.interpolate)) = _
  rw [validated]
  rfl

private theorem translateWords_between (s t : List Symbol) (length : s.length = t.length) :
    Uniform.translateWords (List.zipWith Field.add s t) s = t := by
  induction s generalizing t with
  | nil => cases t <;> simp_all [Uniform.translateWords]
  | cons a s ih =>
    cases t with
    | nil => simp at length
    | cons b t =>
      simp only [Uniform.translateWords, List.zipWith_cons_cons]
      rw [Field.add_comm (Field.add a b) a, Field.add_cancel_left]
      exact congrArg (b :: ·) (ih t (by simpa using length))

private theorem translateWords_between_beq (s t payload : List Symbol)
    (length : s.length = t.length) (payloadLength : payload.length = s.length) :
    (Uniform.translateWords (List.zipWith Field.add s t) payload == t) = (payload == s) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  have maskLength : (List.zipWith Field.add s t).length = s.length := by
    simp [List.length_zipWith, ← length]
  constructor
  · intro h
    have h' := congrArg (Uniform.translateWords (List.zipWith Field.add s t)) h
    rw [Uniform.translateWords_involutive _ _ (maskLength.trans payloadLength.symm)] at h'
    have back : Uniform.translateWords (List.zipWith Field.add s t) t = s := by
      calc
        _ = Uniform.translateWords (List.zipWith Field.add s t)
            (Uniform.translateWords (List.zipWith Field.add s t) s) :=
          congrArg (Uniform.translateWords (List.zipWith Field.add s t))
            (translateWords_between s t length).symm
        _ = s := Uniform.translateWords_involutive _ _ maskLength
    exact h'.trans back
  · intro h
    rw [h]
    exact translateWords_between s t length

/-- The same source-column translation used for secrecy translates the
recovered secret payload by the mask's values at the secret index. -/
theorem checked_secret_translated (a b : Shares.ValidatedShareSet)
    (observed : List Symbol) (deltas : List Symbol)
    (length : a.first.payload.length = b.first.payload.length)
    (deltaLength : deltas.length = a.first.payload.length)
    (fewObserved : observed.length < a.messages.length)
    (shift : ∀ j, j < a.first.payload.length →
      messageColumn b.messages j =
        Field.shiftSamples (Field.secrecyMask 16 (deltas[j]?.getD 0) observed)
          (messageColumn a.messages j)) :
    (b.interpolate 16).payload =
      Uniform.translateWords deltas (a.interpolate 16).payload := by
  apply List.ext_getElem
  · simp only [checked_interpolate_length, Uniform.translateWords,
      List.length_zipWith, deltaLength, Nat.min_self, length]
  · intro j hb ht
    have jb : j < b.first.payload.length := by
      simpa only [checked_interpolate_length] using hb
    have ja : j < a.first.payload.length := by omega
    have jd : j < deltas.length := by omega
    have hap : j < (a.interpolate 16).payload.length := by
      simpa only [checked_interpolate_length] using ja
    have h := Field.interpolate_shift_secrecyMask_secret
      (messageColumn a.messages j)
      (by simpa only [messageColumn_indices] using a.distinctIndices)
      16 (deltas[j]?.getD 0) observed
      (by simpa only [messageColumn_length] using fewObserved)
    rw [← shift j ja, ← checked_interpolate_column a 16 j ja,
      ← checked_interpolate_column b 16 j jb] at h
    simp only [List.getElem?_eq_getElem hb, List.getElem?_eq_getElem hap,
      List.getElem?_eq_getElem jd, Option.getD_some] at h
    simp only [Uniform.translateWords, List.getElem_zipWith]
    exact h.trans (Field.add_comm _ _)

/-- Every well-shaped fresh entropy matrix successfully initializes and
validates. Its recovered secret retains the prescribed payload length. -/
theorem observeFresh_success (threshold : Threshold) (identifier : Identifier)
    (length : Nat) (nonzero : threshold.count ≠ 0)
    (supported : length ∈ Seed.supportedPayloadLengths)
    (entropy : List (List Symbol)) (shape : Uniform.EntropyShape threshold.count length entropy)
    (observed : List Symbol) :
    ∃ payload views, observeFresh threshold identifier entropy observed = .ok (payload, views) ∧
      payload.length = length := by
  obtain ⟨checked, initialized, validated, dataList, firstThreshold, firstIdentifier, firstLength⟩ :=
    initializeFresh_valid threshold identifier entropy length nonzero shape.1 supported shape.2
  refine ⟨(checked.interpolate 16).payload, observed.map checked.interpolate, ?_, ?_⟩
  · exact observeFresh_of_valid threshold identifier entropy observed checked initialized validated
  · rw [checked_interpolate_length, firstLength]

/-- Mask translation preserves the views and exchanges any two candidate
secret payloads in the corresponding joint event. -/
theorem fresh_event_translation (threshold : Threshold) (identifier : Identifier)
    (s t : List Symbol) (sameLength : s.length = t.length)
    (nonzero : threshold.count ≠ 0)
    (supported : s.length ∈ Seed.supportedPayloadLengths)
    (observed : List Symbol) (secretNotObserved : (16 : Symbol) ∉ observed)
    (fewObserved : observed.length < threshold.count)
    (entropy : List (List Symbol))
    (shape : Uniform.EntropyShape threshold.count s.length entropy)
    (event : List Message → Bool) :
    freshEvent t event (observeFresh threshold identifier
      (Uniform.translateEntropy (masks s t observed threshold.count) entropy) observed) =
      freshEvent s event (observeFresh threshold identifier entropy observed) := by
  have maskShape := masks_shape s t observed threshold.count sameLength
    (threshold_count_le_nine threshold)
  have shiftedShape := Uniform.translateEntropy_shape threshold.count s.length _ _ maskShape shape
  obtain ⟨a, initA, validA, dataA, thresholdA, identifierA, lengthA⟩ :=
    initializeFresh_valid threshold identifier entropy s.length nonzero shape.1 supported shape.2
  obtain ⟨b, initB, validB, dataB, thresholdB, identifierB, lengthB⟩ :=
    initializeFresh_valid threshold identifier _ s.length nonzero shiftedShape.1 supported shiftedShape.2
  have sourceCount : a.messages.length = threshold.count := by
    rw [a.exactCount, thresholdA]
  have shift : ∀ j, j < a.first.payload.length →
      messageColumn b.messages j =
        Field.shiftSamples
          (Field.secrecyMask 16 (Field.add (s[j]?.getD 0) (t[j]?.getD 0)) observed)
          (messageColumn a.messages j) := by
    intro j hj
    rw [messageColumn_data, messageColumn_data, dataA, dataB]
    exact column_shift_tail s t observed threshold.count entropy shape
      (threshold_count_le_nine threshold) sameLength j (by omega)
  have views := checked_observations_equal a b observed
    (fun j => Field.add (s[j]?.getD 0) (t[j]?.getD 0))
    (thresholdA.trans thresholdB.symm) (identifierA.trans identifierB.symm)
    (lengthA.trans lengthB.symm) secretNotObserved (by omega) shift
  have secret := checked_secret_translated a b observed (List.zipWith Field.add s t)
    (lengthA.trans lengthB.symm)
    (by simp only [List.length_zipWith, ← sameLength, Nat.min_self, lengthA])
    (by omega) (by
      intro j hj
      have hs : j < s.length := by omega
      have ht : j < t.length := by omega
      simpa only [List.getElem?_zipWith, List.getElem?_eq_getElem hs,
        List.getElem?_eq_getElem ht, Option.getD_some] using shift j hj)
  rw [observeFresh_of_valid threshold identifier entropy observed a initA validA,
    observeFresh_of_valid threshold identifier _ observed b initB validB]
  simp only [freshEvent]
  rw [views, secret, translateWords_between_beq s t _ sameLength]
  rw [checked_interpolate_length, lengthA]

/-- Exact joint-count symmetry for fresh initialization: under independently
uniform full-symbol entropy, every candidate secret payload has the same
number of outcomes for every event on messages observed at a list of fewer
than `threshold.count` nonsecret indices. Duplicate indices are allowed and
count toward the list-length bound. The common sample-space denominator is
`32^(threshold.count * s.length)`. -/
theorem initializeFresh_secrecy (threshold : Threshold) (identifier : Identifier)
    (s t : List Symbol) (sameLength : s.length = t.length)
    (nonzero : threshold.count ≠ 0)
    (supported : s.length ∈ Seed.supportedPayloadLengths)
    (observed : List Symbol)
    (secretNotObserved : (16 : Symbol) ∉ observed)
    (fewObserved : observed.length < threshold.count) (event : List Message → Bool) :
    ((Uniform.allEntropy threshold.count s.length).map
      (fun entropy => observeFresh threshold identifier entropy observed)).countP (freshEvent s event) =
    ((Uniform.allEntropy threshold.count s.length).map
      (fun entropy => observeFresh threshold identifier entropy observed)).countP (freshEvent t event) := by
  have h := Uniform.observations_countP_eq threshold.count s.length
    (masks s t observed threshold.count)
    (masks_shape s t observed threshold.count sameLength (threshold_count_le_nine threshold))
    (fun entropy => freshEvent t event (observeFresh threshold identifier entropy observed))
    (fun entropy => freshEvent s event (observeFresh threshold identifier entropy observed))
    (fun entropy shape => fresh_event_translation threshold identifier s t sameLength nonzero
      supported observed secretNotObserved fewObserved entropy shape event) id
  simpa only [List.countP_map, Function.comp_def, id_eq] using h.symm

end Codex32.Secrecy
