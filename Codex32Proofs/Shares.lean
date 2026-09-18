import Codex32.Shares

/-! Initial share proofs, kept separate from executable code.
All finite calculations below use the kernel's `decide`, never native evaluation.
The two-share algebra theorem is exhaustive over arbitrary symbol values; it is
not restricted to a test vector. Arbitrary-threshold recovery is proved in
`Codex32Proofs.ShareRecovery`, using the scalar algebra in `Codex32Proofs.Recovery`.
-/

namespace Codex32.Proofs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Messages are equal when their public data fields agree. -/
theorem message_ext (a b : Message) (threshold : a.threshold = b.threshold)
    (identifier : a.identifier = b.identifier) (index : a.index = b.index)
    (payload : a.payload = b.payload) : a = b := by
  cases a
  cases b
  cases threshold
  cases identifier
  cases index
  cases payload
  rfl

/-- Revalidating a checked set returns the same checked set. -/
theorem validate_checked (checked : Shares.ValidatedShareSet) :
    Shares.validate checked.messages = .ok checked := by
  cases checked with
  | mk messages first firstPresent nonzeroThreshold exactCount sameThreshold
      sameIdentifier sameLength distinctIndices =>
    cases messages with
    | nil => simp at firstPresent
    | cons head rest =>
      have equal : head = first := by simpa using firstPresent
      subst head
      simp only [Shares.validate, List.head?_cons, nonzeroThreshold, exactCount,
        distinctIndices, ↓reduceDIte]
      rw [dite_eq_left sameThreshold, dite_eq_left sameIdentifier, dite_eq_left sameLength]

/-- The checked set retains exactly the caller's messages. -/
theorem validate_preserves_messages (shares : List Message)
    (checked : Shares.ValidatedShareSet) (valid : Shares.validate shares = .ok checked) :
    checked.messages = shares := by
  unfold Shares.validate at valid
  split at valid <;> try contradiction
  split at valid <;> try contradiction
  split at valid <;> try contradiction
  split at valid <;> try contradiction
  split at valid <;> try contradiction
  split at valid <;> try contradiction
  split at valid <;> try contradiction
  cases valid
  rfl

/-- At an existing index, interpolation returns exactly the matching checked
message, including any nonzero padding bits. The hypotheses express successful
set validation and lookup; no field identities or checksum assumptions occur. -/
theorem interpolate_at_existing (shares : List Message) (target : Symbol)
    (checked : Shares.ValidatedShareSet) (existing : Message)
    (valid : Shares.validate shares = .ok checked)
    (found : shares.find? (fun s => s.index == target) = some existing) :
    Shares.interpolate shares target = .ok existing := by
  have retained := validate_preserves_messages shares checked valid
  rw [Shares.interpolate, valid]
  change Except.ok (checked.interpolate target) = Except.ok existing
  simp only [Shares.ValidatedShareSet.interpolate, retained, found]

/-- In particular, every valid set is unchanged when evaluated at its head. -/
theorem interpolate_at_head (first : Message) (rest : List Message)
    (checked : Shares.ValidatedShareSet) (valid : Shares.validate (first :: rest) = .ok checked) :
    Shares.interpolate (first :: rest) first.index = .ok first := by
  apply interpolate_at_existing _ _ checked first valid
  simp

private theorem threshold_eq_of_count_eq (a b : Threshold) (h : a.count = b.count) :
    a = b := by
  cases a <;> cases b
  · rfl
  · simp only [Threshold.count] at h; omega
  · simp only [Threshold.count] at h; omega
  · apply congrArg Threshold.shared
    apply Fin.ext
    simp only [Threshold.count] at h
    omega

private theorem identifier_eq_of_symbols_eq (a b : Identifier) (h : a.symbols = b.symbols) :
    a = b := by
  cases a
  cases b
  cases h
  rfl

/-- Checked interpolation preserves the common threshold. -/
theorem checked_interpolate_threshold (checked : Shares.ValidatedShareSet) (target : Symbol) :
    (checked.interpolate target).threshold = checked.first.threshold := by
  unfold Shares.ValidatedShareSet.interpolate
  split
  · rename_i existing found
    exact threshold_eq_of_count_eq _ _
      (checked.sameThreshold existing (List.mem_of_find?_eq_some found))
  · rfl

/-- Checked interpolation preserves the common identifier. -/
theorem checked_interpolate_identifier (checked : Shares.ValidatedShareSet) (target : Symbol) :
    (checked.interpolate target).identifier = checked.first.identifier := by
  unfold Shares.ValidatedShareSet.interpolate
  split
  · rename_i existing found
    exact identifier_eq_of_symbols_eq _ _
      (checked.sameIdentifier existing (List.mem_of_find?_eq_some found))
  · rfl

/-- Checked interpolation always produces its requested index. -/
theorem checked_interpolate_index (checked : Shares.ValidatedShareSet) (target : Symbol) :
    (checked.interpolate target).index = target := by
  unfold Shares.ValidatedShareSet.interpolate
  split
  · rename_i existing found
    exact eq_of_beq (List.find?_some (p := fun s : Message => s.index == target) found)
  · rfl

/-- Checked interpolation preserves the payload length. -/
theorem checked_interpolate_length (checked : Shares.ValidatedShareSet) (target : Symbol) :
    (checked.interpolate target).payload.length = checked.first.payload.length := by
  unfold Shares.ValidatedShareSet.interpolate
  split
  · rename_i existing found
    exact checked.sameLength existing (List.mem_of_find?_eq_some found)
  · simp [Shares.ValidatedShareSet.interpolatePayload]

/-- Threshold-two recovery for arbitrary secret and randomness symbols: begin
at `s` and `a`, derive `c`, then recover from `a` and `c`. This proves the
per-column identity used by share interpolation for every possible input value. -/
theorem recover_generated_threshold_two_column : ∀ secret random : Symbol,
    Field.interpolate
      [(29, random), (24, Field.interpolate [(16, secret), (29, random)] 24)] 16 =
      secret := by
  decide

/-- The preceding recovery identity lifted to payloads of arbitrary equal
length. Random padding symbols are included, so no byte conversion is assumed. -/
theorem recover_generated_threshold_two_payload (secret random : List Symbol)
    (sameLength : secret.length = random.length) :
    (secret.zip random).map (fun (s, r) =>
      Field.interpolate [(29, r), (24, Field.interpolate [(16, s), (29, r)] 24)] 16) =
      secret := by
  simp only [recover_generated_threshold_two_column]
  exact List.map_fst_zip (by omega)

private def twoPointPayload (a b : List Symbol) (i j target : Symbol) : List Symbol :=
  (List.range a.length).map fun n =>
    Field.interpolate [(i,a[n]?.getD 0),(j,b[n]?.getD 0)] target
private def thresholdTwoMessage (id : Identifier) (index : Symbol) (payload : List Symbol)
    (h : payload.length ≤ 997) : Message :=
  ⟨.shared 0, id, index, payload, (by intro he; cases he), h⟩
private def twoMessageSet (id : Identifier) (a b : List Symbol)
    (ha : a.length ≤ 997) (hb : b.length ≤ 997) (hlen : a.length = b.length)
    (i j : Symbol) (hne : i ≠ j) : Shares.ValidatedShareSet where
  messages := [thresholdTwoMessage id i a ha, thresholdTwoMessage id j b hb]
  first := thresholdTwoMessage id i a ha
  firstPresent := rfl
  nonzeroThreshold := by simp [thresholdTwoMessage, Threshold.count]
  exactCount := rfl
  sameThreshold := by simp [thresholdTwoMessage]
  sameIdentifier := by simp [thresholdTwoMessage]
  sameLength := by simp [thresholdTwoMessage, hlen]
  distinctIndices := by simp [thresholdTwoMessage, hne]

private theorem validate_two_messages (id : Identifier) (a b : List Symbol)
    (ha : a.length ≤ 997) (hb : b.length ≤ 997) (hlen : a.length = b.length)
    (i j : Symbol) (hne : i ≠ j) :
    Shares.validate [thresholdTwoMessage id i a ha,thresholdTwoMessage id j b hb] = .ok (twoMessageSet id a b ha hb hlen i j hne) := by
  simp [Shares.validate, thresholdTwoMessage, Threshold.count, hlen, hne, twoMessageSet]
private theorem twoMessageSet_payload (id : Identifier) (a b : List Symbol)
    (ha : a.length ≤ 997) (hb : b.length ≤ 997) (hlen : a.length = b.length)
    (i j target : Symbol) (hne : i ≠ j) :
    (twoMessageSet id a b ha hb hlen i j hne).interpolatePayload target =
      twoPointPayload a b i j target := by
  apply List.ext_getElem
  · simp [Shares.ValidatedShareSet.interpolatePayload, twoMessageSet, thresholdTwoMessage,
      twoPointPayload]
  · intro n hleft hright
    have hn : n < a.length := by
      simpa [Shares.ValidatedShareSet.interpolatePayload, twoMessageSet, thresholdTwoMessage] using hleft
    have hb' : n < b.length := by omega
    simp [Shares.ValidatedShareSet.interpolatePayload, twoMessageSet, thresholdTwoMessage,
      twoPointPayload, List.getElem?_eq_getElem hn, List.getElem?_eq_getElem hb']

private theorem interpolate_two_messages (id : Identifier) (a b : List Symbol)
    (ha : a.length ≤ 997) (hb : b.length ≤ 997) (hlen : a.length = b.length)
    (i j target : Symbol) (hne : i ≠ j) (hit : i ≠ target) (hjt : j ≠ target) :
    Shares.interpolate [thresholdTwoMessage id i a ha,thresholdTwoMessage id j b hb] target =
      .ok (thresholdTwoMessage id target (twoPointPayload a b i j target) (by simpa [twoPointPayload] using ha)) := by
  rw [Shares.interpolate, validate_two_messages id a b ha hb hlen i j hne]
  change Except.ok ((twoMessageSet id a b ha hb hlen i j hne).interpolate target) = _
  have hp := twoMessageSet_payload id a b ha hb hlen i j target hne
  simp only [Shares.ValidatedShareSet.interpolate, twoMessageSet, thresholdTwoMessage,
    List.find?_cons, List.find?_nil, beq_eq_false_iff_ne.mpr hit,
    beq_eq_false_iff_ne.mpr hjt]
  congr 2
private theorem twoPointPayload_recovery (secret random : List Symbol)
    (hlen : secret.length = random.length) :
    twoPointPayload random (twoPointPayload secret random 16 29 24) 29 24 16 = secret := by
  apply List.ext_getElem?
  intro n
  by_cases hn : n < secret.length
  · have hr : n < random.length := by omega
    simp [twoPointPayload, List.getElem?_range hn, List.getElem?_range hr,
      recover_generated_threshold_two_column, List.getElem?_eq_getElem hn]
  · have hr : random.length ≤ n := by omega
    simp [twoPointPayload, List.getElem?_eq_none (by omega : secret.length ≤ n), hr]
/-- Complete threshold-two recovery for an arbitrary checked secret and an
arbitrary equally long random payload. Create the share at `a`, derive `c`
from the secret and `a`, then recover from `a` and `c`. The result is the
original `Message`, including metadata and all padding symbols. This theorem
supports every generic Codex32 payload length; it assumes no entropy property. -/
theorem recover_generated_threshold_two_message (secret : Message)
    (random : List Symbol) (threshold : secret.threshold = .shared 0)
    (index : secret.index = 16) (sameLength : secret.payload.length = random.length) :
    (do
      let a ← Message.create secret.threshold secret.identifier 29 random
      let c ← Shares.derive [secret, a] 24
      Shares.recover [a, c]) = .ok secret := by
  cases secret with
  | mk t id si payload hzero hbound =>
    cases threshold
    cases index
    have hr : random.length ≤ 997 := by simpa only [← sameLength] using hbound
    have hc : (twoPointPayload payload random 16 29 24).length ≤ 997 := by simpa [twoPointPayload] using hbound
    have createA : Message.create (.shared 0) id 29 random = .ok (thresholdTwoMessage id 29 random hr) := by
      simp [Message.create, thresholdTwoMessage, hr]
    change (do
      let a ← Message.create (.shared 0) id 29 random
      let c ← Shares.derive [thresholdTwoMessage id 16 payload hbound, a] 24
      Shares.recover [a, c]) = .ok (thresholdTwoMessage id 16 payload hbound)
    rw [createA]
    change (do
      let c ← Shares.derive [thresholdTwoMessage id 16 payload hbound, thresholdTwoMessage id 29 random hr] 24
      Shares.recover [thresholdTwoMessage id 29 random hr, c]) = .ok (thresholdTwoMessage id 16 payload hbound)
    have deriveC : Shares.derive [thresholdTwoMessage id 16 payload hbound, thresholdTwoMessage id 29 random hr] 24 =
        .ok (thresholdTwoMessage id 24 (twoPointPayload payload random 16 29 24) hc) := by
      rw [Shares.derive, validate_two_messages id payload random hbound hr sameLength 16 29 (by decide)]
      change Except.ok ((twoMessageSet id payload random hbound hr sameLength 16 29 (by decide)).interpolate 24) = _
      have h := interpolate_two_messages id payload random hbound hr sameLength 16 29 24 (by decide) (by decide) (by decide)
      rw [Shares.interpolate, validate_two_messages id payload random hbound hr sameLength 16 29 (by decide)] at h
      exact h
    rw [deriveC]
    change Shares.recover [thresholdTwoMessage id 29 random hr, thresholdTwoMessage id 24 (twoPointPayload payload random 16 29 24) hc] = _
    have lengths : random.length = (twoPointPayload payload random 16 29 24).length := by simp [twoPointPayload, sameLength]
    rw [Shares.recover, validate_two_messages id random (twoPointPayload payload random 16 29 24) hr hc lengths 29 24 (by decide)]
    change Except.ok ((twoMessageSet id random (twoPointPayload payload random 16 29 24) hr hc lengths 29 24 (by decide)).interpolate 16) = _
    have h := interpolate_two_messages id random (twoPointPayload payload random 16 29 24) hr hc lengths 29 24 16 (by decide) (by decide) (by decide)
    rw [Shares.interpolate, validate_two_messages id random (twoPointPayload payload random 16 29 24) hr hc lengths 29 24 (by decide)] at h
    change Except.ok ((twoMessageSet id random (twoPointPayload payload random 16 29 24) hr hc lengths 29 24 (by decide)).interpolate 16) = _ at h
    rw [h]
    simp only [thresholdTwoMessage, twoPointPayload_recovery payload random sameLength]

end Codex32.Proofs
