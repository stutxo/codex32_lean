import Codex32Proofs.Shares
import Codex32Proofs.Recovery

/-! General share recovery, lifted from scalar Lagrange interpolation to
complete checked messages and the public recovery API. All thresholds, generic
payload lengths, and padding symbols are covered. Executable code imports none
of these proofs. -/

namespace Codex32.Proofs

set_option maxHeartbeats 0

/-- Scalar samples for one payload column of a message list. -/
def messageColumn (messages : List Message) (column : Nat) : List (Symbol × Symbol) :=
  messages.map fun message => (message.index, message.payload[column]?.getD 0)

theorem messageColumn_indices (messages : List Message) (column : Nat) :
    (messageColumn messages column).map Prod.fst = messages.map Message.index := by
  simp [messageColumn, List.map_map]

theorem messageColumn_length (messages : List Message) (column : Nat) :
    (messageColumn messages column).length = messages.length := by
  simp [messageColumn]

private theorem messageColumn_bounded (checked : Shares.ValidatedShareSet)
    (column : Nat) (bound : column < checked.first.payload.length) :
    messageColumn checked.messages column = checked.messages.attach.map (fun share =>
      (share.val.index, share.val.payload[column]'(by
        rw [checked.sameLength share.val share.property]; exact bound))) := by
  unfold messageColumn
  rw [← List.attach_map_val]
  apply List.map_congr_left
  intro share _
  have h : column < share.val.payload.length := by
    rw [checked.sameLength share.val share.property]; exact bound
  simp [List.getElem?_eq_getElem h]

private theorem checked_interpolatePayload_column (checked : Shares.ValidatedShareSet)
    (target : Symbol) (column : Nat) (bound : column < checked.first.payload.length) :
    (checked.interpolatePayload target)[column]?.getD 0 =
      Field.interpolate (messageColumn checked.messages column) target := by
  rw [messageColumn_bounded checked column bound]
  simp [Shares.ValidatedShareSet.interpolatePayload, bound]

/-- Checked message interpolation agrees with the executable scalar formula
at every payload coordinate, including when the requested index is present. -/
theorem checked_interpolate_column (checked : Shares.ValidatedShareSet)
    (target : Symbol) (column : Nat) (bound : column < checked.first.payload.length) :
    (checked.interpolate target).payload[column]?.getD 0 =
      Field.interpolate (messageColumn checked.messages column) target := by
  unfold Shares.ValidatedShareSet.interpolate
  split
  · rename_i existing found
    have member := List.mem_of_find?_eq_some found
    have index : existing.index = target :=
      eq_of_beq (List.find?_some (p := fun s : Message => s.index == target) found)
    have pMember : (existing.index, existing.payload[column]?.getD 0) ∈
        messageColumn checked.messages column := List.mem_map_of_mem member
    have h := Field.interpolate_existing (messageColumn checked.messages column)
      (by simpa [messageColumn_indices] using checked.distinctIndices)
      _ pMember
    simpa [index] using h.symm
  · exact checked_interpolatePayload_column checked target column bound

private theorem generated_common_metadata (original generated : Shares.ValidatedShareSet)
    (indices : List Symbol) (generatedFrom : generated.messages = indices.map original.interpolate) :
    generated.first.threshold = original.first.threshold ∧
    generated.first.identifier = original.first.identifier ∧
    generated.first.payload.length = original.first.payload.length := by
  have member : generated.first ∈ indices.map original.interpolate := by
    rw [← generatedFrom]
    exact List.mem_of_head? generated.firstPresent
  obtain ⟨index, _, equal⟩ := List.mem_map.mp member
  rw [← equal]
  exact ⟨checked_interpolate_threshold original index,
    checked_interpolate_identifier original index, checked_interpolate_length original index⟩

private theorem generated_column (original generated : Shares.ValidatedShareSet)
    (indices : List Symbol) (generatedFrom : generated.messages = indices.map original.interpolate)
    (column : Nat) (bound : column < original.first.payload.length) :
    messageColumn generated.messages column = indices.map (fun i =>
      (i, Field.interpolate (messageColumn original.messages column) i)) := by
  simp [messageColumn, generatedFrom, List.map_map, checked_interpolate_index,
    checked_interpolate_column original _ column bound]

private def reinterpolatedSet (original : Shares.ValidatedShareSet)
    (index : Symbol) (rest : List Symbol)
    (count : (index :: rest).length = original.messages.length)
    (distinct : (index :: rest).Nodup) : Shares.ValidatedShareSet where
  messages := (index :: rest).map original.interpolate
  first := original.interpolate index
  firstPresent := rfl
  nonzeroThreshold := by
    rw [checked_interpolate_threshold]
    exact original.nonzeroThreshold
  exactCount := by
    rw [List.length_map, count, checked_interpolate_threshold]
    exact original.exactCount
  sameThreshold := by
    intro share member
    obtain ⟨i, _, equal⟩ := List.mem_map.mp member
    rw [← equal, checked_interpolate_threshold, checked_interpolate_threshold]
  sameIdentifier := by
    intro share member
    obtain ⟨i, _, equal⟩ := List.mem_map.mp member
    rw [← equal, checked_interpolate_identifier, checked_interpolate_identifier]
  sameLength := by
    intro share member
    obtain ⟨i, _, equal⟩ := List.mem_map.mp member
    rw [← equal, checked_interpolate_length, checked_interpolate_length]
  distinctIndices := by
    simpa [List.map_map, Function.comp_def, checked_interpolate_index] using distinct

/-- Reinterpolating any exact-threshold selection of distinct, correctly
generated strings returns the same message at every target. The checked sets
carry the threshold, distinctness, metadata, and payload-length conditions;
the generation hypothesis connects every new payload to the original set.
This includes arbitrary supported thresholds and all padding symbols. -/
theorem checked_reinterpolate_message (original generated : Shares.ValidatedShareSet)
    (indices : List Symbol) (generatedFrom : generated.messages = indices.map original.interpolate)
    (target : Symbol) : generated.interpolate target = original.interpolate target := by
  obtain ⟨threshold, identifier, length⟩ :=
    generated_common_metadata original generated indices generatedFrom
  have indexList : generated.messages.map Message.index = indices := by
    simp [generatedFrom, List.map_map, Function.comp_def, checked_interpolate_index]
  have distinct : indices.Nodup := by
    rw [← indexList]
    exact generated.distinctIndices
  have count : indices.length = original.messages.length := by
    have hg := generated.exactCount
    have ho := original.exactCount
    rw [threshold] at hg
    simpa [generatedFrom, ho] using hg
  apply message_ext
  · rw [checked_interpolate_threshold, checked_interpolate_threshold, threshold]
  · rw [checked_interpolate_identifier, checked_interpolate_identifier, identifier]
  · rw [checked_interpolate_index, checked_interpolate_index]
  · apply List.ext_getElem
    · rw [checked_interpolate_length, checked_interpolate_length, length]
    · intro column hgenerated horiginal
      have bound : column < original.first.payload.length := by
        simpa only [checked_interpolate_length] using horiginal
      have generatedBound : column < generated.first.payload.length := by
        rw [length]; exact bound
      have columnEqual : (generated.interpolate target).payload[column]?.getD 0 =
          (original.interpolate target).payload[column]?.getD 0 := by
        rw [checked_interpolate_column generated target column generatedBound,
          checked_interpolate_column original target column bound,
          generated_column original generated indices generatedFrom column bound]
        exact Field.interpolate_reinterpolate (messageColumn original.messages column)
          indices distinct (by simpa [messageColumn_length] using count) target
      simpa only [List.getElem?_eq_getElem hgenerated,
        List.getElem?_eq_getElem horiginal, Option.getD_some] using columnEqual

/-- Recovering any checked threshold-size selection of correctly generated
shares returns the original set evaluated at the secret index. This covers
both fresh and existing-secret initialization. Generic Codex32 payload lengths
are supported; no entropy assumption is needed for algebraic correctness. -/
theorem checked_recover_generated (original generated : Shares.ValidatedShareSet)
    (indices : List Symbol) (generatedFrom : generated.messages = indices.map original.interpolate)
    (sharesOnly : 16 ∉ indices) :
    generated.recover = .ok (original.interpolate 16) := by
  have fresh : generated.messages.any (fun s => s.index == 16) = false := by
    simp only [generatedFrom, List.any_map, Function.comp_def, checked_interpolate_index,
      List.any_eq_false]
    intro index member equal
    exact sharesOnly ((eq_of_beq equal) ▸ member)
  simp only [Shares.ValidatedShareSet.recover, fresh, Bool.false_eq_true, ↓reduceIte]
  rw [checked_reinterpolate_message original generated indices generatedFrom 16]
/-- Recovery to an existing secret, including all of its metadata and padding. -/
theorem recover_generated_message (original generated : Shares.ValidatedShareSet)
    (indices : List Symbol) (generatedFrom : generated.messages = indices.map original.interpolate)
    (sharesOnly : 16 ∉ indices) (secret : Message)
    (found : original.messages.find? (fun s => s.index == 16) = some secret) :
    generated.recover = .ok secret := by
  rw [checked_recover_generated original generated indices generatedFrom sharesOnly]
  simp only [Shares.ValidatedShareSet.interpolate, found]

/-- The public recovery API succeeds for any threshold-size selection of
distinct generated shares. Validation is proved to succeed, not assumed.
The selected indices may include existing random-share indices and must
exclude the secret index. -/
theorem recover_generated_shares (original : Shares.ValidatedShareSet)
    (indices : List Symbol) (distinct : indices.Nodup)
    (count : indices.length = original.messages.length) (sharesOnly : 16 ∉ indices) :
    Shares.recover (indices.map original.interpolate) = .ok (original.interpolate 16) := by
  cases indices with
  | nil =>
    have zero : original.first.threshold.count = 0 := by
      have := original.exactCount
      simp only [List.length_nil] at count
      omega
    exact False.elim (original.nonzeroThreshold zero)
  | cons index rest =>
    let generated := reinterpolatedSet original index rest count distinct
    have valid : Shares.validate ((index :: rest).map original.interpolate) = .ok generated :=
      validate_checked generated
    rw [Shares.recover, valid]
    change generated.recover = .ok (original.interpolate 16)
    exact checked_recover_generated original generated (index :: rest) rfl sharesOnly

/-- The public recovery API returns an existing secret exactly for every
supported threshold and every distinct selection of nonsecret share indices. -/
theorem recover_generated_existing_secret (original : Shares.ValidatedShareSet)
    (indices : List Symbol) (distinct : indices.Nodup)
    (count : indices.length = original.messages.length) (sharesOnly : 16 ∉ indices)
    (secret : Message)
    (found : original.messages.find? (fun s => s.index == 16) = some secret) :
    Shares.recover (indices.map original.interpolate) = .ok secret := by
  rw [recover_generated_shares original indices distinct count sharesOnly]
  simp only [Shares.ValidatedShareSet.interpolate, found]

end Codex32.Proofs
