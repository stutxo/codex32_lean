import Codex32Proofs.ShareRecovery

/-!
Initialization through recovery for admissible fresh and existing-secret
inputs. The initial source's validation is proved from the initializer inputs;
the general recovery results then cover every distinct threshold-size set of
nonsecret output indices. No entropy assumption is needed for correctness.
-/

namespace Codex32.Proofs

set_option maxHeartbeats 0

/-- The fixed initial share indices, as a proof-visible view of the executable
initializer's private list: `a,c,d,e,f,g,h,j,k`. -/
def initialIndices : List Symbol := [29, 24, 13, 25, 9, 8, 23, 18, 22]

private def buildInitial (threshold : Threshold) (identifier : Identifier)
    (indices : List Symbol) (payloads : List (List Symbol)) : Except Error (List Message) :=
  (indices.zip payloads).mapM fun (index, payload) =>
    Message.create threshold identifier index payload

/-- A proof-visible structural view of the executable initial-share builder. -/
def initialMessages (threshold : Threshold) (identifier : Identifier)
    (payloads : List (List Symbol)) : Except Error (List Message) :=
  (initialIndices.zip payloads).mapM fun (index, payload) =>
    Message.create threshold identifier index payload

private theorem threshold_ne_unshared (threshold : Threshold)
    (nonzero : threshold.count ≠ 0) : threshold ≠ .unshared := by
  intro equal
  exact nonzero (by simp [equal, Threshold.count])

private theorem threshold_le_nine (threshold : Threshold) : threshold.count ≤ 9 := by
  cases threshold with
  | unshared => simp [Threshold.count]
  | shared k => have := k.isLt; simp [Threshold.count]; omega

private theorem buildInitial_success (threshold : Threshold) (identifier : Identifier)
    (indices : List Symbol) (payloads : List (List Symbol)) (length : Nat)
    (nonzero : threshold.count ≠ 0) (enough : payloads.length ≤ indices.length)
    (bound : length ≤ 997) (lengths : ∀ p ∈ payloads, p.length = length) :
    ∃ messages,
      buildInitial threshold identifier indices payloads = .ok messages ∧
      messages.length = payloads.length ∧
      messages.map Message.index = indices.take payloads.length ∧
      messages.map (fun m => (m.index, m.payload)) = indices.zip payloads ∧
      (∀ m ∈ messages, m.threshold = threshold) ∧
      (∀ m ∈ messages, m.identifier = identifier) ∧
      (∀ m ∈ messages, m.payload.length = length) := by
  induction payloads generalizing indices with
  | nil => exact ⟨[], by simp [buildInitial]; rfl⟩
  | cons payload rest ih =>
    cases indices with
    | nil => simp at enough
    | cons index indices =>
      have firstLength := lengths payload (by simp)
      have payloadBound : payload.length ≤ 997 := by omega
      let first : Message := ⟨threshold, identifier, index, payload,
        (by intro equal; exact False.elim (threshold_ne_unshared threshold nonzero equal)),
        payloadBound⟩
      have created : Message.create threshold identifier index payload = .ok first := by
        simp [Message.create, threshold_ne_unshared threshold nonzero, payloadBound, first]
      obtain ⟨messages, built, count, indexList, dataList, thresholds, identifiers, payloadLengths⟩ :=
        ih indices (by simp only [List.length_cons] at enough; omega)
          (fun p hp => lengths p (by simp [hp]))
      refine ⟨first :: messages, ?_, by simp [count], ?_, ?_, ?_, ?_, ?_⟩
      · simp only [buildInitial, List.zip_cons_cons, List.mapM_cons, created]
        change (do
          let tail ← buildInitial threshold identifier indices rest
          pure (first :: tail)) = .ok (first :: messages)
        rw [built]
        rfl
      · simp [first, indexList]
      · simp [first, dataList]
      · intro m hm
        rcases List.mem_cons.mp hm with rfl | hm
        · rfl
        · exact thresholds m hm
      · intro m hm
        rcases List.mem_cons.mp hm with rfl | hm
        · rfl
        · exact identifiers m hm
      · intro m hm
        rcases List.mem_cons.mp hm with rfl | hm
        · exact firstLength
        · exact payloadLengths m hm

private theorem validate_checked (checked : Shares.ValidatedShareSet) :
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

private theorem checked_of_common (messages : List Message)
    (threshold : Threshold) (identifier : Identifier) (length : Nat)
    (nonzero : threshold.count ≠ 0) (count : messages.length = threshold.count)
    (thresholds : ∀ m ∈ messages, m.threshold = threshold)
    (identifiers : ∀ m ∈ messages, m.identifier = identifier)
    (lengths : ∀ m ∈ messages, m.payload.length = length)
    (distinct : (messages.map Message.index).Nodup) :
    ∃ checked : Shares.ValidatedShareSet, checked.messages = messages ∧
      Shares.validate messages = .ok checked := by
  cases messages with
  | nil => simp at count; exact False.elim (nonzero count.symm)
  | cons first rest =>
    have ht := thresholds first (by simp)
    have hi := identifiers first (by simp)
    have hl := lengths first (by simp)
    let checked : Shares.ValidatedShareSet := {
      messages := first :: rest
      first := first
      firstPresent := rfl
      nonzeroThreshold := by simpa [ht] using nonzero
      exactCount := by simpa [ht] using count
      sameThreshold := by intro m hm; rw [thresholds m hm, ht]
      sameIdentifier := by intro m hm; rw [identifiers m hm, hi]
      sameLength := by intro m hm; rw [lengths m hm, hl]
      distinctIndices := distinct }
    exact ⟨checked, rfl, validate_checked checked⟩

/-- On admissible inputs the fresh initializer is exactly the fixed-index
message builder, with all rejection branches discharged. -/
theorem initializeFresh_eq (threshold : Threshold) (identifier : Identifier)
    (payloads : List (List Symbol)) (length : Nat)
    (nonzero : threshold.count ≠ 0) (count : payloads.length = threshold.count)
    (supported : length ∈ [26, 32, 39, 45, 52, 103])
    (lengths : ∀ p ∈ payloads, p.length = length) :
    Shares.initializeFresh threshold identifier payloads =
      initialMessages threshold identifier payloads := by
  cases payloads with
  | nil => simp at count; exact False.elim (nonzero count.symm)
  | cons first rest =>
    have firstLength := lengths first (by simp)
    have supported' : ([26, 32, 39, 45, 52, 103] : List Nat).contains first.length = true :=
      List.contains_iff_mem.mpr (by simpa only [firstLength] using supported)
    have equalLengths : (first :: rest).any (fun p => p.length != first.length) = false := by
      rw [List.any_eq_false]
      intro p hp
      simp [lengths p hp, firstLength]
    simp only [Shares.initializeFresh, beq_eq_false_iff_ne.mpr nonzero,
      count, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, List.head?_cons,
      equalLengths]
    change (if (!([26, 32, 39, 45, 52, 103] : List Nat).contains first.length) = true
      then _ else _) = _
    simp only [supported', Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rfl

/-- On admissible inputs the existing-secret initializer preserves the secret
and appends exactly the fixed-index message builder's output. -/
theorem initializeExisting_eq (secret : Message) (payloads : List (List Symbol))
    (index : secret.index = 16) (nonzero : secret.threshold.count ≠ 0)
    (count : payloads.length + 1 = secret.threshold.count)
    (lengths : ∀ p ∈ payloads, p.length = secret.payload.length) :
    Shares.initializeExisting secret payloads = (do
      let randomShares ← initialMessages secret.threshold secret.identifier payloads
      pure (secret :: randomShares)) := by
  have equalLengths : payloads.any (fun p => p.length != secret.payload.length) = false := by
    rw [List.any_eq_false]
    intro p hp
    simp [lengths p hp]
  simp only [Shares.initializeExisting, index, bne_self_eq_false,
    beq_eq_false_iff_ne.mpr nonzero, count, equalLengths,
    Bool.false_eq_true, ↓reduceIte]
  rfl

/-- The explicit initial-message model succeeds, retaining every input
payload and its assigned fixed index as well as the common metadata. -/
theorem initialMessages_success (threshold : Threshold) (identifier : Identifier)
    (payloads : List (List Symbol)) (length : Nat)
    (nonzero : threshold.count ≠ 0) (enough : payloads.length ≤ 9)
    (bound : length ≤ 997) (lengths : ∀ p ∈ payloads, p.length = length) :
    ∃ messages,
      initialMessages threshold identifier payloads = .ok messages ∧
      messages.length = payloads.length ∧
      messages.map Message.index = initialIndices.take payloads.length ∧
      messages.map (fun m => (m.index, m.payload)) = initialIndices.zip payloads ∧
      (∀ m ∈ messages, m.threshold = threshold) ∧
      (∀ m ∈ messages, m.identifier = identifier) ∧
      (∀ m ∈ messages, m.payload.length = length) := by
  exact buildInitial_success threshold identifier initialIndices payloads length
    nonzero (by simpa only [initialIndices, List.length_cons, List.length_nil] using enough)
    bound lengths

/-- Every admissible fresh initialization succeeds and its actual output is
accepted by the share validator. The witness preserves the exact input
payloads and fixed indices; no validation hypothesis is assumed. -/
theorem initializeFresh_valid (threshold : Threshold) (identifier : Identifier)
    (payloads : List (List Symbol)) (length : Nat)
    (nonzero : threshold.count ≠ 0) (count : payloads.length = threshold.count)
    (supported : length ∈ [26, 32, 39, 45, 52, 103])
    (lengths : ∀ p ∈ payloads, p.length = length) :
    ∃ checked : Shares.ValidatedShareSet,
      Shares.initializeFresh threshold identifier payloads = .ok checked.messages ∧
      Shares.validate checked.messages = .ok checked ∧
      checked.messages.map (fun m => (m.index, m.payload)) = initialIndices.zip payloads ∧
      checked.first.threshold = threshold ∧
      checked.first.identifier = identifier ∧
      checked.first.payload.length = length := by
  have bound : length ≤ 997 := by simp at supported; omega
  obtain ⟨messages, built, messageCount, indices, dataList, thresholds, identifiers, payloadLengths⟩ :=
    initialMessages_success threshold identifier payloads length nonzero
      (by rw [count]; exact threshold_le_nine threshold) bound lengths
  have distinct : (messages.map Message.index).Nodup := by
    rw [indices]
    exact (List.take_sublist _ _).nodup (by decide +kernel : initialIndices.Nodup)
  obtain ⟨checked, retained, valid⟩ := checked_of_common messages threshold identifier length
    nonzero (messageCount.trans count) thresholds identifiers payloadLengths distinct
  have firstMem : checked.first ∈ messages := by
    rw [← retained]
    exact List.mem_of_head? checked.firstPresent
  refine ⟨checked, ?_, ?_, ?_, thresholds _ firstMem, identifiers _ firstMem,
    payloadLengths _ firstMem⟩
  · rw [initializeFresh_eq threshold identifier payloads length nonzero count supported lengths,
      built, retained]
  · simpa only [retained] using valid
  · simpa only [retained] using dataList

/-- Every admissible existing-secret initialization succeeds and its actual
output is accepted by the share validator. The secret is the first message,
and every entropy payload retains its prescribed fixed share index. -/
theorem initializeExisting_valid (secret : Message) (payloads : List (List Symbol))
    (index : secret.index = 16) (nonzero : secret.threshold.count ≠ 0)
    (count : payloads.length + 1 = secret.threshold.count)
    (lengths : ∀ p ∈ payloads, p.length = secret.payload.length) :
    ∃ checked : Shares.ValidatedShareSet,
      Shares.initializeExisting secret payloads = .ok checked.messages ∧
      Shares.validate checked.messages = .ok checked ∧
      checked.first = secret ∧
      checked.messages.map (fun m => (m.index, m.payload)) =
        (16, secret.payload) :: initialIndices.zip payloads := by
  obtain ⟨messages, built, messageCount, indices, dataList, thresholds, identifiers, payloadLengths⟩ :=
    initialMessages_success secret.threshold secret.identifier payloads secret.payload.length
      nonzero (by have := threshold_le_nine secret.threshold; omega) secret.lengthValid lengths
  have distinct : ((secret :: messages).map Message.index).Nodup := by
    rw [List.map_cons, index, indices, List.nodup_cons]
    constructor
    · intro member
      exact (by decide +kernel : (16 : Symbol) ∉ initialIndices) (List.mem_of_mem_take member)
    · exact (List.take_sublist _ _).nodup (by decide +kernel : initialIndices.Nodup)
  obtain ⟨checked, retained, valid⟩ := checked_of_common (secret :: messages)
    secret.threshold secret.identifier secret.payload.length nonzero
    (by simp only [List.length_cons, messageCount]; omega)
    (by simpa only [List.forall_mem_cons, true_and] using thresholds)
    (by simpa only [List.forall_mem_cons, true_and] using identifiers)
    (by simpa only [List.forall_mem_cons, true_and] using payloadLengths) distinct
  refine ⟨checked, ?_, ?_, ?_, ?_⟩
  · rw [initializeExisting_eq secret payloads index nonzero count lengths, built]
    rw [retained]
    rfl
  · simpa only [retained] using valid
  · have := checked.firstPresent
    simpa only [retained, List.head?_cons, Option.some.injEq] using this.symm
  · simp only [retained, List.map_cons, dataList, index]

/-- Fresh initialization, validation, sampling and public recovery all succeed
for every distinct threshold-size choice of nonsecret output indices. Every
choice returns the same secret, with the requested metadata and payload size. -/
theorem initializeFresh_recover (threshold : Threshold) (identifier : Identifier)
    (payloads : List (List Symbol)) (length : Nat)
    (nonzero : threshold.count ≠ 0) (count : payloads.length = threshold.count)
    (supported : length ∈ [26, 32, 39, 45, 52, 103])
    (lengths : ∀ p ∈ payloads, p.length = length) :
    ∃ secret : Message,
      secret.threshold = threshold ∧ secret.identifier = identifier ∧
      secret.index = 16 ∧ secret.payload.length = length ∧
      ∀ indices : List Symbol, indices.Nodup → indices.length = threshold.count →
        16 ∉ indices →
        (do
          let messages ← Shares.initializeFresh threshold identifier payloads
          let checked ← Shares.validate messages
          Shares.recover (indices.map checked.interpolate)) = .ok secret := by
  obtain ⟨checked, initialized, validated, _, firstThreshold, firstIdentifier, firstLength⟩ :=
    initializeFresh_valid threshold identifier payloads length nonzero count supported lengths
  refine ⟨checked.interpolate 16, ?_, ?_, checked_interpolate_index checked 16, ?_, ?_⟩
  · rw [checked_interpolate_threshold, firstThreshold]
  · rw [checked_interpolate_identifier, firstIdentifier]
  · rw [checked_interpolate_length, firstLength]
  · intro indices distinct selectedCount sharesOnly
    rw [initialized]
    change (do
      let source ← Shares.validate checked.messages
      Shares.recover (indices.map source.interpolate)) = .ok (checked.interpolate 16)
    rw [validated]
    exact recover_generated_shares checked indices distinct
      (by rw [selectedCount, ← firstThreshold, ← checked.exactCount]) sharesOnly

/-- Starting with an existing secret, the complete public initialization,
validation and recovery pipeline returns that exact message, including padding,
for every distinct threshold-size selection of nonsecret derived indices. -/
theorem initializeExisting_recover (secret : Message) (payloads : List (List Symbol))
    (index : secret.index = 16) (nonzero : secret.threshold.count ≠ 0)
    (count : payloads.length + 1 = secret.threshold.count)
    (lengths : ∀ p ∈ payloads, p.length = secret.payload.length)
    (indices : List Symbol) (distinct : indices.Nodup)
    (selectedCount : indices.length = secret.threshold.count) (sharesOnly : 16 ∉ indices) :
    (do
      let messages ← Shares.initializeExisting secret payloads
      let checked ← Shares.validate messages
      Shares.recover (indices.map checked.interpolate)) = .ok secret := by
  obtain ⟨checked, initialized, validated, first, _⟩ :=
    initializeExisting_valid secret payloads index nonzero count lengths
  have found : checked.messages.find? (fun m => m.index == 16) = some secret := by
    have head := checked.firstPresent
    rw [first] at head
    cases messagesEq : checked.messages with
    | nil => simp [messagesEq] at head
    | cons message rest =>
      have equal : message = secret := by simpa only [messagesEq, List.head?_cons,
        Option.some.injEq] using head
      simp only [equal, List.find?_cons, index, beq_self_eq_true]
  rw [initialized]
  change (do
    let source ← Shares.validate checked.messages
    Shares.recover (indices.map source.interpolate)) = .ok secret
  rw [validated]
  exact recover_generated_existing_secret checked indices distinct
    (by rw [selectedCount, ← first, ← checked.exactCount]) sharesOnly secret found

end Codex32.Proofs
