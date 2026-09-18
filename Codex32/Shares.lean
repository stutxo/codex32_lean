import Codex32.Seed
import Codex32.Field

/-! BIP 93 share derivation, recovery, and initial share generation.

Randomness is explicit input: the caller supplies independent uniform GF(32)
symbols. In particular, random bytes padded with zero bits are not a substitute
for these full-symbol payloads. No random generator or entropy source is hidden
in this module. Checked `Message`s have no unchecked checksum attached; their
serialization constructs the appropriate checksum.
-/

namespace Codex32.Shares

/-- An exact-threshold set whose interpolation preconditions have been checked.
The witnesses are propositions, erased from executable code. Keep this value
when deriving multiple shares to avoid validating the same inputs repeatedly. -/
structure ValidatedShareSet where
  messages : List Message
  first : Message
  firstPresent : messages.head? = some first
  nonzeroThreshold : first.threshold.count ≠ 0
  exactCount : messages.length = first.threshold.count
  sameThreshold : ∀ share ∈ messages, share.threshold.count = first.threshold.count
  sameIdentifier : ∀ share ∈ messages, share.identifier.symbols = first.identifier.symbols
  sameLength : ∀ share ∈ messages, share.payload.length = first.payload.length
  distinctIndices : (messages.map Message.index).Nodup

/-- Check all interpolation preconditions once and retain their evidence. -/
def validate (shares : List Message) : Except Error ValidatedShareSet :=
  match hfirst : shares.head? with
  | none => .error .emptyShareSet
  | some first =>
    if hnonzero : first.threshold.count = 0 then .error .invalidShareThreshold
    else if hcount : shares.length = first.threshold.count then
      if hthreshold : ∀ s ∈ shares, s.threshold.count = first.threshold.count then
        if hidentifier : ∀ s ∈ shares, s.identifier.symbols = first.identifier.symbols then
          if hlength : ∀ s ∈ shares, s.payload.length = first.payload.length then
            if hindices : (shares.map Message.index).Nodup then
              .ok ⟨shares, first, hfirst, hnonzero, hcount, hthreshold,
                hidentifier, hlength, hindices⟩
            else .error .duplicateIndex
          else .error .mismatchedLength
        else .error .mismatchedIdentifier
      else .error .mismatchedThreshold
    else .error .wrongShareCount

namespace ValidatedShareSet

/-- Evaluate payload columns using indices whose bounds follow from the
validated equal-length invariant. -/
def interpolatePayload (set : ValidatedShareSet) (target : Symbol) : List Symbol :=
  List.ofFn fun column : Fin set.first.payload.length =>
    Field.interpolate (set.messages.attach.map fun share =>
      (share.val.index, share.val.payload[column.val]'(by
        rw [set.sameLength share.val share.property]
        exact column.isLt))) target

/-- Evaluate a checked interpolation set. Existing indices return the original
message, including all padding symbols. No validation is repeated. -/
def interpolate (set : ValidatedShareSet) (target : Symbol) : Message :=
  match set.messages.find? (fun s => s.index == target) with
  | some existing => existing
  | none =>
    ⟨set.first.threshold, set.first.identifier, target, set.interpolatePayload target,
      (by intro h; have := set.nonzeroThreshold; simp [h, Threshold.count] at this),
      (by simpa [interpolatePayload] using set.first.lengthValid)⟩

/-- Derive at a fresh target from an already checked set. -/
def derive (set : ValidatedShareSet) (target : Symbol) : Except Error Message :=
  if set.messages.any (fun s => s.index == target) then .error .targetAlreadyPresent
  else .ok (set.interpolate target)

/-- Recover from an already checked set, additionally rejecting the secret
index among the inputs. -/
def recover (set : ValidatedShareSet) : Except Error Message :=
  if set.messages.any (fun s => s.index == 16) then .error .secretInRecovery
  else .ok (set.interpolate 16)

end ValidatedShareSet

/-- Validate an exact-threshold interpolation set and evaluate its polynomial.
Existing indices return the corresponding original message unchanged. Initial
strings may include the secret, as required when splitting an existing seed.
Generic codex32 payload sizes are supported; master-seed sizes are checked by
`Seed` and by the initialization helpers below. -/
def interpolate (shares : List Message) (target : Symbol) : Except Error Message := do
  let checked ← validate shares
  return checked.interpolate target

/-- Derive a string at a fresh index, as specified in "Generating Shares".
The secret index `s` is permitted; `recover` additionally requires share-only
inputs. Use `interpolate` to evaluate at an already existing index. -/
def derive (shares : List Message) (target : Symbol) : Except Error Message := do
  let checked ← validate shares
  checked.derive target

/-- Recover the secret from exactly the threshold number of distinct shares.
An input with the secret index is not a share and is rejected. -/
def recover (shares : List Message) : Except Error Message := do
  let checked ← validate shares
  checked.recover

/-- The first nine available alphabetic bech32 letters, in alphabetical order.
The largest supported threshold is nine; the secret letter `s` is not reached. -/
private def initialIndices : List Symbol :=
  [29, 24, 13, 25, 9, 8, 23, 18, 22] -- a c d e f g h j k

private def initialMessages (threshold : Threshold) (identifier : Identifier)
    (payloads : List (List Symbol)) : Except Error (List Message) :=
  (initialIndices.zip payloads).mapM fun (index, payload) =>
    Message.create threshold identifier index payload

/-- Create the initial `k` shares of a fresh master seed. The `k` supplied
payloads must have the same supported master-seed payload length and must have
been drawn independently, uniformly over all five-bit symbols. The caller
chooses the seed size by the payload length; all padding bits remain random. -/
def initializeFresh (threshold : Threshold) (identifier : Identifier)
    (payloads : List (List Symbol)) : Except Error (List Message) := do
  if threshold.count == 0 then
    throw .invalidShareThreshold
  if payloads.length != threshold.count then
    throw .wrongEntropyCount
  let some first := payloads.head? | throw .entropyRequired
  if !Seed.validPayloadLength first.length then
    throw .unsupportedPayloadLength
  if payloads.any (fun p => p.length != first.length) then
    throw .mismatchedLength
  initialMessages threshold identifier payloads

/-- Create the initial interpolation set for an existing codex32 secret.
The secret must already carry the desired nonzero threshold. Supply `k - 1`
independent uniform full-symbol payloads matching its payload length. The
returned set includes the secret first; derive distributable shares from it.
As in "For an existing secret", application-specific payload sizes are allowed;
use `Seed` to impose the master-seed application rules. -/
def initializeExisting (secret : Message) (payloads : List (List Symbol)) :
    Except Error (List Message) := do
  if secret.index != 16 then
    throw .expectedSecret
  if secret.threshold.count == 0 then
    throw .invalidShareThreshold
  if payloads.length + 1 != secret.threshold.count then
    throw .wrongEntropyCount
  if payloads.any (fun p => p.length != secret.payload.length) then
    throw .mismatchedLength
  let randomShares ← initialMessages secret.threshold secret.identifier payloads
  return secret :: randomShares

end Codex32.Shares
