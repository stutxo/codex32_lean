import Codex32Proofs.Recovery

/-!
Algebra behind Shamir secrecy for the executable GF(32) interpolation.
A polynomial mask changes the secret evaluation by an arbitrary amount while
vanishing at fewer-than-threshold observed indices. Translating the source
samples by this mask is an involution and preserves all those observations.
Distributional consequences require uniformly sampled source values and are
proved separately; these identities make no randomness assumptions.
-/

namespace Codex32.Field

set_option maxHeartbeats 0

/-- The normalized vanishing mask. When `secretIndex` is not observed, its
basis factor is the product of `(x + j) / (secretIndex + j)` over observations.
The executable field has characteristic two, so addition is subtraction. -/
def secrecyMask (secretIndex delta : Symbol) (observed : List Symbol)
    (x : Symbol) : Symbol :=
  mul delta (basis observed secretIndex x)

theorem secrecyMask_secret (secretIndex delta : Symbol) (observed : List Symbol) :
    secrecyMask secretIndex delta observed secretIndex = delta := by
  rw [secrecyMask, basis_self, mul_one]

theorem secrecyMask_observed (secretIndex delta : Symbol) (observed : List Symbol)
    (secretNotObserved : secretIndex ∉ observed) (x : Symbol) (hx : x ∈ observed) :
    secrecyMask secretIndex delta observed x = 0 := by
  rw [secrecyMask, basis_other observed secretIndex x hx
    (fun h => secretNotObserved (h ▸ hx)), mul_zero]

/-- The product representation has no skipped factors when the secret index
is excluded. In particular, every divisor in it is nonzero. -/
theorem secrecyMask_product (secretIndex delta : Symbol) (observed : List Symbol)
    (secretNotObserved : secretIndex ∉ observed) (x : Symbol) :
    secrecyMask secretIndex delta observed x =
      mul delta (observed.foldr
        (fun j rest => mul (div (add x j) (add secretIndex j)) rest) 1) := by
  unfold secrecyMask
  congr 1
  induction observed with
  | nil => rfl
  | cons j js ih =>
    have hne : secretIndex ≠ j := fun h => secretNotObserved (by simp [h])
    have htail : secretIndex ∉ js := fun h => secretNotObserved (by simp [h])
    simp only [basis, beq_eq_false_iff_ne.mpr hne, Bool.false_eq_true,
      ↓reduceIte, List.foldr_cons, ih htail]

theorem secrecyMask_denominator_nonzero (secretIndex : Symbol) (observed : List Symbol)
    (secretNotObserved : secretIndex ∉ observed) (j : Symbol) (hj : j ∈ observed) :
    add secretIndex j ≠ 0 := by
  intro h
  exact secretNotObserved ((add_eq_zero _ _).mp h ▸ hj)

theorem secrecyMask_degree (secretIndex delta : Symbol) (observed : List Symbol)
    (k : Nat) (fewObserved : observed.length < k) :
    DegreeLT k (secrecyMask secretIndex delta observed) := by
  exact ((basis_degree observed secretIndex).scale_closed delta).weaken (by
    have := List.length_filter_le (fun j => secretIndex != j) observed
    omega)

/-- Translate each source value by the evaluation of a fixed polynomial.
Source indices and their order are unchanged. -/
def shiftSamples (f : Symbol → Symbol) (points : List (Symbol × Symbol)) :
    List (Symbol × Symbol) :=
  points.map (fun p => (p.1, add p.2 (f p.1)))

@[simp] theorem shiftSamples_length (f : Symbol → Symbol) (points : List (Symbol × Symbol)) :
    (shiftSamples f points).length = points.length := by
  simp [shiftSamples]

@[simp] theorem shiftSamples_indices (f : Symbol → Symbol) (points : List (Symbol × Symbol)) :
    (shiftSamples f points).map Prod.fst = points.map Prod.fst := by
  simp [shiftSamples, List.map_map, Function.comp_def]

/-- Translation by a fixed mask is its own inverse in characteristic two. -/
theorem shiftSamples_involutive (f : Symbol → Symbol) (points : List (Symbol × Symbol)) :
    shiftSamples f (shiftSamples f points) = points := by
  simp [shiftSamples, List.map_map, Function.comp_def, add_assoc, add_self, add_zero]

/-- Translating distinct source samples by any polynomial below the source
degree bound translates the executable interpolant by that same polynomial. -/
theorem interpolate_shiftSamples (points : List (Symbol × Symbol))
    (distinct : (points.map Prod.fst).Nodup) (f : Symbol → Symbol)
    (hf : DegreeLT points.length f) (target : Symbol) :
    interpolate (shiftSamples f points) target = add (interpolate points target) (f target) := by
  have hshift : DegreeLT points.length (interpolate (shiftSamples f points)) := by
    simpa only [shiftSamples_length] using interpolate_degree (shiftSamples f points)
  apply DegreeLT.unique hshift ((interpolate_degree points).add_closed hf)
    (points.map Prod.fst) distinct (by simp) _ target
  intro x hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  have hnew := interpolate_existing (shiftSamples f points)
    (by simpa only [shiftSamples_indices] using distinct)
    (p.1, add p.2 (f p.1)) (List.mem_map.mpr ⟨p, hp, rfl⟩)
  change interpolate (shiftSamples f points) p.1 = add p.2 (f p.1) at hnew
  rw [hnew, interpolate_existing points distinct p hp]

/-- Specialized executable interpolation identity for the secrecy mask. -/
theorem interpolate_shift_secrecyMask (points : List (Symbol × Symbol))
    (distinct : (points.map Prod.fst).Nodup) (secretIndex delta : Symbol)
    (observed : List Symbol) (fewObserved : observed.length < points.length)
    (target : Symbol) :
    interpolate (shiftSamples (secrecyMask secretIndex delta observed) points) target =
      add (interpolate points target) (secrecyMask secretIndex delta observed target) :=
  interpolate_shiftSamples points distinct _
    (secrecyMask_degree secretIndex delta observed points.length fewObserved) target

theorem interpolate_shift_secrecyMask_observed (points : List (Symbol × Symbol))
    (distinct : (points.map Prod.fst).Nodup) (secretIndex delta : Symbol)
    (observed : List Symbol) (secretNotObserved : secretIndex ∉ observed)
    (fewObserved : observed.length < points.length) (x : Symbol) (hx : x ∈ observed) :
    interpolate (shiftSamples (secrecyMask secretIndex delta observed) points) x =
      interpolate points x := by
  rw [interpolate_shift_secrecyMask points distinct secretIndex delta observed fewObserved,
    secrecyMask_observed secretIndex delta observed secretNotObserved x hx, add_zero]

theorem interpolate_shift_secrecyMask_secret (points : List (Symbol × Symbol))
    (distinct : (points.map Prod.fst).Nodup) (secretIndex delta : Symbol)
    (observed : List Symbol) (fewObserved : observed.length < points.length) :
    interpolate (shiftSamples (secrecyMask secretIndex delta observed) points) secretIndex =
      add (interpolate points secretIndex) delta := by
  rw [interpolate_shift_secrecyMask points distinct secretIndex delta observed fewObserved,
    secrecyMask_secret]

/-- For a source whose head is its secret sample, mask translation changes the
secret to any requested value while translating only the other sample values. -/
theorem shiftSamples_change_secret (secretIndex secret replacement : Symbol)
    (observed : List Symbol) (randomSamples : List (Symbol × Symbol)) :
    shiftSamples (secrecyMask secretIndex (add secret replacement) observed)
      ((secretIndex, secret) :: randomSamples) =
      (secretIndex, replacement) ::
        shiftSamples (secrecyMask secretIndex (add secret replacement) observed) randomSamples := by
  simp only [shiftSamples, List.map_cons, secrecyMask_secret]
  rw [add_cancel_left]

/-- Arbitrary two secrets yield the same observations after an involutive
translation of the remaining source values. This includes observations at
original random-sample indices as well as at derived-share indices. -/
theorem change_secret_preserves_observations (secretIndex secret replacement : Symbol)
    (randomSamples : List (Symbol × Symbol))
    (distinct : (((secretIndex, secret) :: randomSamples).map Prod.fst).Nodup)
    (observed : List Symbol) (secretNotObserved : secretIndex ∉ observed)
    (fewObserved : observed.length < randomSamples.length + 1) :
    observed.map (interpolate ((secretIndex, replacement) ::
      shiftSamples (secrecyMask secretIndex (add secret replacement) observed) randomSamples)) =
      observed.map (interpolate ((secretIndex, secret) :: randomSamples)) := by
  rw [← shiftSamples_change_secret secretIndex secret replacement observed randomSamples]
  apply List.map_congr_left
  intro x hx
  exact interpolate_shift_secrecyMask_observed _ distinct secretIndex _ observed
    secretNotObserved (by simpa only [List.length_cons] using fewObserved) x hx

end Codex32.Field
