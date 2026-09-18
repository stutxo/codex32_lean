import Codex32Proofs.Field

/-!
General Lagrange interpolation and recovery for the executable implementation.
The recursive `basis` and `weightedSum` views are proved equal to the executable
folds. Each basis has degree below the point count; distinct-node interpolation
and polynomial uniqueness then prove recovery from any equal-sized subset.
No restrictions on threshold, secret symbols, padding or randomness are needed
for these algebraic identities. Protocol validation is proved separately.
-/

namespace Codex32.Field

set_option maxHeartbeats 0
set_option maxRecDepth 10000

/-- Recursive view of an executable Lagrange basis weight. -/
def basis : List Symbol → Symbol → Symbol → Symbol
  | [], _, _ => 1
  | j :: js, i, x =>
    if i == j then basis js i x
    else mul (div (add x j) (add i j)) (basis js i x)

theorem basis_fold (indices : List Symbol) (i x acc : Symbol) :
    indices.foldl (fun product j => if i == j then product
      else mul product (div (add x j) (add i j))) acc = mul acc (basis indices i x) := by
  induction indices generalizing acc with
  | nil => simp [basis, mul_one]
  | cons j js ih =>
    simp only [List.foldl_cons, basis]
    split
    · exact ih acc
    · rw [ih, mul_assoc]

theorem lagrange_basis (indices : List Symbol) (x : Symbol) :
    lagrange indices x = indices.map (fun i => basis indices i x) := by
  simp only [lagrange, basis_fold, one_mul]

def weightedSum (indices : List Symbol) (points : List (Symbol × Symbol)) (x : Symbol) : Symbol :=
  points.foldr (fun p sum => add (mul (basis indices p.1 x) p.2) sum) 0

theorem weighted_fold (indices : List Symbol) (points : List (Symbol × Symbol)) (x acc : Symbol) :
    ((points.map (fun p => basis indices p.1 x)).zip points).foldl
      (fun sum (weight, point) => add sum (mul weight point.2)) acc =
      add acc (weightedSum indices points x) := by
  induction points generalizing acc with
  | nil => simp [weightedSum, add_zero]
  | cons p points ih =>
    simp only [List.map_cons, List.zip_cons_cons, List.foldl_cons]
    rw [ih]
    simp only [weightedSum, List.foldr_cons]
    rw [add_assoc]

theorem interpolate_weightedSum (points : List (Symbol × Symbol)) (x : Symbol) :
    interpolate points x = weightedSum (points.map Prod.fst) points x := by
  simp only [interpolate, lagrange_basis, List.map_map, Function.comp_def]
  rw [weighted_fold, zero_add]

theorem basis_degree (indices : List Symbol) (i : Symbol) :
    DegreeLT ((indices.filter (fun j => i != j)).length + 1) (basis indices i) := by
  induction indices with
  | nil => exact DegreeLT.constant 1
  | cons j js ih =>
    by_cases hij : i = j
    · subst j
      simpa only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
        basis, beq_self_eq_true] using ih
    · have hfactor : ∀ x, div (add x j) (add i j) =
          add (mul j (inv (add i j))) (mul (inv (add i j)) x) := by
        intro x
        rw [div, add_mul, mul_comm x, add_comm]
      have h := DegreeLT.linear_mul ih (mul j (inv (add i j))) (inv (add i j))
      simpa only [List.filter_cons, bne_iff_ne.mpr hij, ↓reduceIte, List.length_cons,
        basis, beq_eq_false_iff_ne.mpr hij, Bool.false_eq_true, hfactor] using h

theorem filter_basis_bound (indices : List Symbol) (i : Symbol) (hi : i ∈ indices) :
    (indices.filter (fun j => i != j)).length + 1 ≤ indices.length := by
  induction indices with
  | nil => simp at hi
  | cons j js ih =>
    by_cases hij : i = j
    · subst j
      simpa only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
        List.length_cons, Nat.add_le_add_iff_right] using
        (List.length_filter_le (fun j => i != j) js)
    · have hi' : i ∈ js := (List.mem_cons.mp hi).resolve_left hij
      have h := ih hi'
      simpa only [List.filter_cons, bne_iff_ne.mpr hij, ↓reduceIte, List.length_cons,
        Nat.add_le_add_iff_right] using h

theorem basis_degree_of_mem (indices : List Symbol) (i : Symbol) (hi : i ∈ indices) :
    DegreeLT indices.length (basis indices i) :=
  (basis_degree indices i).weaken (filter_basis_bound indices i hi)

theorem weightedSum_degree (indices : List Symbol) (points : List (Symbol × Symbol))
    (membership : ∀ p ∈ points, p.1 ∈ indices) : DegreeLT indices.length (weightedSum indices points) := by
  induction points with
  | nil => exact DegreeLT.zero_at _
  | cons p points ih =>
    have hfirst := DegreeLT.scale_closed (basis_degree_of_mem indices p.1 (membership p (by simp))) p.2
    have hrest := ih (by intro p hp; exact membership p (by simp [hp]))
    have h := DegreeLT.add_closed hfirst hrest
    change DegreeLT indices.length (fun x => add (mul (basis indices p.1 x) p.2)
      (weightedSum indices points x))
    simpa only [mul_comm p.2] using h

theorem interpolate_degree (points : List (Symbol × Symbol)) :
    DegreeLT points.length (interpolate points) := by
  have h := weightedSum_degree (points.map Prod.fst) points (by
    intro p hp; exact List.mem_map.mpr ⟨p, hp, rfl⟩)
  rw [show interpolate points = weightedSum (points.map Prod.fst) points from
    funext (interpolate_weightedSum points)]
  simpa only [List.length_map] using h

theorem basis_self (indices : List Symbol) (i : Symbol) : basis indices i i = 1 := by
  induction indices with
  | nil => rfl
  | cons j js ih =>
    by_cases hij : i = j
    · subst j
      simp only [basis, beq_self_eq_true, ↓reduceIte, ih]
    · have hdenom : add i j ≠ 0 := fun h => hij ((add_eq_zero i j).mp h)
      simp only [basis, beq_eq_false_iff_ne.mpr hij, Bool.false_eq_true, ↓reduceIte,
        div, mul_inv _ hdenom, ih, one_mul]

theorem basis_other (indices : List Symbol) (i x : Symbol) (member : x ∈ indices)
    (different : i ≠ x) : basis indices i x = 0 := by
  induction indices with
  | nil => simp at member
  | cons j js ih =>
    by_cases hij : i = j
    · have hx : x ∈ js := by
        rcases List.mem_cons.mp member with h | h
        · exact False.elim (different (hij.trans h.symm))
        · exact h
      simp only [basis, beq_iff_eq.mpr hij, ↓reduceIte]
      exact ih hx
    · simp only [basis, beq_eq_false_iff_ne.mpr hij, Bool.false_eq_true, ↓reduceIte]
      rcases List.mem_cons.mp member with hx | hx
      · subst x
        simp [div, add_self, zero_mul]
      · rw [ih hx, mul_zero]

theorem weightedSum_zero (indices : List Symbol) (points : List (Symbol × Symbol))
    (x : Symbol) (zeros : ∀ p ∈ points, basis indices p.1 x = 0) :
    weightedSum indices points x = 0 := by
  induction points with
  | nil => rfl
  | cons p points ih =>
    change add (mul (basis indices p.1 x) p.2) (weightedSum indices points x) = 0
    rw [zeros p (by simp), zero_mul, zero_add]
    apply ih
    intro q hq
    exact zeros q (by simp [hq])

theorem weightedSum_existing (indices : List Symbol) (points : List (Symbol × Symbol))
    (distinct : (points.map Prod.fst).Nodup) (p : Symbol × Symbol) (member : p ∈ points)
    (indexMember : p.1 ∈ indices) : weightedSum indices points p.1 = p.2 := by
  induction points with
  | nil => simp at member
  | cons q points ih =>
    have hd := List.nodup_cons.mp distinct
    change add (mul (basis indices q.1 p.1) q.2) (weightedSum indices points p.1) = p.2
    rcases List.mem_cons.mp member with hp | hp
    · subst p
      rw [basis_self, one_mul]
      have hz : weightedSum indices points q.1 = 0 := weightedSum_zero _ _ _ (by
        intro r hr
        apply basis_other _ _ _ indexMember
        intro heq
        apply hd.1
        exact List.mem_map.mpr ⟨r, hr, heq⟩)
      rw [hz, add_zero]
    · have hneq : q.1 ≠ p.1 := by
        intro heq
        apply hd.1
        exact List.mem_map.mpr ⟨p, hp, heq.symm⟩
      rw [basis_other indices q.1 p.1 indexMember hneq, zero_mul, zero_add]
      exact ih hd.2 hp

theorem interpolate_existing (points : List (Symbol × Symbol))
    (distinct : (points.map Prod.fst).Nodup) (p : Symbol × Symbol) (member : p ∈ points) :
    interpolate points p.1 = p.2 := by
  rw [interpolate_weightedSum]
  exact weightedSum_existing _ _ distinct p member (List.mem_map.mpr ⟨p, member, rfl⟩)

/-- Sampling an interpolated polynomial at any equally sized, distinct set of
indices and interpolating those samples recovers the same polynomial. No
restriction on threshold or on field-element values is assumed. -/
theorem interpolate_reinterpolate (points : List (Symbol × Symbol)) (indices : List Symbol)
    (distinct : indices.Nodup) (sameLength : indices.length = points.length) (target : Symbol) :
    interpolate (indices.map fun i => (i, interpolate points i)) target = interpolate points target := by
  let sampled := indices.map fun i => (i, interpolate points i)
  have hnew : DegreeLT points.length (interpolate sampled) := by
    simpa only [sampled, List.length_map, sameLength] using interpolate_degree sampled
  apply DegreeLT.unique hnew (interpolate_degree points) indices distinct (by omega) _ target
  intro i hi
  exact interpolate_existing sampled (by simpa [sampled, List.map_map, Function.comp_def] using distinct)
    (i, interpolate points i) (List.mem_map.mpr ⟨i, hi, rfl⟩)

/-- Any equal-sized distinct set of correctly generated scalar samples recovers
the original secret at index `s` (field value 16). Arbitrary symbol values are
allowed, and no assumption about an entropy source is required for correctness. -/
theorem recover_generated_column (points : List (Symbol × Symbol))
    (sourceDistinct : (points.map Prod.fst).Nodup) (secret : Symbol)
    (secretPresent : (16, secret) ∈ points) (indices : List Symbol)
    (distinct : indices.Nodup) (sameLength : indices.length = points.length) :
    interpolate (indices.map fun i => (i, interpolate points i)) 16 = secret := by
  rw [interpolate_reinterpolate points indices distinct sameLength]
  exact interpolate_existing points sourceDistinct (16, secret) secretPresent

end Codex32.Field
