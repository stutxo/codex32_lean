import Codex32Proofs.Recovery

/-!
Equivalence of the optimized `bech32_lagrange` in the pinned BIP 93 snapshot
and the executable standard Lagrange product at fresh targets. The reference
helper is transcribed over the same five-bit field operations, retaining its
numerator fold, denominator folds, and final multiplication by table inverses.
This theorem concerns the weights, not the full-message reference helper.
-/

namespace Codex32.Field

set_option maxHeartbeats 0
set_option maxRecDepth 10000

/-- BIP 93's inline `bech32_lagrange`, with `^` represented by field addition
and `BECH32_INV` represented by the executable inverse table. -/
def referenceLagrange (indices : List Symbol) (target : Symbol) : List Symbol :=
  let numerator := indices.foldl (fun product i => mul product (add i target)) 1
  let denominators := indices.map fun i =>
    indices.foldl (fun product j => mul product (add (if i == j then target else i) j)) 1
  denominators.map fun denominator => mul numerator (inv denominator)

private theorem inv_mul (a b : Symbol) : inv (mul a b) = mul (inv a) (inv b) := by
  revert a b
  decide +kernel

private theorem mul_pair (a b c d : Symbol) :
    mul (mul a b) (mul c d) = mul (mul a c) (mul b d) := by
  rw [mul_assoc, mul_left_comm b c, ← mul_assoc, ← mul_assoc]

private def product (f : Symbol → Symbol) : List Symbol → Symbol
  | [] => 1
  | j :: js => mul (f j) (product f js)

private theorem product_fold (f : Symbol → Symbol) (indices : List Symbol) (acc : Symbol) :
    indices.foldl (fun p j => mul p (f j)) acc = mul acc (product f indices) := by
  induction indices generalizing acc with
  | nil => simp [product, mul_one]
  | cons j js ih => simp only [List.foldl_cons, product, ih, mul_assoc]

private theorem quotient_products (numerator denominator : Symbol → Symbol)
    (indices : List Symbol) :
    mul (product numerator indices) (inv (product denominator indices)) =
      product (fun j => div (numerator j) (denominator j)) indices := by
  induction indices with
  | nil =>
    change mul 1 (inv 1) = 1
    decide +kernel
  | cons j js ih =>
    simp only [product, inv_mul, mul_pair, ih, div]

private theorem reference_basis (indices : List Symbol) (i target : Symbol)
    (fresh : target ∉ indices) :
    product (fun j => div (add j target) (add (if i == j then target else i) j)) indices =
      basis indices i target := by
  induction indices with
  | nil => rfl
  | cons j js ih =>
    have freshHead : target ≠ j := fun h => fresh (List.mem_cons.mpr (Or.inl h))
    have freshTail : target ∉ js := fun h => fresh (List.mem_cons.mpr (Or.inr h))
    have nonzero : add target j ≠ 0 := fun h => freshHead ((add_eq_zero _ _).mp h)
    simp only [product, basis]
    by_cases equal : i = j
    · subst i
      simp only [beq_self_eq_true, ↓reduceIte, add_comm j target, ih freshTail]
      rw [div, mul_inv _ nonzero, one_mul]
    · simp only [beq_eq_false_iff_ne.mpr equal, Bool.false_eq_true, ↓reduceIte,
        add_comm j target, ih freshTail]

/-- At every fresh target, BIP 93's optimized weights equal the executable
standard Lagrange weights. Distinct source indices are needed to interpret
the weights as interpolation, but the equality itself does not require them. -/
theorem referenceLagrange_eq_lagrange (indices : List Symbol) (target : Symbol)
    (fresh : target ∉ indices) : referenceLagrange indices target = lagrange indices target := by
  simp only [referenceLagrange, product_fold, one_mul, List.map_map, Function.comp_def,
    lagrange_basis]
  apply List.map_congr_left
  intro i _
  rw [quotient_products, reference_basis indices i target fresh]

end Codex32.Field
