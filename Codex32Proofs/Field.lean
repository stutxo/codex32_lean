import Codex32Proofs.FieldLaws

/-!
Proof-only polynomial functions over the executable GF(32) operations. `DegreeLT`
records a bounded Horner expression without adding a polynomial dependency.
Divided differences reduce the degree bound and yield the distinct-root
uniqueness theorem used to prove general Shamir recovery.
-/

namespace Codex32.Field

set_option maxHeartbeats 0
set_option maxRecDepth 10000

@[simp] theorem zero_add (a : Symbol) : add 0 a = a := by rw [add_comm, add_zero]
@[simp] theorem zero_mul (a : Symbol) : mul 0 a = 0 := by rw [mul_comm, mul_zero]
@[simp] theorem one_mul (a : Symbol) : mul 1 a = a := by rw [mul_comm, mul_one]
@[simp] theorem add_eq_zero (a b : Symbol) : add a b = 0 ↔ a = b := by
  constructor
  · intro h
    have := congrArg (add a) h
    simpa [← add_assoc, add_self, zero_add, add_zero] using this.symm
  · rintro rfl; exact add_self _
theorem add_mul (a b c : Symbol) : mul (add a b) c = add (mul a c) (mul b c) := by
  rw [mul_comm, mul_add, mul_comm c a, mul_comm c b]
theorem add_left_comm (a b c : Symbol) : add a (add b c) = add b (add a c) := by
  rw [← add_assoc, add_comm a b, add_assoc]
theorem mul_left_comm (a b c : Symbol) : mul a (mul b c) = mul b (mul a c) := by
  rw [← mul_assoc, mul_comm a b, mul_assoc]
theorem add_pair (a b c d : Symbol) : add (add a b) (add c d) = add (add a c) (add b d) := by
  rw [add_assoc, add_left_comm b c, ← add_assoc]
theorem add_cancel_left (a b : Symbol) : add a (add a b) = b := by
  rw [← add_assoc, add_self, zero_add]

/-- A polynomial function with degree strictly less than its natural-number
bound, represented by a Horner expression. Zero is permitted at every bound. -/
inductive DegreeLT : Nat → (Symbol → Symbol) → Prop where
  | zero : DegreeLT 0 (fun _ => 0)
  | horner {n : Nat} {f : Symbol → Symbol} (a : Symbol) (hf : DegreeLT n f) :
      DegreeLT (n+1) (fun x => add a (mul x (f x)))

namespace DegreeLT

theorem zero_at (n : Nat) : DegreeLT n (fun _ => 0) := by
  induction n with
  | zero => exact .zero
  | succ n ih =>
    have h := horner 0 ih
    simpa only [mul_zero, add_zero] using h

theorem add_closed {n : Nat} {f g : Symbol → Symbol}
    (hf : DegreeLT n f) (hg : DegreeLT n g) : DegreeLT n (fun x => add (f x) (g x)) := by
  induction hf generalizing g with
  | zero => cases hg; simpa only [add_zero] using DegreeLT.zero
  | horner a hf ih =>
    cases hg with
    | horner b hg =>
      have h := horner (add a b) (ih hg)
      simpa only [mul_add, add_pair] using h

theorem scale_closed {n : Nat} {f : Symbol → Symbol}
    (hf : DegreeLT n f) (c : Symbol) : DegreeLT n (fun x => mul c (f x)) := by
  induction hf with
  | zero => simpa only [mul_zero] using DegreeLT.zero
  | @horner n f a hf ih =>
    have h := horner (mul c a) ih
    simpa only [mul_add, mul_left_comm c] using h

theorem weaken_one {n : Nat} {f : Symbol → Symbol} (hf : DegreeLT n f) : DegreeLT (n+1) f := by
  induction hf with
  | zero => exact zero_at 1
  | horner a hf ih => exact horner a ih

theorem weaken {n m : Nat} {f : Symbol → Symbol} (hf : DegreeLT n f)
    (hnm : n ≤ m) : DegreeLT m f := by
  induction hnm with
  | refl => exact hf
  | step h ih => exact weaken_one ih

theorem constant (a : Symbol) : DegreeLT 1 (fun _ => a) := by
  simpa only [mul_zero, add_zero] using (horner a DegreeLT.zero)

theorem linear_mul {n : Nat} {f : Symbol → Symbol} (hf : DegreeLT n f)
    (a b : Symbol) : DegreeLT (n+1) (fun x => mul (add a (mul b x)) (f x)) := by
  have ha := (scale_closed hf a).weaken_one
  have hb := horner 0 (scale_closed hf b)
  have h := add_closed ha hb
  simpa only [zero_add, add_mul, mul_assoc, mul_comm b] using h

private theorem difference_identity (a x r b d : Symbol) :
    add a (mul x (add b (mul (add x r) d))) =
    add (add a (mul r b)) (mul (add x r) (add b (mul x d))) := by
  simp only [mul_add, add_mul]
  rw [mul_left_comm r x d]
  rw [add_assoc a]
  rw [add_assoc (mul x b) (mul r b)]
  rw [add_left_comm (mul r b) (mul x b)]
  rw [add_cancel_left]

/-- Every polynomial has a polynomial divided difference of one lower degree. -/
theorem divided_difference {n : Nat} {f : Symbol → Symbol} (hf : DegreeLT (n+1) f)
    (r : Symbol) : ∃ q, DegreeLT n q ∧
      ∀ x, f x = add (f r) (mul (add x r) (q x)) := by
  induction n generalizing f with
  | zero =>
    cases hf with
    | horner a h =>
      cases h
      exact ⟨fun _ => 0, DegreeLT.zero, by simp [mul_zero, add_zero]⟩
  | succ n ih =>
    cases hf with
    | @horner _ g a hg =>
      obtain ⟨q, hq, heq⟩ := ih hg
      refine ⟨fun x => add (g r) (mul x (q x)), horner (g r) hq, ?_⟩
      intro x
      dsimp only
      rw [heq x]
      exact difference_identity a x r (g r) (q x)

/-- A polynomial of degree less than `n` that vanishes at `n` distinct field
elements is zero everywhere. The bound may also exceed the actual degree. -/
theorem roots_zero {n : Nat} {f : Symbol → Symbol} (hf : DegreeLT n f)
    (roots : List Symbol) (distinct : roots.Nodup) (enough : n ≤ roots.length)
    (vanishes : ∀ r ∈ roots, f r = 0) : ∀ x, f x = 0 := by
  induction n generalizing f roots with
  | zero => cases hf; intro x; rfl
  | succ n ih =>
    cases roots with
    | nil => simp at enough
    | cons a roots =>
      obtain ⟨q, hq, heq⟩ := divided_difference hf a
      have ha : f a = 0 := vanishes a (by simp)
      have hdistinct := List.nodup_cons.mp distinct
      have hqzero : ∀ b ∈ roots, q b = 0 := by
        intro b hb
        have hfb : f b = 0 := vanishes b (by simp [hb])
        have hm : mul (add b a) (q b) = 0 := by
          simpa only [hfb, ha, zero_add] using (heq b).symm
        have hba : add b a ≠ 0 := by
          intro h
          have := (add_eq_zero b a).mp h
          subst b
          exact hdistinct.1 hb
        exact ((mul_eq_zero _ _).mp hm).resolve_left hba
      have hqall := ih hq roots hdistinct.2 (by simp only [List.length_cons] at enough; omega) hqzero
      intro x
      rw [heq x, ha, hqall x, mul_zero, add_zero]

/-- Two degree-bounded polynomial functions agreeing at enough distinct points
agree throughout GF(32). -/
theorem unique {n : Nat} {f g : Symbol → Symbol} (hf : DegreeLT n f) (hg : DegreeLT n g)
    (indices : List Symbol) (distinct : indices.Nodup) (enough : n ≤ indices.length)
    (agree : ∀ i ∈ indices, f i = g i) : ∀ x, f x = g x := by
  have hzero := roots_zero (add_closed hf hg) indices distinct enough
    (by intro i hi; rw [agree i hi, add_self])
  intro x
  exact (add_eq_zero _ _).mp (hzero x)

end DegreeLT
end Codex32.Field
