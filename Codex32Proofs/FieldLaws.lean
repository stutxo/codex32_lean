import Codex32.Field

/-! Kernel-checked algebraic laws of the executable 32-element field. -/
namespace Codex32.Field

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem add_assoc : ∀ a b c : Symbol, add (add a b) c = add a (add b c) := by
  decide +kernel

theorem add_comm : ∀ a b : Symbol, add a b = add b a := by decide +kernel
theorem add_zero : ∀ a : Symbol, add a 0 = a := by decide +kernel
theorem add_self : ∀ a : Symbol, add a a = 0 := by decide +kernel
theorem mul_comm : ∀ a b : Symbol, mul a b = mul b a := by decide +kernel
theorem mul_zero : ∀ a : Symbol, mul a 0 = 0 := by decide +kernel
theorem mul_one : ∀ a : Symbol, mul a 1 = a := by decide +kernel
theorem mul_inv : ∀ a : Symbol, a ≠ 0 → mul a (inv a) = 1 := by decide +kernel

theorem mul_assoc : ∀ a b c : Symbol, mul (mul a b) c = mul a (mul b c) := by
  decide +kernel

theorem mul_add : ∀ a b c : Symbol, mul a (add b c) = add (mul a b) (mul a c) := by
  decide +kernel

theorem mul_eq_zero : ∀ a b : Symbol, mul a b = 0 ↔ a = 0 ∨ b = 0 := by
  decide +kernel

end Codex32.Field
