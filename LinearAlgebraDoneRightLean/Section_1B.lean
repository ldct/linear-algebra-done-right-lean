import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Recall
import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 1B: Definition of Vector Space
-/

namespace LADR.Section_1B

/-! 1.19–1.20 Definition: vector space

Mathlib's `Module F V` (over `[AddCommGroup V]`) is exactly Axler's "vector space
over `F`". The eight axioms are derivable from the typeclass methods. -/

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]

example (u v : V) : u + v = v + u := add_comm u v
example (u v w : V) : (u + v) + w = u + (v + w) := add_assoc u v w
example (v : V) : v + 0 = v := add_zero v
example (v : V) : v + (-v) = 0 := add_neg_cancel v
example (v : V) : (1 : F) • v = v := one_smul F v
example (a : F) (u v : V) : a • (u + v) = a • u + a • v := smul_add a u v
example (a b : F) (v : V) : (a + b) • v = a • v + b • v := add_smul a b v
example (a b : F) (v : V) : (a * b) • v = a • (b • v) := mul_smul a b v

/-! 1.21 Example: Fⁿ is a vector space over F -/

example {n : ℕ} : Module ℝ (Fin n → ℝ) := inferInstance
example {n : ℕ} : Module ℂ (Fin n → ℂ) := inferInstance

/-! 1.22 Example: F^∞ -/

example : Module ℝ (ℕ → ℝ) := inferInstance

/-! 1.23 Example: F^S -/

example (S : Type*) : Module ℝ (S → ℝ) := inferInstance

/-! 1.25 Unique additive identity

If `z + v = v` for every `v ∈ V`, then `z = 0`. The textbook proof: take `v = 0`. -/

theorem unique_zero (z : V) (h : ∀ v, v + z = v) : z = 0 := by
  have h0 : (0 : V) + z = 0 := h 0
  rwa [zero_add] at h0

/-! 1.26 Unique additive inverse

If `v + w = 0`, then `w = -v`. -/

theorem unique_neg (v w : V) (h : v + w = 0) : w = -v := by
  have : -v + (v + w) = -v + 0 := by rw [h]
  rw [← add_assoc, neg_add_cancel, zero_add, add_zero] at this
  exact this

/-! 1.29 The zero scalar annihilates every vector -/

example (v : V) : (0 : F) • v = 0 := zero_smul F v

/-! 1.30 Any scalar applied to the zero vector is zero -/

example (a : F) : a • (0 : V) = 0 := smul_zero a

/-! 1.31 `(-1) • v = -v` -/

example (v : V) : (-1 : F) • v = -v := neg_one_smul F v

/-! # Exercises -/

/-- 1B.1 Show that `-(-v) = v` for every `v ∈ V`. -/
@[avoiding neg_neg]
theorem exercise_1B_1 (v : V) : -(-v) = v := by
  sorry

/-- 1B.2 Suppose `a ∈ F`, `v ∈ V`, and `a • v = 0`. Prove `a = 0` or `v = 0`. -/
@[avoiding smul_eq_zero, smul_eq_zero_iff_eq, smul_eq_zero_iff_eq']
theorem exercise_1B_2 (a : F) (v : V) (h : a • v = 0) :
    a = 0 ∨ v = 0 := by
  sorry

/-- 1B.3 For all `v, x ∈ V`, there is a unique `t ∈ V` with `v + 3 • t = x`. -/
theorem exercise_1B_3 (v x : V) : ∃! t : V, v + (3 : F) • t = x := by
  sorry

/-- 1B.5 Show that `(2 : F) • v = v + v` for every `v ∈ V`. -/
@[avoiding two_smul]
theorem exercise_1B_5 (v : V) : (2 : F) • v = v + v := by
  sorry

end LADR.Section_1B
