import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Recall
import Mathlib.Tactic.Ring
import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 1C: Subspaces
-/

namespace LADR.Section_1C

/-! 1.33–1.34 Definition: subspace

A subset `U ⊆ V` is a subspace iff it contains `0`, is closed under addition,
and is closed under scalar multiplication. Mathlib calls this a `Submodule F V`. -/

recall Submodule.zero_mem {R : Type u} {M : Type v} [Semiring R] [AddCommMonoid M]
    {module_M : Module R M} (p : Submodule R M) : (0 : M) ∈ p
recall Submodule.add_mem {R : Type u} {M : Type v} [Semiring R] [AddCommMonoid M]
    {module_M : Module R M} (p : Submodule R M)
    {x y : M} (h₁ : x ∈ p) (h₂ : y ∈ p) : x + y ∈ p
recall Submodule.smul_mem {R : Type u} {M : Type v} [Semiring R] [AddCommMonoid M]
    {module_M : Module R M} (p : Submodule R M)
    {x : M} (r : R) (h : x ∈ p) : r • x ∈ p

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]

/-! 1.35 Examples of subspaces -/

example : Submodule F V := ⊥
example : Submodule F V := ⊤

/-- 1.35(c): the set `{(x₁, x₂, x₃) ∈ F³ | x₁ + 2 x₂ + 3 x₃ = 0}` is a subspace
of `F³`. -/
example : Submodule ℝ (Fin 3 → ℝ) where
  carrier := {v | v 0 + 2 * v 1 + 3 * v 2 = 0}
  zero_mem' := by simp
  add_mem' := by
    intro u v hu hv
    simp only [Set.mem_setOf_eq, Pi.add_apply] at *
    linarith
  smul_mem' := by
    intro a v hv
    simp only [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul] at *
    have : a * v 0 + 2 * (a * v 1) + 3 * (a * v 2) = a * (v 0 + 2 * v 1 + 3 * v 2) := by
      ring
    rw [this, hv, mul_zero]

/-- A line through the origin in `ℝ²` is a subspace. -/
def lineThrough (v : Fin 2 → ℝ) : Submodule ℝ (Fin 2 → ℝ) :=
  Submodule.span ℝ {v}

/-! 1.36–1.37 Sum of subspaces

`U + W = {u + w | u ∈ U, w ∈ W}` is the smallest subspace containing both.
Mathlib uses `⊔` (the lattice supremum). -/

example (U W : Submodule F V) : Submodule F V := U ⊔ W

example (U W : Submodule F V) (u : V) (hu : u ∈ U) :
    u ∈ U ⊔ W := by
  exact Submodule.mem_sup_left hu

/-! 1.41 Direct sum criterion

`U + W` is direct iff `U ∩ W = {0}`. Mathlib expresses this as `U ⊓ W = ⊥`. -/

theorem disjoint_iff_inter_trivial (U W : Submodule F V) :
    U ⊓ W = ⊥ ↔ ∀ v, v ∈ U → v ∈ W → v = 0 := by
  rw [Submodule.eq_bot_iff]
  refine ⟨fun h v hu hw => h v ⟨hu, hw⟩, fun h v ⟨hu, hw⟩ => h v hu hw⟩

/-! # Exercises -/

/-- 1C.1 The set `{(x₁, x₂, x₃, x₄) ∈ ℝ⁴ | x₃ = 5 x₄ + b}` is a subspace iff
`b = 0`. -/
theorem exercise_1C_1 (b : ℝ) :
    (∃ U : Submodule ℝ (Fin 4 → ℝ),
        (U : Set (Fin 4 → ℝ)) = {v | v 2 = 5 * v 3 + b}) ↔ b = 0 := by
  sorry

/-- 1C.3 The set `{v ∈ ℝ³ | v 0 + 2 v 1 + 3 v 2 = 4}` is **not** a subspace. -/
theorem exercise_1C_3 :
    ¬ ∃ U : Submodule ℝ (Fin 3 → ℝ),
      (U : Set (Fin 3 → ℝ)) = {v | v 0 + 2 * v 1 + 3 * v 2 = 4} := by
  sorry

/-- 1C.6(a) The set `{(a, b, c) ∈ ℝ³ | a^3 = b^3}` is a subspace of `ℝ³`. -/
theorem exercise_1C_6a :
    ∃ U : Submodule ℝ (Fin 3 → ℝ),
      (U : Set (Fin 3 → ℝ)) = {v | v 0 ^ 3 = v 1 ^ 3} := by
  sorry

/-- 1C.6(b) The set `{(a, b, c) ∈ ℂ³ | a^3 = b^3}` is **not** a subspace of `ℂ³`. -/
theorem exercise_1C_6b :
    ¬ ∃ U : Submodule ℂ (Fin 3 → ℂ),
      (U : Set (Fin 3 → ℂ)) = {v | v 0 ^ 3 = v 1 ^ 3} := by
  sorry

/-- 1C.8 The intersection of any two subspaces is a subspace. -/
example (U W : Submodule F V) : Submodule F V := U ⊓ W

/-- 1C.9 The union of two subspaces is a subspace iff one contains the other. -/
@[avoiding Submodule.union_eq_iff_le_or_le]
theorem exercise_1C_9 (U W : Submodule F V) :
    (∃ S : Submodule F V, (S : Set V) = (U : Set V) ∪ (W : Set V)) ↔
      U ≤ W ∨ W ≤ U := by
  sorry

/-- 1C.10 If `U` is a subspace of `V`, then `U + U = U`. -/
@[avoiding sup_idem, sup_self]
theorem exercise_1C_10 (U : Submodule F V) : U ⊔ U = U := by
  sorry

/-- 1C.12 Sum of subspaces is commutative. -/
@[avoiding sup_comm]
theorem exercise_1C_12_comm (U W : Submodule F V) : U ⊔ W = W ⊔ U := by
  sorry

/-- 1C.12 Sum of subspaces is associative. -/
@[avoiding sup_assoc]
theorem exercise_1C_12_assoc (U W X : Submodule F V) :
    (U ⊔ W) ⊔ X = U ⊔ (W ⊔ X) := by
  sorry

end LADR.Section_1C
