import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Recall
import Mathlib.Tactic.Ring
import LinearAlgebraDoneRightLean.Section_2A
import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 2B: Bases
-/

namespace LADR.Section_2B

open LADR.Section_2A (Spans)

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]

/-! 2.26 Definition: basis

A *basis* of {lit}`V` is a list of vectors in {lit}`V` that is linearly
independent and spans {lit}`V`. -/

def IsBasis (F : Type*) {V : Type*} [Field F] [AddCommGroup V] [Module F V]
    {m : ℕ} (v : Fin m → V) : Prop :=
  LinearIndependent F v ∧ Spans F v

/-! 2.27 Example: bases -/

/-! (a) The standard basis of {lit}`Fⁿ`:
{lit}`(1, 0, …, 0), (0, 1, …, 0), …, (0, …, 0, 1)`. -/

example (n : ℕ) :
    IsBasis F (fun k : Fin n => (Pi.single k (1 : F) : Fin n → F)) := by
  sorry

/-! (b) The list {lit}`(1, 2), (3, 5)` is a basis of {lit}`F²`. Note its
length is 2, the same as the length of the standard basis of {lit}`F²`; this
is no coincidence (see 2.34). -/

example : IsBasis F (![![1, 2], ![3, 5]] : Fin 2 → Fin 2 → F) := by
  sorry

/-! (c) The list {lit}`(1, 2, -4), (7, -5, 6)` is linearly independent in
{lit}`F³` but is *not* a basis: it fails to span. -/

example : LinearIndependent F (![![1, 2, -4], ![7, -5, 6]] : Fin 2 → Fin 3 → F) := by
  sorry

example : ¬ Spans F (![![1, 2, -4], ![7, -5, 6]] : Fin 2 → Fin 3 → F) := by
  sorry

/-! (d) The list {lit}`(1, 2), (3, 5), (4, 13)` spans {lit}`F²` but is not
a basis: it is linearly dependent. -/

example : Spans F (![![1, 2], ![3, 5], ![4, 13]] : Fin 3 → Fin 2 → F) := by
  sorry

example : ¬ LinearIndependent F
    (![![1, 2], ![3, 5], ![4, 13]] : Fin 3 → Fin 2 → F) := by
  sorry

/-! (e) The list {lit}`(1, 1, 0), (0, 0, 1)` is a basis of
{lit}`{(x, x, y) ∈ F³ : x, y ∈ F}`. -/

namespace Example_2_27e

def U (F : Type*) [Field F] : Submodule F (Fin 3 → F) where
  carrier := {v | v 0 = v 1}
  zero_mem' := rfl
  add_mem' := by intro u v hu hv; show u 0 + v 0 = u 1 + v 1; rw [hu, hv]
  smul_mem' := by intro a v hv; show a • v 0 = a • v 1; rw [hv]

def basisVec : Fin 2 → U F :=
  ![⟨![1, 1, 0], rfl⟩, ⟨![0, 0, 1], rfl⟩]

example : IsBasis F (basisVec (F := F)) := by sorry

end Example_2_27e

/-! (f) The list {lit}`(1, -1, 0), (1, 0, -1)` is a basis of
{lit}`{(x, y, z) ∈ F³ : x + y + z = 0}`. -/

namespace Example_2_27f

def U (F : Type*) [Field F] : Submodule F (Fin 3 → F) where
  carrier := {v | v 0 + v 1 + v 2 = 0}
  zero_mem' := by show (0 : F) + 0 + 0 = 0; ring
  add_mem' := by
    intro u v hu hv
    show (u 0 + v 0) + (u 1 + v 1) + (u 2 + v 2) = 0
    have hu' : u 0 + u 1 + u 2 = 0 := hu
    have hv' : v 0 + v 1 + v 2 = 0 := hv
    have heq : (u 0 + v 0) + (u 1 + v 1) + (u 2 + v 2) =
               (u 0 + u 1 + u 2) + (v 0 + v 1 + v 2) := by ring
    rw [heq, hu', hv', add_zero]
  smul_mem' := by
    intro a v hv
    show a • v 0 + a • v 1 + a • v 2 = 0
    simp only [smul_eq_mul]
    have hv' : v 0 + v 1 + v 2 = 0 := hv
    have heq : a * v 0 + a * v 1 + a * v 2 = a * (v 0 + v 1 + v 2) := by ring
    rw [heq, hv', mul_zero]

def basisVec : Fin 2 → U F :=
  ![⟨![1, -1, 0], by show (1 : F) + (-1) + 0 = 0; ring⟩,
    ⟨![1, 0, -1], by show (1 : F) + 0 + (-1) = 0; ring⟩]

example : IsBasis F (basisVec (F := F)) := by sorry

end Example_2_27f

/-! (g) The list {lit}`1, z, …, zᵐ` is the *standard basis* of {lit}`Pₘ(F)`. -/

example (m : ℕ) [Infinite F] : IsBasis F
    (fun i : Fin (m + 1) =>
      (⟨Polynomial.X ^ (i : ℕ), by
        rw [Polynomial.mem_degreeLT, Polynomial.degree_X_pow]
        exact_mod_cast i.isLt⟩ : Polynomial.degreeLT F (m + 1))) := by
  sorry

/-! Note: {lit}`(7, 5), (-4, 9)` and {lit}`(1, 2), (3, 5)` are both bases of
{lit}`F²`. So {lit}`Fⁿ` has many bases beyond the standard one. -/

/-! 2.28 Criterion for basis

A list {lit}`v₁, …, vₙ` is a basis of {lit}`V` iff every {lit}`v ∈ V` can be
written *uniquely* as {lit}`v = a₁ v₁ + ⋯ + aₙ vₙ` with {lit}`aᵢ ∈ F`. -/

theorem isBasis_iff_unique_combo {m : ℕ} (v : Fin m → V) :
    IsBasis F v ↔ ∀ u : V, ∃! a : Fin m → F, ∑ i, a i • v i = u := by
  sorry

/-! 2.30 Every spanning list contains a basis

Every spanning list in a vector space can be reduced to a basis by iterating
the rule "drop {lit}`vₖ` if it lies in the span of {lit}`v₁, …, v_{k-1}`". -/

theorem exists_basis_of_spans {m : ℕ} (v : Fin m → V) (hv : Spans F v) :
    ∃ (n : ℕ) (vs : Fin n → V), IsBasis F vs ∧ Set.range vs ⊆ Set.range v := by
  sorry

/-! 2.31 Basis of finite-dimensional vector space

Every finite-dimensional vector space has a basis: apply 2.30 to a spanning
list given by finite-dimensionality. -/

theorem exists_basis [Module.Finite F V] :
    ∃ (n : ℕ) (v : Fin n → V), IsBasis F v := by
  sorry

/-! 2.32 Every linearly independent list extends to a basis

Every linearly independent list in a finite-dimensional vector space can be
extended (by adjoining further vectors) to a basis of the space. -/

theorem exists_basis_extending [Module.Finite F V] {m : ℕ} (v : Fin m → V)
    (hv : LinearIndependent F v) :
    ∃ (n : ℕ) (hmn : m ≤ n) (w : Fin n → V), IsBasis F w ∧
      ∀ i : Fin m, w (Fin.castLE hmn i) = v i := by
  sorry

/-! 2.33 Every subspace of {lit}`V` is part of a direct sum equal to {lit}`V`

If {lit}`V` is finite-dimensional and {lit}`U` is a subspace of {lit}`V`,
then there is a subspace {lit}`W` of {lit}`V` such that {lit}`V = U ⊕ W`. -/

theorem exists_isCompl [Module.Finite F V] (U : Submodule F V) :
    ∃ W : Submodule F V, IsCompl U W := by
  sorry

/-! # Exercises -/

/-- 2B.1 Find all vector spaces that have exactly one basis.

(Answer: the trivial space {lit}`{0}`. Equivalently, every basis has length
zero iff {lit}`V` is a subsingleton.) -/
theorem exercise_2B_1 :
    (∀ {n : ℕ} (v : Fin n → V), IsBasis F v → n = 0) ↔ Subsingleton V := by
  sorry

/-! 2B.2 Verify the assertions in Example 2.27. (Already stated above as
`example`s; this exercise is the union of those proofs.) -/

/-- 2B.3 Let {lit}`U = {(x₁, x₂, x₃, x₄, x₅) ∈ ℝ⁵ : x₁ = 3x₂ ∧ x₃ = 7x₄}`. -/
def exercise_2B_3_U : Submodule ℝ (Fin 5 → ℝ) where
  carrier := {v | v 0 = 3 * v 1 ∧ v 2 = 7 * v 3}
  zero_mem' := ⟨by simp, by simp⟩
  add_mem' := by
    rintro u v ⟨h1, h2⟩ ⟨h1', h2'⟩
    refine ⟨?_, ?_⟩
    · show u 0 + v 0 = 3 * (u 1 + v 1); rw [h1, h1']; ring
    · show u 2 + v 2 = 7 * (u 3 + v 3); rw [h2, h2']; ring
  smul_mem' := by
    rintro a v ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · show a • v 0 = 3 * (a • v 1); simp only [smul_eq_mul]; rw [h1]; ring
    · show a • v 2 = 7 * (a • v 3); simp only [smul_eq_mul]; rw [h2]; ring

/-- 2B.3(a) Find a basis of {lit}`U`. -/
theorem exercise_2B_3a :
    ∃ (n : ℕ) (v : Fin n → exercise_2B_3_U), IsBasis ℝ v := by
  sorry

/-- 2B.3(b) Extend the basis of {lit}`U` to a basis of {lit}`ℝ⁵`. -/
theorem exercise_2B_3b :
    ∃ (n : ℕ) (v : Fin n → (Fin 5 → ℝ)), IsBasis ℝ v ∧
      (Set.range (fun i : exercise_2B_3_U => (i : Fin 5 → ℝ))) ⊆
        Submodule.span ℝ (Set.range v) := by
  sorry

/-- 2B.3(c) Find {lit}`W ≤ ℝ⁵` with {lit}`ℝ⁵ = U ⊕ W`. -/
theorem exercise_2B_3c :
    ∃ W : Submodule ℝ (Fin 5 → ℝ), IsCompl exercise_2B_3_U W := by
  sorry

/-- 2B.4 Let {lit}`U = {(z₁, z₂, z₃, z₄, z₅) ∈ ℂ⁵ : 6z₁ = z₂ ∧ z₃ + 2z₄ + 3z₅ = 0}`. -/
def exercise_2B_4_U : Submodule ℂ (Fin 5 → ℂ) where
  carrier := {v | 6 * v 0 = v 1 ∧ v 2 + 2 * v 3 + 3 * v 4 = 0}
  zero_mem' := ⟨by simp, by simp⟩
  add_mem' := by
    rintro u v ⟨h1, h2⟩ ⟨h1', h2'⟩
    refine ⟨?_, ?_⟩
    · show 6 * (u 0 + v 0) = u 1 + v 1
      have : 6 * (u 0 + v 0) = 6 * u 0 + 6 * v 0 := by ring
      rw [this, h1, h1']
    · show (u 2 + v 2) + 2 * (u 3 + v 3) + 3 * (u 4 + v 4) = 0
      have heq : (u 2 + v 2) + 2 * (u 3 + v 3) + 3 * (u 4 + v 4) =
                 (u 2 + 2 * u 3 + 3 * u 4) + (v 2 + 2 * v 3 + 3 * v 4) := by ring
      rw [heq, h2, h2', add_zero]
  smul_mem' := by
    rintro a v ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · show 6 * (a • v 0) = a • v 1
      simp only [smul_eq_mul]
      have : 6 * (a * v 0) = a * (6 * v 0) := by ring
      rw [this, h1]
    · show a • v 2 + 2 * (a • v 3) + 3 * (a • v 4) = 0
      simp only [smul_eq_mul]
      have heq : a * v 2 + 2 * (a * v 3) + 3 * (a * v 4) =
                 a * (v 2 + 2 * v 3 + 3 * v 4) := by ring
      rw [heq, h2, mul_zero]

/-- 2B.4(a) Find a basis of {lit}`U`. -/
theorem exercise_2B_4a :
    ∃ (n : ℕ) (v : Fin n → exercise_2B_4_U), IsBasis ℂ v := by
  sorry

/-- 2B.4(b) Extend the basis to a basis of {lit}`ℂ⁵`. -/
theorem exercise_2B_4b :
    ∃ (n : ℕ) (v : Fin n → (Fin 5 → ℂ)), IsBasis ℂ v ∧
      (Set.range (fun i : exercise_2B_4_U => (i : Fin 5 → ℂ))) ⊆
        Submodule.span ℂ (Set.range v) := by
  sorry

/-- 2B.4(c) Find {lit}`W ≤ ℂ⁵` with {lit}`ℂ⁵ = U ⊕ W`. -/
theorem exercise_2B_4c :
    ∃ W : Submodule ℂ (Fin 5 → ℂ), IsCompl exercise_2B_4_U W := by
  sorry

/-- 2B.5 Suppose {lit}`V` is finite-dimensional and {lit}`U, W` are subspaces
of {lit}`V` such that {lit}`V = U + W`. Prove that there exists a basis of
{lit}`V` consisting of vectors in {lit}`U ∪ W`. -/
theorem exercise_2B_5 [Module.Finite F V] (U W : Submodule F V) (hUW : U ⊔ W = ⊤) :
    ∃ (n : ℕ) (v : Fin n → V), IsBasis F v ∧
      ∀ i, (v i ∈ U) ∨ (v i ∈ W) := by
  sorry

/-- 2B.6 Prove or counterexample: if {lit}`p₀, p₁, p₂, p₃` is a list in
{lit}`P₃(F)` such that none of {lit}`pᵢ` has degree {lit}`2`, then
{lit}`p₀, p₁, p₂, p₃` is *not* a basis of {lit}`P₃(F)`. -/
def exercise_2B_6 :
    Decidable (∀ (p : Fin 4 → Polynomial.degreeLT F 4),
      (∀ i, (p i : Polynomial F).degree ≠ 2) → ¬ IsBasis F p) := by
  -- first line should be `apply isTrue` or `apply isFalse`
  sorry

/-- 2B.7 Suppose {lit}`v₁, v₂, v₃, v₄` is a basis of {lit}`V`. Prove that
{lit}`v₁ + v₂, v₂ + v₃, v₃ + v₄, v₄` is also a basis of {lit}`V`. -/
theorem exercise_2B_7 (v : Fin 4 → V) (hv : IsBasis F v) :
    IsBasis F (![v 0 + v 1, v 1 + v 2, v 2 + v 3, v 3] : Fin 4 → V) := by
  sorry

/-- 2B.8 Prove or counterexample: if {lit}`v₁, v₂, v₃, v₄` is a basis of
{lit}`V` and {lit}`U` is a subspace of {lit}`V` with {lit}`v₁, v₂ ∈ U` and
{lit}`v₃ ∉ U` and {lit}`v₄ ∉ U`, then {lit}`v₁, v₂` is a basis of {lit}`U`. -/
def exercise_2B_8 :
    Decidable (∀ (v : Fin 4 → V) (U : Submodule F V) (_ : IsBasis F v)
      (h0 : v 0 ∈ U) (h1 : v 1 ∈ U) (_ : v 2 ∉ U) (_ : v 3 ∉ U),
      IsBasis F (![⟨v 0, h0⟩, ⟨v 1, h1⟩] : Fin 2 → U)) := by
  -- first line should be `apply isTrue` or `apply isFalse`
  sorry

/-- 2B.9 Suppose {lit}`v₁, …, vₘ` is a list in {lit}`V`. For
{lit}`k ∈ {1, …, m}`, let {lit}`wₖ = v₁ + ⋯ + vₖ`. Show that {lit}`v` is a
basis of {lit}`V` iff {lit}`w` is a basis of {lit}`V`. -/
theorem exercise_2B_9 {m : ℕ} (v : Fin m → V) :
    IsBasis F v ↔
      IsBasis F (fun k : Fin m => ∑ i : Fin (k + 1), v ⟨i, by omega⟩) := by
  sorry

/-- 2B.10 Suppose {lit}`U` and {lit}`W` are subspaces of {lit}`V` such that
{lit}`V = U ⊕ W`. Suppose also that {lit}`u₁, …, uₘ` is a basis of {lit}`U`
and {lit}`w₁, …, wₙ` is a basis of {lit}`W`. Prove that the concatenation
{lit}`u₁, …, uₘ, w₁, …, wₙ` is a basis of {lit}`V`. -/
theorem exercise_2B_10 (U W : Submodule F V) (hUW : IsCompl U W)
    {m n : ℕ} (u : Fin m → U) (w : Fin n → W)
    (hu : IsBasis F u) (hw : IsBasis F w) :
    IsBasis F (Fin.append (fun i => (u i : V)) (fun i => (w i : V))) := by
  sorry

/-! 2B.11 Suppose {lit}`V` is a real vector space. If {lit}`v₁, …, vₙ` is a
basis of {lit}`V` (as a real vector space), prove that the same list is a
basis of the complexification {lit}`V_ℂ` (as a complex vector space).
(See Exercise 8 of Section 1B for the definition of complexification.)

Stated but not encoded here: the complexification has not been formalised in
this companion. -/

end LADR.Section_2B
