import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Recall
import Mathlib.Tactic.Ring
import LinearAlgebraDoneRightLean.Section_1C
import LinearAlgebraDoneRightLean.Section_2A
import LinearAlgebraDoneRightLean.Section_2B
import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 2C: Dimension
-/

namespace LADR.Section_2C

open LADR.Section_2A (Spans)
open LADR.Section_2B (IsBasis)
open LADR.Section_1C (IsDirectSum)

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]

/-! 2.34 Basis length does not depend on basis

Any two bases of a finite-dimensional vector space have the same length.
The proof is a direct application of 2.22 in both directions: the lin-indep
basis is shorter than the spanning basis, and vice versa. -/

theorem basis_card_eq {m n : ℕ} (v : Fin m → V) (w : Fin n → V)
    (hv : IsBasis F v) (hw : IsBasis F w) : m = n := by
  obtain ⟨hv_li, hv_span⟩ := hv
  obtain ⟨hw_li, hw_span⟩ := hw
  have h1 : m ≤ n :=
    LADR.Section_2A.linearIndependent_le_spanning v w hv_li hw_span
  have h2 : n ≤ m :=
    LADR.Section_2A.linearIndependent_le_spanning w v hw_li hv_span
  omega

/-! 2.35 Definition: dimension, dim V

The *dimension* of a finite-dimensional vector space is the length of any
basis. mathlib's {name}`Module.finrank` is defined to be exactly this (via
the rank of the dual or, equivalently for fin-dim, the cardinality of a
basis), so we use it directly. -/

noncomputable def dim (F : Type*) (V : Type*) [Field F] [AddCommGroup V]
    [Module F V] : ℕ := Module.finrank F V

/-! Bridging: the length of any basis equals {lit}`dim F V`. -/

theorem isBasis_card_eq_dim [Module.Finite F V] {m : ℕ} (v : Fin m → V)
    (hv : IsBasis F v) : m = dim F V := by
  obtain ⟨hv_li, hv_span⟩ := hv
  rw [Spans] at hv_span
  -- Build a {name}`Module.Basis` from the hypotheses, then read off the
  -- dimension from its index cardinality.
  let b : Module.Basis (Fin m) F V :=
    Module.Basis.mk hv_li (by rw [hv_span])
  simp [dim, Module.finrank_eq_card_basis b]

/-! 2.36 Example: dimensions -/

example (n : ℕ) : dim F (Fin n → F) = n := by
  simp [dim]

example (m : ℕ) : dim F (Polynomial.degreeLT F (m + 1)) = m + 1 := by
  simp only [dim, (Polynomial.degreeLTEquiv F (m + 1)).finrank_eq,
    Module.finrank_pi, Fintype.card_fin]

/-! {lit}`dim {(x, x, y) ∈ F³} = 2`. -/
example : dim F (LADR.Section_2B.U_27e F) = 2 := by sorry

/-! {lit}`dim {(x, y, z) ∈ F³ : x + y + z = 0} = 2`. -/
example : dim F (LADR.Section_2B.U_27f F) = 2 := by sorry

/-! 2.37 Dimension of a subspace

If {lit}`V` is finite-dimensional and {lit}`U` is a subspace, then
{lit}`dim U ≤ dim V`. (Think of a basis of {lit}`U` as linearly independent
in {lit}`V`, and a basis of {lit}`V` as spanning, then apply 2.22.) -/

theorem dim_submodule_le [Module.Finite F V] (U : Submodule F V) :
    dim F U ≤ dim F V :=
  Submodule.finrank_le U

/-! 2.38 Linearly independent list of the right length is a basis

If {lit}`V` is finite-dimensional and {lit}`v₁, …, vₙ` is linearly independent
of length {lit}`dim V`, then {lit}`v` is a basis. (Extend {lit}`v` to a basis
by 2.32; the extension has length {lit}`dim V = n`, so it adjoins nothing.) -/

theorem isBasis_of_linearIndependent_of_card_eq [Module.Finite F V] {m : ℕ}
    (v : Fin m → V) (hv : LinearIndependent F v) (hm : m = dim F V) :
    IsBasis F v := by
  refine ⟨hv, ?_⟩
  rw [Spans]
  haveI : FiniteDimensional F V := inferInstance
  exact hv.span_eq_top_of_card_eq_finrank'
    (by simp [dim] at hm; simpa using hm)

/-! 2.39 Subspace of full dimension equals the whole space

If {lit}`V` is finite-dimensional and {lit}`U` is a subspace with
{lit}`dim U = dim V`, then {lit}`U = V`. -/

theorem subspace_eq_top_of_dim_eq [Module.Finite F V] (U : Submodule F V)
    (h : dim F U = dim F V) : U = ⊤ := by
  haveI : FiniteDimensional F V := inferInstance
  exact Submodule.eq_top_of_finrank_eq h

/-! 2.40 Example: a basis of {lit}`F²`

The list {lit}`(5, 7), (4, 3)` is a basis of {lit}`F²`: it is linearly
independent (neither is a scalar multiple of the other) and has length
{lit}`2 = dim F²`, so 2.38 makes it a basis without checking spanning. -/

example : IsBasis F (![![5, 7], ![4, 3]] : Fin 2 → Fin 2 → F) := by sorry

/-! 2.41 Example: a basis of a subspace of {lit}`P₃(ℝ)`

{lit}`U = {p ∈ P₃(ℝ) : p'(5) = 0}`. Since {lit}`1, (x-5)², (x-5)³ ∈ U` and are
linearly independent, {lit}`dim U ≥ 3`. Also {lit}`dim U ≤ dim P₃(ℝ) = 4` and
{lit}`U ≠ P₃(ℝ)` (the polynomial {lit}`x` is not in {lit}`U`), so by 2.39
{lit}`dim U ≠ 4` and hence {lit}`dim U = 3`. The list of length 3 is then a
basis by 2.38.

(Stated; not encoded here — requires {lit}`Polynomial.derivative` and a
specific Polynomial subspace definition.) -/

/-! 2.42 Spanning list of the right length is a basis

If {lit}`V` is finite-dimensional and {lit}`v₁, …, vₙ` spans of length
{lit}`dim V`, then {lit}`v` is a basis. (Reduce to a basis by 2.30; the
reduction has length {lit}`dim V = n`, so deletes nothing.) -/

theorem isBasis_of_spans_of_card_eq [Module.Finite F V] {m : ℕ}
    (v : Fin m → V) (hv : Spans F v) (hm : m = dim F V) : IsBasis F v := by
  refine ⟨?_, hv⟩
  apply linearIndependent_of_top_le_span_of_card_eq_finrank
  · rw [Spans] at hv; rw [hv]
  · simp [dim] at hm; simpa using hm

/-! 2.43 Dimension of a sum

If {lit}`V₁` and {lit}`V₂` are subspaces of a finite-dimensional vector space,
then {lit}`dim(V₁ + V₂) = dim V₁ + dim V₂ - dim(V₁ ∩ V₂)`. We state this in
the additive form to avoid {lit}`ℕ` truncated subtraction. -/

theorem dim_sup_add_dim_inf_eq [Module.Finite F V] (V₁ V₂ : Submodule F V) :
    dim F ↥(V₁ ⊔ V₂) + dim F ↥(V₁ ⊓ V₂) = dim F V₁ + dim F V₂ :=
  Submodule.finrank_sup_add_finrank_inf_eq V₁ V₂

/-! # Exercises -/

/-- 2C.1 The subspaces of {lit}`ℝ²` are precisely {lit}`{0}`, the lines
through the origin, and {lit}`ℝ²`. -/
theorem exercise_2C_1 (U : Submodule ℝ (Fin 2 → ℝ)) :
    U = ⊥ ∨ dim ℝ U = 1 ∨ U = ⊤ := by
  sorry

/-- 2C.2 The subspaces of {lit}`ℝ³` are precisely {lit}`{0}`, the lines
through the origin, the planes through the origin, and {lit}`ℝ³`. -/
theorem exercise_2C_2 (U : Submodule ℝ (Fin 3 → ℝ)) :
    U = ⊥ ∨ dim ℝ U = 1 ∨ dim ℝ U = 2 ∨ U = ⊤ := by
  sorry

/-! 2C.3 Let {lit}`U = {p ∈ P₄(F) : p(6) = 0}`. (a) Find a basis of {lit}`U`.
(b) Extend to a basis of {lit}`P₄(F)`. (c) Find {lit}`W` with
{lit}`P₄(F) = U ⊕ W`. (Stated; explicit subspace not encoded here — would
need a polynomial-evaluation linear map and its kernel.) -/

/-! 2C.4 Let {lit}`U = {p ∈ P₄(ℝ) : p''(6) = 0}`. (Stated; not encoded —
requires {lit}`Polynomial.derivative`.) -/

/-! 2C.5 Let {lit}`U = {p ∈ P₄(F) : p(2) = p(5)}`. (Stated; explicit subspace
not encoded here.) -/

/-! 2C.6 Let {lit}`U = {p ∈ P₄(F) : p(2) = p(5) = p(6)}`. (Stated; explicit
subspace not encoded here.) -/

/-! 2C.7 Let {lit}`U = {p ∈ P₄(ℝ) : ∫₋₁¹ p = 0}`. (Stated; not encoded —
requires interval integration.) -/

/-- 2C.8 Suppose {lit}`v₁, …, vₘ` is linearly independent in {lit}`V` and
{lit}`w ∈ V`. Prove {lit}`dim span(v₁ + w, …, vₘ + w) ≥ m - 1`. -/
theorem exercise_2C_8 {m : ℕ} (v : Fin m → V) (hv : LinearIndependent F v)
    (w : V) :
    m - 1 ≤ Module.finrank F
      ↥(Submodule.span F (Set.range (fun i : Fin m => v i + w))) := by
  sorry

/-- 2C.9 Suppose {lit}`m ≥ 1` and {lit}`p₀, p₁, …, pₘ ∈ P(F)` are such that
each {lit}`pₖ` has degree {lit}`k`. Prove that {lit}`p₀, p₁, …, pₘ` is a
basis of {lit}`Pₘ(F)`. -/
theorem exercise_2C_9 [Infinite F] (m : ℕ) (hm : 1 ≤ m)
    (p : Fin (m + 1) → Polynomial.degreeLT F (m + 1))
    (hp : ∀ k : Fin (m + 1), (p k : Polynomial F).degree = (k : ℕ)) :
    IsBasis F p := by
  sorry

/-- 2C.10 Let {lit}`m ≥ 1` and {lit}`pₖ(x) = xᵏ (1 - x)ᵐ⁻ᵏ` for
{lit}`0 ≤ k ≤ m`. Show that {lit}`p₀, …, pₘ` is a basis of {lit}`Pₘ(F)`. -/
theorem exercise_2C_10 [Infinite F] (m : ℕ) (hm : 1 ≤ m) :
    IsBasis F (fun k : Fin (m + 1) =>
      (⟨Polynomial.X ^ (k : ℕ) * (1 - Polynomial.X) ^ (m - (k : ℕ)), by
        sorry⟩ : Polynomial.degreeLT F (m + 1))) := by
  sorry

/-- 2C.11 If {lit}`U, W` are 4-dimensional subspaces of {lit}`ℂ⁶`, prove
that there exist two vectors in {lit}`U ∩ W` such that neither is a scalar
multiple of the other. -/
theorem exercise_2C_11 (U W : Submodule ℂ (Fin 6 → ℂ))
    (hU : dim ℂ U = 4) (hW : dim ℂ W = 4) :
    ∃ x y : (U ⊓ W : Submodule ℂ (Fin 6 → ℂ)),
      (∀ a : ℂ, x ≠ a • y) ∧ (∀ b : ℂ, y ≠ b • x) := by
  sorry

/-- 2C.12 Suppose {lit}`U, W ≤ ℝ⁸` with {lit}`dim U = 3, dim W = 5,
U + W = ℝ⁸`. Prove {lit}`ℝ⁸ = U ⊕ W`. -/
theorem exercise_2C_12 (U W : Submodule ℝ (Fin 8 → ℝ))
    (hU : dim ℝ U = 3) (hW : dim ℝ W = 5) (hUW : U ⊔ W = ⊤) :
    IsCompl U W := by
  sorry

/-- 2C.13 If {lit}`U, W` are 5-dimensional subspaces of {lit}`ℝ⁹`, prove
{lit}`U ∩ W ≠ {0}`. -/
theorem exercise_2C_13 (U W : Submodule ℝ (Fin 9 → ℝ))
    (hU : dim ℝ U = 5) (hW : dim ℝ W = 5) :
    U ⊓ W ≠ ⊥ := by
  sorry

/-- 2C.14 If {lit}`V` is 10-dim and {lit}`V₁, V₂, V₃` are subspaces of {lit}`V`
with {lit}`dim V₁ = dim V₂ = dim V₃ = 7`, prove {lit}`V₁ ∩ V₂ ∩ V₃ ≠ {0}`. -/
theorem exercise_2C_14 [Module.Finite F V] (hV : dim F V = 10)
    (V₁ V₂ V₃ : Submodule F V)
    (hV₁ : dim F V₁ = 7) (hV₂ : dim F V₂ = 7) (hV₃ : dim F V₃ = 7) :
    V₁ ⊓ V₂ ⊓ V₃ ≠ ⊥ := by
  sorry

/-- 2C.15 If {lit}`V` is finite-dimensional and {lit}`V₁, V₂, V₃` are
subspaces with {lit}`dim V₁ + dim V₂ + dim V₃ > 2 dim V`, prove
{lit}`V₁ ∩ V₂ ∩ V₃ ≠ {0}`. -/
theorem exercise_2C_15 [Module.Finite F V] (V₁ V₂ V₃ : Submodule F V)
    (hsum : dim F V₁ + dim F V₂ + dim F V₃ > 2 * dim F V) :
    V₁ ⊓ V₂ ⊓ V₃ ≠ ⊥ := by
  sorry

/-- 2C.16 If {lit}`V` is finite-dimensional and {lit}`U ≤ V` with
{lit}`U ≠ V`, let {lit}`n = dim V` and {lit}`m = dim U`. Prove that there
exist {lit}`n - m` subspaces of {lit}`V`, each of dimension {lit}`n - 1`,
whose intersection equals {lit}`U`. -/
theorem exercise_2C_16 [Module.Finite F V] (U : Submodule F V) (hU : U ≠ ⊤) :
    ∃ (W : Fin (dim F V - dim F U) → Submodule F V),
      (∀ i, dim F (W i) = dim F V - 1) ∧
      ⨅ i, W i = U := by
  sorry

/-- 2C.17 Suppose {lit}`V₁, …, Vₘ` are finite-dimensional subspaces of
{lit}`V`. Prove that {lit}`V₁ + ⋯ + Vₘ` is finite-dimensional and
{lit}`dim(V₁ + ⋯ + Vₘ) ≤ dim V₁ + ⋯ + dim Vₘ`. -/
theorem exercise_2C_17 {m : ℕ} (W : Fin m → Submodule F V)
    (hW : ∀ i, Module.Finite F (W i)) :
    Module.Finite F ↥(⨆ i, W i) ∧
      Module.finrank F ↥(⨆ i, W i) ≤ ∑ i, Module.finrank F (W i) := by
  sorry

/-- 2C.18 Suppose {lit}`V` is finite-dimensional with {lit}`dim V = n ≥ 1`.
Prove that there exist 1-dimensional subspaces {lit}`V₁, …, Vₙ` of {lit}`V`
such that {lit}`V = V₁ ⊕ ⋯ ⊕ Vₙ`. -/
theorem exercise_2C_18 [Module.Finite F V] (hV : 1 ≤ dim F V) :
    ∃ (W : Fin (dim F V) → Submodule F V),
      (∀ i, dim F (W i) = 1) ∧ IsDirectSum W ∧ ⨆ i, W i = ⊤ := by
  sorry

/-- 2C.19 Prove or counterexample: if {lit}`V₁, V₂, V₃ ≤ V` (fin-dim), then
{lit}`dim(V₁ + V₂ + V₃) = dim V₁ + dim V₂ + dim V₃ - dim(V₁ ∩ V₂) -
dim(V₁ ∩ V₃) - dim(V₂ ∩ V₃) + dim(V₁ ∩ V₂ ∩ V₃)`. -/
def exercise_2C_19 :
    Decidable (∀ (V₁ V₂ V₃ : Submodule F V) [Module.Finite F V],
      Module.finrank F ↥(V₁ ⊔ V₂ ⊔ V₃) + Module.finrank F ↥(V₁ ⊓ V₂) +
        Module.finrank F ↥(V₁ ⊓ V₃) + Module.finrank F ↥(V₂ ⊓ V₃) =
        Module.finrank F V₁ + Module.finrank F V₂ + Module.finrank F V₃ +
          Module.finrank F ↥(V₁ ⊓ V₂ ⊓ V₃)) := by
  -- first line should be `apply isTrue` or `apply isFalse`
  sorry

/-! 2C.20 The "strange formula" for {lit}`dim(V₁ + V₂ + V₃)`. (Stated;
formula encoding involves rational arithmetic.) -/

end LADR.Section_2C
