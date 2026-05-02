import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Module.Submodule.Pointwise
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Recall
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 1C: Subspaces
-/

namespace LADR.Section_1C

/-! Reminder: This is how we say V is a vector space over F in mathlib -/
variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]

/-! 1.33 Definition: subspace

A subset of {lit}`V` is called a *subspace* of {lit}`V` if it is itself a vector
space with the same additive identity, addition, and scalar multiplication.

In Lean/mathlib the bundled object {name}`Submodule` carries the carrier set
together with the three closure proofs at once. -/

/-! 1.34 Conditions for a subspace

A subset is a subspace iff it contains {lit}`0`, is closed under addition, and is
closed under scalar multiplication. These are exactly the three fields of
{name}`Submodule`. -/

recall Submodule.zero_mem {R : Type*} {M : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] (p : Submodule R M) : (0 : M) ∈ p
recall Submodule.add_mem {R : Type*} {M : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] (p : Submodule R M) {x y : M} (h₁ : x ∈ p) (h₂ : y ∈ p) : x + y ∈ p
recall Submodule.smul_mem {R : Type*} {M : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] (p : Submodule R M) {x : M} (r : R) (h : x ∈ p) : r • x ∈ p

/-! Conversely, Axler's 1.34 says these three conditions are *enough*: any
subset {lit}`S ⊆ V` containing {lit}`0` and closed under addition and scalar
multiplication is itself a vector space under the operations inherited from
{lit}`V`. We prove every vector-space axiom on the subtype {lit}`↥S` directly
from the three closure assumptions and the corresponding axiom in {lit}`V`. -/

/-! In what follows, {lit}`S : Set V` is an arbitrary subset and {lit}`h0`,
{lit}`hadd`, {lit}`hsmul` are the three closure assumptions of Axler 1.34. -/

/-! The inherited operations on the subtype {lit}`↥S`. Closure under {lit}`0`,
{lit}`+`, {lit}`•` is exactly what lets each operation land back inside
{lit}`S`. The additive inverse uses {lit}`-u = (-1) • u`, which is why we don't
need a fourth closure assumption. -/

def subZero (S : Set V) (h0 : (0 : V) ∈ S) : S := ⟨0, h0⟩

def subAdd (S : Set V) (hadd : ∀ (u w : V), u ∈ S → w ∈ S → u + w ∈ S)
    (u w : S) : S := ⟨u.1 + w.1, hadd u.1 w.1 u.2 w.2⟩

def subNeg (S : Set V) (hsmul : ∀ (a : F) (u : V), u ∈ S → a • u ∈ S) (u : S) :
    S := ⟨-u.1, by simpa using hsmul (-1) u.1 u.2⟩

def subSMul (S : Set V) (hsmul : ∀ (a : F) (u : V), u ∈ S → a • u ∈ S)
    (a : F) (u : S) : S := ⟨a • u.1, hsmul a u.1 u.2⟩

/-! Each vector-space axiom on {lit}`↥S` is now a one-line proof: unfold the
inherited operation with {name}`Subtype.ext`, then invoke the corresponding
axiom of {lit}`V`. -/

theorem sub_add_assoc (S : Set V)
    (hadd : ∀ (u w : V), u ∈ S → w ∈ S → u + w ∈ S) (u w x : S) :
    subAdd S hadd (subAdd S hadd u w) x = subAdd S hadd u (subAdd S hadd w x) :=
  Subtype.ext (add_assoc u.1 w.1 x.1)

theorem sub_add_comm (S : Set V)
    (hadd : ∀ (u w : V), u ∈ S → w ∈ S → u + w ∈ S) (u w : S) :
    subAdd S hadd u w = subAdd S hadd w u :=
  Subtype.ext (add_comm u.1 w.1)

theorem sub_zero_add (S : Set V) (h0 : (0 : V) ∈ S)
    (hadd : ∀ (u w : V), u ∈ S → w ∈ S → u + w ∈ S) (u : S) :
    subAdd S hadd (subZero S h0) u = u :=
  Subtype.ext (zero_add u.1)

theorem sub_add_zero (S : Set V) (h0 : (0 : V) ∈ S)
    (hadd : ∀ (u w : V), u ∈ S → w ∈ S → u + w ∈ S) (u : S) :
    subAdd S hadd u (subZero S h0) = u :=
  Subtype.ext (add_zero u.1)

theorem sub_neg_add_cancel (S : Set V) (h0 : (0 : V) ∈ S)
    (hadd : ∀ (u w : V), u ∈ S → w ∈ S → u + w ∈ S)
    (hsmul : ∀ (a : F) (u : V), u ∈ S → a • u ∈ S) (u : S) :
    subAdd S hadd (subNeg S hsmul u) u = subZero S h0 :=
  Subtype.ext (neg_add_cancel u.1)

theorem sub_one_smul (S : Set V)
    (hsmul : ∀ (a : F) (u : V), u ∈ S → a • u ∈ S) (u : S) :
    subSMul S hsmul 1 u = u :=
  Subtype.ext (one_smul F u.1)

theorem sub_mul_smul (S : Set V)
    (hsmul : ∀ (a : F) (u : V), u ∈ S → a • u ∈ S) (a b : F) (u : S) :
    subSMul S hsmul (a * b) u = subSMul S hsmul a (subSMul S hsmul b u) :=
  Subtype.ext (mul_smul a b u.1)

theorem sub_smul_add (S : Set V)
    (hadd : ∀ (u w : V), u ∈ S → w ∈ S → u + w ∈ S)
    (hsmul : ∀ (a : F) (u : V), u ∈ S → a • u ∈ S) (a : F) (u w : S) :
    subSMul S hsmul a (subAdd S hadd u w)
      = subAdd S hadd (subSMul S hsmul a u) (subSMul S hsmul a w) :=
  Subtype.ext (smul_add a u.1 w.1)

theorem sub_add_smul (S : Set V)
    (hadd : ∀ (u w : V), u ∈ S → w ∈ S → u + w ∈ S)
    (hsmul : ∀ (a : F) (u : V), u ∈ S → a • u ∈ S) (a b : F) (u : S) :
    subSMul S hsmul (a + b) u
      = subAdd S hadd (subSMul S hsmul a u) (subSMul S hsmul b u) :=
  Subtype.ext (add_smul a b u.1)

theorem sub_zero_smul (S : Set V) (h0 : (0 : V) ∈ S)
    (hsmul : ∀ (a : F) (u : V), u ∈ S → a • u ∈ S) (u : S) :
    subSMul S hsmul 0 u = subZero S h0 :=
  Subtype.ext (zero_smul F u.1)

theorem sub_smul_zero (S : Set V) (h0 : (0 : V) ∈ S)
    (hsmul : ∀ (a : F) (u : V), u ∈ S → a • u ∈ S) (a : F) :
    subSMul S hsmul a (subZero S h0) = subZero S h0 :=
  Subtype.ext (smul_zero a)

/-! In particular every subspace is closed under additive inverses, since
{lit}`-u = (-1) • u`. -/

example (U : Submodule F V) {u : V} (hu : u ∈ U) : -u ∈ U := U.neg_mem hu

/-! 1.35 Example: subspaces

(a) The set {lit}`{(x₁, x₂, x₃, x₄) ∈ F⁴ : x₃ = 5 x₄ + b}` is a subspace of
{lit}`F⁴` iff {lit}`b = 0` (the {lit}`b = 0` direction is shown here; both
directions are exercise 1C.1 below). -/

example : Submodule F (Fin 4 → F) where
  carrier := {v | v 2 = 5 * v 3}
  zero_mem' := by simp
  add_mem' := by
    intro u v hu hv
    simp only [Set.mem_setOf_eq, Pi.add_apply] at *
    rw [hu, hv]; ring
  smul_mem' := by
    intro a v hv
    simp only [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul] at *
    rw [hv]; ring

/-! 1.35(b) Continuous real-valued functions on {lit}`[0, 1]` form a subspace
of {lit}`ℝ^[0,1]`. (Axler uses {lit}`[0, 1]`; we work over all of {lit}`ℝ` —
the closure proofs are identical.) -/

example : Submodule ℝ (ℝ → ℝ) where
  carrier := {f | Continuous f}
  zero_mem' := continuous_const
  add_mem' hf hg := hf.add hg
  smul_mem' a _ hf := hf.const_smul a

/-! 1.35(c) Differentiable real-valued functions on {lit}`ℝ` form a subspace
of {lit}`ℝ^ℝ`. -/

example : Submodule ℝ (ℝ → ℝ) where
  carrier := {f | Differentiable ℝ f}
  zero_mem' := differentiable_const 0
  add_mem' hf hg := hf.add hg
  smul_mem' a _ hf := hf.const_smul a

/-! 1.35(d) Differentiable real-valued functions on {lit}`(0, 3)` such that
{lit}`f'(2) = 0` form a subspace. We work on all of {lit}`ℝ` and pin the
derivative at {lit}`2`; both addition and scalar multiplication preserve the
derivative being zero at a point. -/

example : Submodule ℝ (ℝ → ℝ) where
  carrier := {f | Differentiable ℝ f ∧ deriv f 2 = 0}
  zero_mem' := ⟨differentiable_const 0, by simp⟩
  add_mem' := by
    rintro f g ⟨hfd, hf⟩ ⟨hgd, hg⟩
    refine ⟨hfd.add hgd, ?_⟩
    rw [deriv_add (hfd 2) (hgd 2), hf, hg, add_zero]
  smul_mem' := by
    rintro a f ⟨hfd, hf⟩
    refine ⟨hfd.const_smul a, ?_⟩
    rw [deriv_const_smul _ (hfd 2), hf, smul_zero]

/-! 1.35(e) Sequences of complex numbers with limit {lit}`0` form a subspace
of {lit}`ℂ^∞`. In Lean, "sequence" is {lit}`ℕ → ℂ` and "has limit {lit}`0`" is
{lit}`Filter.Tendsto f Filter.atTop (𝓝 0)`. -/

example : Submodule ℂ (ℕ → ℂ) where
  carrier := {f | Filter.Tendsto f Filter.atTop (nhds 0)}
  zero_mem' := tendsto_const_nhds
  add_mem' := by
    intro f g hf hg
    simpa using hf.add hg
  smul_mem' := by
    intro a f hf
    simpa using hf.const_smul a

/-! Two distinguished subspaces every space has: the trivial subspace {lit}`{0}`
({name}`Bot.bot`) and the whole space {name}`Top.top`. -/

example : Submodule F V := ⊥
example : Submodule F V := ⊤
example (v : V) : v ∈ (⊤ : Submodule F V) := Submodule.mem_top
example (v : V) : v ∈ (⊥ : Submodule F V) ↔ v = 0 := Submodule.mem_bot F

/-! 1.36 Definition: sum of subspaces

For subspaces {lit}`V₁, …, Vₘ` of {lit}`V`, the sum
{lit}`V₁ + ⋯ + Vₘ = {v₁ + ⋯ + vₘ : vₖ ∈ Vₖ}` is the set of all such sums.

For two subspaces, mathlib's lattice supremum {lit}`U ⊔ W` is exactly the sum,
and {lit}`U + W` resolves to the same thing via {name}`Submodule.add_eq_sup`. -/

example (U W : Submodule F V) : Submodule F V := U ⊔ W
example (U W : Submodule F V) : U + W = U ⊔ W := Submodule.add_eq_sup U W

/-! Membership in {lit}`U ⊔ W` is exactly the textbook formula. -/

example (U W : Submodule F V) (x : V) :
    x ∈ U ⊔ W ↔ ∃ y ∈ U, ∃ z ∈ W, y + z = x := Submodule.mem_sup

/-! Axler defines {lit}`V₁ + ⋯ + Vₘ` as a single n-ary operation. To make
sense of an iterated binary {lit}`⊔` we need the binary sum to be associative
and commutative — both inherit from {lit}`Submodule F V` being a lattice.
(These are also exercises 1C.16 and 1C.17 below.) -/

example (U W : Submodule F V) : U ⊔ W = W ⊔ U := sup_comm U W
example (V₁ V₂ V₃ : Submodule F V) : (V₁ ⊔ V₂) ⊔ V₃ = V₁ ⊔ (V₂ ⊔ V₃) :=
  sup_assoc V₁ V₂ V₃

/-! So {lit}`V₁ + V₂ + V₃` is unambiguous: the textbook formula
{lit}`{v₁ + v₂ + v₃ : vₖ ∈ Vₖ}` matches either bracketing. -/

example (V₁ V₂ V₃ : Submodule F V) (x : V) :
    x ∈ V₁ ⊔ V₂ ⊔ V₃ ↔ ∃ v₁ ∈ V₁, ∃ v₂ ∈ V₂, ∃ v₃ ∈ V₃, v₁ + v₂ + v₃ = x := by
  rw [Submodule.mem_sup]
  refine ⟨?_, ?_⟩
  · rintro ⟨y, hy, v₃, hv₃, rfl⟩
    obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := Submodule.mem_sup.mp hy
    exact ⟨v₁, hv₁, v₂, hv₂, v₃, hv₃, rfl⟩
  · rintro ⟨v₁, hv₁, v₂, hv₂, v₃, hv₃, rfl⟩
    exact ⟨v₁ + v₂, Submodule.mem_sup.mpr ⟨v₁, hv₁, v₂, hv₂, rfl⟩, v₃, hv₃, rfl⟩

/-! For arbitrary {lit}`m`, mathlib's indexed supremum {lit}`⨆ i, W i` plays
the role of Axler's {lit}`V₁ + ⋯ + Vₘ`. Membership recovers the textbook
formula {lit}`{v₁ + ⋯ + vₘ : vₖ ∈ Vₖ}`. -/

example (m : ℕ) (W : Fin m → Submodule F V) (x : V) :
    x ∈ ⨆ i, W i ↔ ∃ v : (i : Fin m) → W i, ∑ i, ((v i : V)) = x := by
  rw [show (⨆ i, W i) = ⨆ i ∈ (Finset.univ : Finset (Fin m)), W i by simp]
  rw [Submodule.mem_iSup_finset_iff_exists_sum]

/-! 1.37 Example: a sum of subspaces of {lit}`F³`

With {lit}`U = {(x, 0, 0) : x ∈ F}` and {lit}`W = {(0, y, 0) : y ∈ F}`,
{lit}`U + W = {(x, y, 0) : x, y ∈ F}`, i.e. the vectors whose third coordinate
is zero. -/

namespace Example_1_37

def U : Submodule F (Fin 3 → F) where
  carrier := {v | v 1 = 0 ∧ v 2 = 0}
  zero_mem' := ⟨rfl, rfl⟩
  add_mem' := by
    rintro u v ⟨h1, h2⟩ ⟨h3, h4⟩
    exact ⟨by simp [Pi.add_apply, h1, h3], by simp [Pi.add_apply, h2, h4]⟩
  smul_mem' := by
    rintro a v ⟨h1, h2⟩
    exact ⟨by simp [Pi.smul_apply, h1], by simp [Pi.smul_apply, h2]⟩

def W : Submodule F (Fin 3 → F) where
  carrier := {v | v 0 = 0 ∧ v 2 = 0}
  zero_mem' := ⟨rfl, rfl⟩
  add_mem' := by
    rintro u v ⟨h1, h2⟩ ⟨h3, h4⟩
    exact ⟨by simp [Pi.add_apply, h1, h3], by simp [Pi.add_apply, h2, h4]⟩
  smul_mem' := by
    rintro a v ⟨h1, h2⟩
    exact ⟨by simp [Pi.smul_apply, h1], by simp [Pi.smul_apply, h2]⟩

example : (U ⊔ W : Submodule F (Fin 3 → F)) =
    { carrier := {v | v 2 = 0}
      zero_mem' := rfl
      add_mem' := by
        intro u v hu hv
        show u 2 + v 2 = 0
        rw [show u 2 = 0 from hu, show v 2 = 0 from hv, add_zero]
      smul_mem' := by
        intro a v hv
        show a • v 2 = 0
        rw [show v 2 = 0 from hv, smul_zero] } := by
  ext v
  rw [Submodule.mem_sup]
  refine ⟨?_, ?_⟩
  · rintro ⟨y, ⟨_, hy2⟩, z, ⟨_, hz2⟩, rfl⟩
    show y 2 + z 2 = 0
    rw [hy2, hz2, add_zero]
  · intro (hv : v 2 = 0)
    refine ⟨![v 0, 0, 0], ⟨rfl, rfl⟩, ![0, v 1, 0], ⟨rfl, rfl⟩, ?_⟩
    funext i
    fin_cases i <;> simp [hv]

end Example_1_37

/-! 1.38/1.39 Example: a sum of subspaces of {lit}`F⁴`

With {lit}`U = {(x, x, y, y) : x, y ∈ F}` and {lit}`W = {(x, x, x, y) : x, y ∈ F}`
we have {lit}`U + W = {(x, x, y, z) : x, y, z ∈ F}` — exactly the vectors whose
first two coordinates are equal. -/

namespace Example_1_38

def U : Submodule F (Fin 4 → F) where
  carrier := {v | v 0 = v 1 ∧ v 2 = v 3}
  zero_mem' := ⟨rfl, rfl⟩
  add_mem' := by
    rintro u v ⟨h1, h2⟩ ⟨h3, h4⟩
    exact ⟨by simp [Pi.add_apply, h1, h3], by simp [Pi.add_apply, h2, h4]⟩
  smul_mem' := by
    rintro a v ⟨h1, h2⟩
    exact ⟨by simp [Pi.smul_apply, h1], by simp [Pi.smul_apply, h2]⟩

def W : Submodule F (Fin 4 → F) where
  carrier := {v | v 0 = v 1 ∧ v 1 = v 2}
  zero_mem' := ⟨rfl, rfl⟩
  add_mem' := by
    rintro u v ⟨h1, h2⟩ ⟨h3, h4⟩
    exact ⟨by simp [Pi.add_apply, h1, h3], by simp [Pi.add_apply, h2, h4]⟩
  smul_mem' := by
    rintro a v ⟨h1, h2⟩
    exact ⟨by simp [Pi.smul_apply, h1], by simp [Pi.smul_apply, h2]⟩

example : (U ⊔ W : Submodule F (Fin 4 → F)) =
    { carrier := {v | v 0 = v 1}
      zero_mem' := rfl
      add_mem' := by
        intro u v hu hv
        show u 0 + v 0 = u 1 + v 1
        rw [show u 0 = u 1 from hu, show v 0 = v 1 from hv]
      smul_mem' := by
        intro a v hv
        show a • v 0 = a • v 1
        rw [show v 0 = v 1 from hv] } := by
  ext v
  rw [Submodule.mem_sup]
  refine ⟨?_, ?_⟩
  · rintro ⟨y, ⟨hy01, _⟩, z, ⟨hz01, _⟩, rfl⟩
    show y 0 + z 0 = y 1 + z 1
    rw [hy01, hz01]
  · intro (hv : v 0 = v 1)
    refine ⟨![0, 0, v 2 - v 0, v 2 - v 0], ⟨rfl, rfl⟩,
            ![v 0, v 0, v 0, v 3 - v 2 + v 0], ⟨rfl, rfl⟩, ?_⟩
    funext i
    fin_cases i <;> simp [hv]

end Example_1_38

/-! 1.40 Sum is the smallest containing subspace.

Axler's argument has three steps:
(i) The sum is itself a subspace — built into the type {lit}`U ⊔ W : Submodule F V`,
    which 1.34 (the {name}`Submodule` constructor) already supplied.
(ii) Each summand is contained in the sum: take {lit}`u = u + 0` and
    {lit}`w = 0 + w` (Axler's "consider sums where all except one are 0").
 -/
example (U W : Submodule F V) : U ≤ U ⊔ W :=
  fun u hu => Submodule.mem_sup.mpr ⟨u, hu, 0, W.zero_mem, add_zero u⟩
example (U W : Submodule F V) : W ≤ U ⊔ W :=
  fun w hw => Submodule.mem_sup.mpr ⟨0, U.zero_mem, w, hw, zero_add w⟩

/-! (iii) Any subspace containing both summands contains the sum, because subspaces
    are closed under addition. -/
example (U W X : Submodule F V) (h₁ : U ≤ X) (h₂ : W ≤ X) : U ⊔ W ≤ X := by
  intro x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  exact X.add_mem (h₁ hy) (h₂ hz)

/-! 1.41 Definition: direct sum, ⊕

The sum {lit}`V₁ + ⋯ + Vₘ` is a *direct sum* if each element has only one
representation as {lit}`v₁ + ⋯ + vₘ` with each {lit}`vₖ ∈ Vₖ`.

In mathlib, two submodules form a direct sum exactly when {name}`Disjoint`
holds. By {name}`Submodule.disjoint_def`,
{lit}`Disjoint U W ↔ ∀ x ∈ U, x ∈ W → x = 0`. -/

recall Submodule.disjoint_def {R : Type*} {M : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] {p p' : Submodule R M} :
    Disjoint p p' ↔ ∀ x ∈ p, x ∈ p' → x = 0

/-! Equivalent in any lattice with a bottom element: -/

example (U W : Submodule F V) : Disjoint U W ↔ U ⊓ W = ⊥ := disjoint_iff

/-! 1.42 Example: a direct sum of two subspaces

With {lit}`U = {(x, y, 0)}` and {lit}`W = {(0, 0, z)}` in {lit}`F³`, we have
{lit}`F³ = U ⊕ W`. The direct-sum statement is
{lit}`Disjoint U W ∧ U ⊔ W = ⊤`, i.e. {name}`IsCompl`. -/

/-! 1.43 Example: a direct sum of multiple subspaces

For {lit}`Vₖ = {v ∈ Fⁿ : vᵢ = 0 for i ≠ k}` (the {lit}`k`-th coordinate axis),
{lit}`Fⁿ = V₁ ⊕ ⋯ ⊕ Vₙ`. -/

/-! 1.44 Example: a sum that is *not* a direct sum

In {lit}`F³`, take
{lit}`V₁ = {(x, y, 0)}`, {lit}`V₂ = {(0, 0, z)}`, {lit}`V₃ = {(0, y, y)}`.
Then {lit}`F³ = V₁ + V₂ + V₃` but {lit}`0` has more than one representation, so
the sum is *not* direct. Pairwise intersections are all {lit}`{0}`, which is
why 1.46 below characterizes direct sums only of *two* subspaces. -/

/-! 1.45 Condition for a direct sum

The sum is direct iff the only way to write {lit}`0` as {lit}`v₁ + ⋯ + vₘ` with
{lit}`vₖ ∈ Vₖ` is to take each {lit}`vₖ = 0`. For two subspaces, this is
{name}`Submodule.disjoint_iff_add_eq_zero`. -/

example {U W : Submodule F V} :
    Disjoint U W ↔ ∀ {x y : V}, x ∈ U → y ∈ W → x + y = 0 → x = 0 ∧ y = 0 :=
  Submodule.disjoint_iff_add_eq_zero

/-! 1.46 Direct sum of two subspaces

{lit}`U + W` is a direct sum {lit}`⟺ U ∩ W = {0}`. -/

theorem disjoint_iff_inter_trivial (U W : Submodule F V) :
    U ⊓ W = ⊥ ↔ ∀ v, v ∈ U → v ∈ W → v = 0 := by
  rw [Submodule.eq_bot_iff]
  exact ⟨fun h v hu hw => h v ⟨hu, hw⟩, fun h v ⟨hu, hw⟩ => h v hu hw⟩

/-! # Exercises -/

/-- 1C.1(a) The set {lit}`{v ∈ F³ : v 0 + 2 v 1 + 3 v 2 = 0}` is a subspace
of {lit}`F³`. -/
def exercise_1C_1a : Submodule ℝ (Fin 3 → ℝ) where
  carrier := {v | v 0 + 2 * v 1 + 3 * v 2 = 0}
  zero_mem' := by simp
  add_mem' := by
    intro u v hu hv
    simp only [Set.mem_setOf_eq, Pi.add_apply] at *
    linarith
  smul_mem' := by
    intro a v hv
    simp only [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul] at *
    have : a * v 0 + 2 * (a * v 1) + 3 * (a * v 2) = a * (v 0 + 2 * v 1 + 3 * v 2) := by ring
    rw [this, hv, mul_zero]

/-! 1C.1(b) The set {lit}`{v ∈ F³ : v 0 + 2 v 1 + 3 v 2 = 4}` is **not** a
subspace (this is exercise 1C.3 below). -/

/-- 1C.1(c) The set {lit}`{v ∈ F³ : v 0 * v 1 * v 2 = 0}` is **not** a
subspace. -/
theorem exercise_1C_1c :
    ¬ ∃ U : Submodule ℝ (Fin 3 → ℝ),
      (U : Set (Fin 3 → ℝ)) = {v | v 0 * v 1 * v 2 = 0} := by
  sorry

/-- 1C.1(d) The set {lit}`{v ∈ F³ : v 0 = 5 v 2}` is a subspace. -/
def exercise_1C_1d : Submodule ℝ (Fin 3 → ℝ) where
  carrier := {v | v 0 = 5 * v 2}
  zero_mem' := by simp
  add_mem' := by
    intro u v hu hv
    simp only [Set.mem_setOf_eq, Pi.add_apply] at *
    rw [hu, hv]; ring
  smul_mem' := by
    intro a v hv
    simp only [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul] at *
    rw [hv]; ring

/-! 1C.2 ("verify all assertions about subspaces in 1.35"), and 1C.3, 1C.4
(calculus statements about differentiable / continuous / integrable functions)
are omitted here. -/

/-- 1C.3 The set {lit}`{v ∈ ℝ³ : v 0 + 2 v 1 + 3 v 2 = 4}` is **not** a
subspace of {lit}`ℝ³`. -/
theorem exercise_1C_3 :
    ¬ ∃ U : Submodule ℝ (Fin 3 → ℝ),
      (U : Set (Fin 3 → ℝ)) = {v | v 0 + 2 * v 1 + 3 * v 2 = 4} := by
  sorry

/-- 1C.5 {lit}`ℝ²` is *not* a subspace of the complex vector space {lit}`ℂ²`:
the underlying field is wrong, since {lit}`ℝ²` is closed under real scalars,
not complex ones. -/
theorem exercise_1C_5 :
    ¬ ∃ U : Submodule ℂ (Fin 2 → ℂ),
      (U : Set (Fin 2 → ℂ)) = {v | ∀ i, (v i).im = 0} := by
  sorry

/-- 1C.6(a) The set {lit}`{(a, b, c) ∈ ℝ³ : a³ = b³}` is a subspace of
{lit}`ℝ³`. -/
theorem exercise_1C_6a :
    ∃ U : Submodule ℝ (Fin 3 → ℝ),
      (U : Set (Fin 3 → ℝ)) = {v | v 0 ^ 3 = v 1 ^ 3} := by
  sorry

/-- 1C.6(b) The set {lit}`{(a, b, c) ∈ ℂ³ : a³ = b³}` is **not** a subspace
of {lit}`ℂ³`. -/
theorem exercise_1C_6b :
    ¬ ∃ U : Submodule ℂ (Fin 3 → ℂ),
      (U : Set (Fin 3 → ℂ)) = {v | v 0 ^ 3 = v 1 ^ 3} := by
  sorry

/-- 1C.7 *Counterexample.* There is a nonempty subset of {lit}`ℝ²` closed under
addition and additive inverses but **not** a subspace. (Hint: {lit}`ℤ²`.) -/
theorem exercise_1C_7 :
    ∃ U : Set (Fin 2 → ℝ),
      U.Nonempty ∧
      (∀ u ∈ U, ∀ v ∈ U, u + v ∈ U) ∧
      (∀ u ∈ U, -u ∈ U) ∧
      ¬ ∃ S : Submodule ℝ (Fin 2 → ℝ), (S : Set (Fin 2 → ℝ)) = U := by
  sorry

/-- 1C.8 *Counterexample.* There is a nonempty subset of {lit}`ℝ²` closed
under scalar multiplication but **not** a subspace. (Hint: the union of the
two coordinate axes.) -/
theorem exercise_1C_8 :
    ∃ U : Set (Fin 2 → ℝ),
      U.Nonempty ∧
      (∀ (a : ℝ) (u), u ∈ U → a • u ∈ U) ∧
      ¬ ∃ S : Submodule ℝ (Fin 2 → ℝ), (S : Set (Fin 2 → ℝ)) = U := by
  sorry

/-- 1C.9 The set of periodic functions {lit}`ℝ → ℝ` is *not* a subspace of
{lit}`ℝ → ℝ` (the sum of two periodic functions need not be periodic). -/
def Periodic (f : ℝ → ℝ) : Prop := ∃ p > 0, ∀ x, f x = f (x + p)

theorem exercise_1C_9 :
    ¬ ∃ U : Submodule ℝ (ℝ → ℝ), (U : Set (ℝ → ℝ)) = {f | Periodic f} := by
  sorry

/-- 1C.10 The intersection of two subspaces is a subspace. In mathlib this is
the lattice infimum {lit}`U ⊓ W`. -/
example (U W : Submodule F V) : Submodule F V := U ⊓ W

/-- 1C.11 The intersection of *any* collection of subspaces of {lit}`V` is a
subspace. In mathlib this is the lattice infimum {lit}`sInf` / {lit}`iInf`. -/
example (𝒞 : Set (Submodule F V)) : Submodule F V := sInf 𝒞
example {ι : Type*} (𝒞 : ι → Submodule F V) : Submodule F V := iInf 𝒞

/-- 1C.12 The union of two subspaces of {lit}`V` is a subspace iff one of the
subspaces is contained in the other. -/
@[avoiding Submodule.union_eq_iff_le_or_le]
theorem exercise_1C_12 (U W : Submodule F V) :
    (∃ S : Submodule F V, (S : Set V) = (U : Set V) ∪ (W : Set V)) ↔
      U ≤ W ∨ W ≤ U := by
  sorry

/-- 1C.13 The union of three subspaces of {lit}`V` is a subspace iff one
contains the other two. (This requires {lit}`F` to have more than two
elements.) -/
theorem exercise_1C_13 (U W X : Submodule F V) (_hF : ∃ a : F, a ≠ 0 ∧ a ≠ 1) :
    (∃ S : Submodule F V, (S : Set V) = (U : Set V) ∪ W ∪ X) ↔
      (W ≤ U ∧ X ≤ U) ∨ (U ≤ W ∧ X ≤ W) ∨ (U ≤ X ∧ W ≤ X) := by
  sorry

/-- 1C.14 With {lit}`U = {(x, -x, 2x) : x ∈ F}` and
{lit}`W = {(x, x, 2x) : x ∈ F}` in {lit}`F³`,
{lit}`U + W = {v ∈ F³ : v 2 = 2 v 0}` — the vectors whose third coordinate is
twice the first. -/
theorem exercise_1C_14 :
    ∃ S : Submodule F (Fin 3 → F),
      (S : Set (Fin 3 → F)) = {v | v 2 = 2 * v 0} := by
  sorry

/-- 1C.15 If {lit}`U` is a subspace of {lit}`V`, then {lit}`U + U = U`. -/
@[avoiding sup_idem, sup_self]
theorem exercise_1C_15 (U : Submodule F V) : U ⊔ U = U := by
  sorry

/-- 1C.16 Addition on subspaces of {lit}`V` is commutative:
{lit}`U + W = W + U`. -/
@[avoiding sup_comm]
theorem exercise_1C_16 (U W : Submodule F V) : U ⊔ W = W ⊔ U := by
  sorry

/-- 1C.17 Addition on subspaces of {lit}`V` is associative:
{lit}`(V₁ + V₂) + V₃ = V₁ + (V₂ + V₃)`. -/
@[avoiding sup_assoc]
theorem exercise_1C_17 (V₁ V₂ V₃ : Submodule F V) :
    (V₁ ⊔ V₂) ⊔ V₃ = V₁ ⊔ (V₂ ⊔ V₃) := by
  sorry

/-- 1C.18(a) Addition on subspaces has an additive identity, namely
{lit}`{0}` ({lit}`⊥` in mathlib). -/
@[avoiding bot_sup_eq, sup_bot_eq]
theorem exercise_1C_18_id (U : Submodule F V) : U ⊔ ⊥ = U := by
  sorry

/-- 1C.18(b) The only subspace with an additive inverse is {lit}`{0}` itself:
if {lit}`U + W = {0}` then both {lit}`U = {0}` and {lit}`W = {0}`. -/
theorem exercise_1C_18_inv (U W : Submodule F V) (h : U ⊔ W = ⊥) :
    U = ⊥ ∧ W = ⊥ := by
  sorry

/-- 1C.19 *Counterexample.* There exist subspaces {lit}`V₁, V₂, U` with
{lit}`V₁ + U = V₂ + U` but {lit}`V₁ ≠ V₂`. -/
theorem exercise_1C_19 :
    ∃ V₁ V₂ U : Submodule ℝ (Fin 2 → ℝ),
      V₁ ⊔ U = V₂ ⊔ U ∧ V₁ ≠ V₂ := by
  sorry

/-- 1C.20 There is a subspace {lit}`W` of {lit}`F⁴` such that
{lit}`F⁴ = U ⊕ W`, where {lit}`U = {(x, x, y, y) : x, y ∈ F}`. -/
theorem exercise_1C_20 (U : Submodule F (Fin 4 → F)) :
    ∃ W : Submodule F (Fin 4 → F), IsCompl U W := by
  sorry

/-- 1C.21 There is a subspace {lit}`W` of {lit}`F⁵` such that
{lit}`F⁵ = U ⊕ W`, where
{lit}`U = {(x, y, x+y, x-y, 2x) : x, y ∈ F}`. -/
theorem exercise_1C_21 (U : Submodule F (Fin 5 → F)) :
    ∃ W : Submodule F (Fin 5 → F), IsCompl U W := by
  sorry

/-- 1C.22 There exist three nonzero subspaces {lit}`W₁, W₂, W₃` of {lit}`F⁵`
such that {lit}`F⁵ = U ⊕ W₁ ⊕ W₂ ⊕ W₃`, with {lit}`U` as in 1C.21. -/
theorem exercise_1C_22 (U : Submodule F (Fin 5 → F)) :
    ∃ W₁ W₂ W₃ : Submodule F (Fin 5 → F),
      W₁ ≠ ⊥ ∧ W₂ ≠ ⊥ ∧ W₃ ≠ ⊥ ∧
      IsCompl U (W₁ ⊔ W₂ ⊔ W₃) ∧
      Disjoint W₁ W₂ ∧ Disjoint (W₁ ⊔ W₂) W₃ := by
  sorry

/-- 1C.23 *Counterexample.* There exist subspaces {lit}`V₁, V₂, U` with
{lit}`V = V₁ ⊕ U` and {lit}`V = V₂ ⊕ U` but {lit}`V₁ ≠ V₂`. -/
theorem exercise_1C_23 :
    ∃ V₁ V₂ U : Submodule ℝ (Fin 2 → ℝ),
      IsCompl V₁ U ∧ IsCompl V₂ U ∧ V₁ ≠ V₂ := by
  sorry

/-- 1C.24 Let {lit}`Vₑ` be the even and {lit}`Vₒ` the odd real-valued
functions on {lit}`ℝ`. Then {lit}`ℝ → ℝ = Vₑ ⊕ Vₒ`. -/
def evenFunctions : Submodule ℝ (ℝ → ℝ) where
  carrier := {f | ∀ x, f (-x) = f x}
  zero_mem' := by intro x; simp
  add_mem' := by
    intro f g hf hg x
    show (f + g) (-x) = (f + g) x
    simp [Pi.add_apply, hf x, hg x]
  smul_mem' := by
    intro a f hf x
    show (a • f) (-x) = (a • f) x
    simp [Pi.smul_apply, hf x]

def oddFunctions : Submodule ℝ (ℝ → ℝ) where
  carrier := {f | ∀ x, f (-x) = -f x}
  zero_mem' := by intro x; simp
  add_mem' := by
    intro f g hf hg x
    show (f + g) (-x) = -((f + g) x)
    simp only [Pi.add_apply]
    rw [hf x, hg x]; ring
  smul_mem' := by
    intro a f hf x
    show (a • f) (-x) = -((a • f) x)
    simp only [Pi.smul_apply]
    rw [hf x]; ring

theorem exercise_1C_24 : IsCompl evenFunctions oddFunctions := by
  sorry

end LADR.Section_1C
