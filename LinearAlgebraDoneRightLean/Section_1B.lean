import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.PUnit
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Recall
import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 1B: Definition of Vector Space
-/

namespace LADR.Section_1B

/-! 1.19–1.20 Definition: addition, scalar multiplication; vector space -/

structure LADRVectorSpace (F : Type*) [Field F] (V : Type*) where
  /-- Definition 1.19: addition -/
  add : V → V → V
  /-- Definition 1.19: scalar multiplication -/
  smul : F → V → V

  /-- Definition 1.20: commutativity -/
  add_comm : ∀ u v, add u v = add v u
  /-- Definition 1.20: associativity (addition) -/
  add_assoc : ∀ u v w, add (add u v) w = add u (add v w)
  /-- Definition 1.20: associativity (scalar multiplication) -/
  mul_smul : ∀ a b v, smul (a * b) v = smul a (smul b v)
  /-- Definition 1.20: additive identity -/
  zero : V
  add_zero : ∀ v, add v zero = v
  /-- Definition 1.20: additive inverse -/
  neg : V → V
  add_neg_cancel : ∀ v, add v (neg v) = zero
  /-- Definition 1.20: multiplicative identity -/
  one_smul : ∀ v, smul (1 : F) v = v
  /-- Definition 1.20: distributive properties -/
  smul_add : ∀ a u v, smul a (add u v) = add (smul a u) (smul a v)
  add_smul : ∀ a b v, smul (a + b) v = add (smul a v) (smul b v)

/-! Instead of using the definition above, we will use mathlib's definition.

As usual, mathlib has a more general definition, but the special case of
{lit}`Module F V` (over {lit}`[AddCommGroup V]`) where {lit}`[Field F]` is exactly
equivalent to Axler's "vector space over {lit}`F`". -/

/-! You will learn what these mean in an abstract algebra course, but
for now, just treat them as a magic incantation that gives us the properties
of vector spaces. -/
variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]

/-! The eight axioms above are derivable from the typeclass methods and
we get to use a nicer notation. -/
recall add_comm {G : Type*} [AddCommMagma G] (a b : G) : a + b = b + a
recall add_assoc {G : Type*} [AddSemigroup G] (a b c : G) : a + b + c = a + (b + c)
recall add_zero {M : Type*} [AddZeroClass M] (a : M) : a + 0 = a
recall add_neg_cancel {G : Type*} [AddGroup G] (a : G) : a + -a = 0
recall one_smul (M : Type*) {α : Type*} [Monoid M] [MulAction M α] (b : α) : (1 : M) • b = b
recall smul_add {M : Type*} {A : Type*} [AddZeroClass A] [DistribSMul M A]
    (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
recall add_smul {R : Type*} {M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (r s : R) (x : M) : (r + s) • x = r • x + s • x
recall mul_smul {α : Type*} {β : Type*} [Semigroup α] [SemigroupAction α β]
    (x y : α) (b : β) : (x * y) • b = x • y • b

/-! 1.21 Definition: vector, point

Elements {lit}`v : V` are called vectors or points. -/

/-! 1.22 Definition: real vector space, complex vector space

A vector space over {lit}`ℝ` is a real vector space; over {lit}`ℂ`, a complex vector space.
In Lean, whenever we see {lit}`{V : Type*} [AddCommGroup V] [Module ℝ V]`, that is a
real vector space; with {lit}`[Module ℂ V]`, a complex vector space. -/


/-! 1.23 Example: F∞

{lit}`F∞` is the set of all sequences of elements of {lit}`F`; in Lean, {lit}`ℕ → F`. -/

example : AddCommGroup (ℕ → F) := inferInstance
example : Module F (ℕ → F) := inferInstance

example (f g : ℕ → ℝ) (i : ℕ) : (f + g) i = f i + g i := rfl
example (c : ℝ) (f : ℕ → ℝ) (i : ℕ) : (c • f) i = c * f i := rfl

/-! The simplest vector space is the one-element space {lit}`{0}`. In Lean this is
{lit}`PUnit`; mathlib provides the instances automatically. -/

example (F : Type*) [Field F] : Module F PUnit := inferInstance
example (v w : PUnit) : v = w := rfl

/-! 1.24 Notation: F^S

For a set {lit}`S`, {lit}`F^S` denotes the set of functions from {lit}`S` to {lit}`F`. In Lean we
just write {lit}`S → F`. Addition and scalar multiplication are pointwise. -/

example (S : Type*) (f g : S → F) (x : S) : (f + g) x = f x + g x := rfl
example (S : Type*) (c : F) (f : S → F) (x : S) : (c • f) x = c * f x := rfl

/-! 1.25 Example: F^S is a vector space

The additive identity of {lit}`F^S` is the function {lit}`0 : S → F` defined by
{lit}`0 x = 0` for all {lit}`x ∈ S`. For {lit}`f : S → F`, the additive inverse {lit}`-f`
is defined by {lit}`(-f) x = -(f x)` for all {lit}`x ∈ S`. -/

example (S : Type*) : AddCommGroup (S → F) := inferInstance
example (S : Type*) : Module F (S → F) := inferInstance

example (S : Type*) (x : S) : (0 : S → F) x = 0 := rfl
example (S : Type*) (f : S → F) (x : S) : (-f) x = -(f x) := rfl

/-! 1.26 Unique additive identity

If {lit}`z` acts as an additive identity (i.e. {lit}`v + z = v` for every {lit}`v`), then {lit}`z = 0`. -/

theorem unique_zero (z : V) (h : ∀ v, v + z = v) : z = 0 :=
  calc z = z + 0     := (add_zero z).symm
    _    = 0 + z     := add_comm z 0
    _    = 0         := h 0

/-! 1.27 Unique additive inverse

If {lit}`v + w = 0`, then {lit}`w = -v`. -/

theorem unique_neg (v w : V) (h : v + w = 0) : w = -v :=
  calc w = w + 0                 := (add_zero w).symm
    _    = w + (v + (-v))        := by rw [add_neg_cancel]
    _    = (w + v) + (-v)        := (add_assoc w v (-v)).symm
    _    = (v + w) + (-v)        := by rw [add_comm w v]
    _    = 0 + (-v)              := by rw [h]
    _    = -v                    := zero_add (-v)

/-! 1.28 Notation: −v, w − v

{lit}`-v` is the additive inverse of {lit}`v`; {lit}`w - v` is shorthand for {lit}`w + (-v)`. -/

example (v : V) : v + (-v) = 0 := add_neg_cancel v
example (v w : V) : w - v = w + (-v) := sub_eq_add_neg w v

/-! 1.29 Notation: V

For the rest of this section, {lit}`V` denotes a vector space over {lit}`F` (declared
once at the top via {lit}`variable {V : Type*} [AddCommGroup V] [Module F V]`). -/

/-! 1.30 The number 0 times a vector

For every {lit}`v ∈ V`, {lit}`0 • v = 0` (the scalar {lit}`0 ∈ F` times any vector is the
zero vector). -/

example (v : V) : (0 : F) • v = 0 := by
  have h : (0 : F) • v = (0 : F) • v + (0 : F) • v :=
    calc (0 : F) • v = (0 + 0 : F) • v          := by rw [add_zero]
      _              = (0 : F) • v + (0 : F) • v := add_smul 0 0 v
  -- Add `-(0 • v)` to both sides of `h`, then simplify.
  have h2 := congrArg (· + -((0 : F) • v)) h
  rw [add_neg_cancel, add_assoc, add_neg_cancel, add_zero] at h2
  exact h2.symm

/-! 1.31 A number times the vector 0

For every {lit}`a ∈ F`, {lit}`a • 0 = 0` (any scalar times the zero vector is the
zero vector). -/

example (a : F) : a • (0 : V) = 0 := smul_zero a

/-! 1.32 The number −1 times a vector

{lit}`(-1) • v = -v`, i.e. multiplying by the scalar {lit}`-1` produces the additive
inverse. -/

example (v : V) : (-1 : F) • v = -v := neg_one_smul F v

/-! # Exercises -/

/-- 1B.1 Show that {lit}`-(-v) = v` for every {lit}`v ∈ V`. -/
@[avoiding neg_neg]
theorem exercise_1B_1 (v : V) : -(-v) = v := by
  sorry

/-- 1B.2 Suppose {lit}`a ∈ F`, {lit}`v ∈ V`, and {lit}`a • v = 0`. Prove {lit}`a = 0` or {lit}`v = 0`. -/
@[avoiding smul_eq_zero, smul_eq_zero_iff_eq, smul_eq_zero_iff_eq']
theorem exercise_1B_2 (a : F) (v : V) (h : a • v = 0) :
    a = 0 ∨ v = 0 := by
  sorry

/-- 1B.3 For all {lit}`v, w ∈ V`, there is a unique {lit}`x ∈ V` with {lit}`v + 3 • x = w`. -/
theorem exercise_1B_3 (v w : V) : ∃! x : V, v + (3 : F) • x = w := by
  sorry

end LADR.Section_1B
