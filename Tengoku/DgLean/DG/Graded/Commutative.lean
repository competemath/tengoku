import Tengoku.Seed.RingTheory.GradedAlgebra.Basic
import Tengoku.DgLean.DG.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Graded commutativity

For a `ℤ`-graded `R`-algebra `A` with grading `𝒜 : ℤ → Submodule R A`, this file defines the
predicate `DG.IsGradedComm 𝒜`, graded commutativity (also called supercommutativity or
commutativity in the graded sense): for homogeneous elements `a ∈ 𝒜 i` and `b ∈ 𝒜 j`,

  `a * b = (-1)^(i * j) • (b * a)`,

with the sign written `koszulSign (i * j) • _` (`DG.koszulSign n = Int.negOnePow n : ℤˣ`).

## Main definitions and results

* `DG.IsGradedComm 𝒜`: the graded commutativity predicate.
* `DG.IsGradedCommStrict 𝒜`: graded commutativity together with `a * a = 0` for every
  homogeneous `a` of odd degree (the "strict" version; the two differ only in the presence of
  `2`-torsion).
* `DG.IsGradedComm.mem_center_of_even`: homogeneous elements of even degree are central.
* `DG.IsGradedComm.two_nsmul_mul_self_of_odd`: for `a` homogeneous of odd degree,
  `2 • (a * a) = 0`.
* `DG.IsGradedCommStrict.of_noZeroSMulDivisors`: if `A` has no `2`-torsion (more precisely,
  `NoZeroSMulDivisors ℕ A`), graded commutativity implies strict graded commutativity.
* `DG.map_mul_of_homogeneous`: an additive map out of a graded algebra is multiplicative as soon
  as it is multiplicative on pairs of homogeneous elements.

The predicate only refers to the family `𝒜` and the multiplication; the consequences that
involve arbitrary (non-homogeneous) elements need `[GradedAlgebra 𝒜]`.
-/

namespace DG

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
variable (𝒜 : ℤ → Submodule R A)

/-- An additive map out of a graded algebra is multiplicative if it is multiplicative on pairs of
homogeneous elements.
@isnad1 id=eq.1h8v.s9.27753526cecf from=translated src=- shape=5073912c vocab=97adba54
-/
theorem map_mul_of_homogeneous [GradedAlgebra 𝒜] {B F : Type*} [NonUnitalNonAssocSemiring B]
    [FunLike F A B] [AddMonoidHomClass F A B] (f : F)
    (h : ∀ {i j : ℤ} (a : 𝒜 i) (b : 𝒜 j), f (a * b) = f a * f b) (x y : A) :
    f (x * y) = f x * f y := by
  refine DirectSum.Decomposition.inductionOn 𝒜
    (motive := fun x => ∀ y, f (x * y) = f x * f y) ?_ ?_ ?_ x y
  · intro y
    rw [zero_mul, map_zero, zero_mul]
  · intro i a
    refine DirectSum.Decomposition.inductionOn 𝒜
      (motive := fun y => f (a * y) = f a * f y) ?_ ?_ ?_
    · show f (a * 0) = f a * f 0
      rw [mul_zero, map_zero, mul_zero]
    · intro j b
      exact h a b
    · intro y y' hy hy'
      show f (a * (y + y')) = f a * f (y + y')
      rw [mul_add, map_add, hy, hy', map_add, mul_add]
  · intro x x' hx hx' y
    rw [add_mul, map_add, hx, hx', map_add, add_mul]

/-- A `ℤ`-graded algebra is *graded commutative* if `a * b = (-1)^(i * j) • (b * a)` for all
homogeneous elements `a` of degree `i` and `b` of degree `j`.-/
class IsGradedComm : Prop where
  /-- Homogeneous elements commute up to the Koszul sign.-/
  mul_comm_of_mem : ∀ {i j : ℤ} {a b : A}, a ∈ 𝒜 i → b ∈ 𝒜 j →
    a * b = koszulSign (i * j) • (b * a)

/-- A `ℤ`-graded algebra is *strictly graded commutative* if it is graded commutative and every
homogeneous element of odd degree squares to zero.-/
class IsGradedCommStrict : Prop extends IsGradedComm 𝒜 where
  /-- Homogeneous elements of odd degree square to zero.-/
  mul_self_of_odd : ∀ {i : ℤ} {a : A}, a ∈ 𝒜 i → Odd i → a * a = 0

namespace IsGradedComm

variable {𝒜} [IsGradedComm 𝒜]

/--
@isnad1 id=eq.2h7v.s8.3741c887058a from=translated src=- shape=4c57750f vocab=5b843987
-/
theorem mul_comm_of_mem' {i j : ℤ} {a b : A} (ha : a ∈ 𝒜 i) (hb : b ∈ 𝒜 j) :
    b * a = koszulSign (i * j) • (a * b) := by
  rw [mul_comm_of_mem ha hb, smul_smul, Int.units_mul_self, one_smul]

/--
@isnad1 id=eq.3h7v.s8.7c9d7b7181d4 from=translated src=- shape=d61fe675 vocab=b6233993
-/
theorem mul_comm_of_mem_of_even {i j : ℤ} {a b : A} (ha : a ∈ 𝒜 i) (hb : b ∈ 𝒜 j)
    (h : Even (i * j)) : a * b = b * a := by
  rw [mul_comm_of_mem ha hb, koszulSign_even h, one_smul]

/--
@isnad1 id=eq.3h7v.s8.fdbcb47ae40b from=translated src=- shape=e2bb5910 vocab=489fc9c6
-/
theorem mul_comm_of_mem_of_odd {i j : ℤ} {a b : A} (ha : a ∈ 𝒜 i) (hb : b ∈ 𝒜 j)
    (h : Odd (i * j)) : a * b = -(b * a) := by
  rw [mul_comm_of_mem ha hb, koszulSign_odd h, Units.neg_smul, one_smul]

/-- Two homogeneous elements commute when one of them has even degree.
@isnad1 id=eq.3h7v.s7.afbe6660242d from=translated src=- shape=1cdc5e94 vocab=b6233993
-/
theorem mul_comm_of_mem_of_even_left {i j : ℤ} {a b : A} (ha : a ∈ 𝒜 i) (hb : b ∈ 𝒜 j)
    (hi : Even i) : a * b = b * a :=
  mul_comm_of_mem_of_even ha hb (hi.mul_right j)

/-- Two homogeneous elements anticommute when both have odd degree.
@isnad1 id=eq.4h7v.s8.0696fc0f5338 from=translated src=- shape=f3039ac7 vocab=489fc9c6
-/
theorem mul_comm_of_mem_of_odd_of_odd {i j : ℤ} {a b : A} (ha : a ∈ 𝒜 i) (hb : b ∈ 𝒜 j)
    (hi : Odd i) (hj : Odd j) : a * b = -(b * a) :=
  mul_comm_of_mem_of_odd ha hb (hi.mul hj)

/-- A homogeneous element of odd degree anticommutes with itself: `a * a = -(a * a)`.
@isnad1 id=eq.2h5v.s7.c4fd9c483fe4 from=translated src=- shape=946ffc20 vocab=489fc9c6
-/
theorem mul_self_eq_neg_of_odd {i : ℤ} {a : A} (ha : a ∈ 𝒜 i) (hi : Odd i) :
    a * a = -(a * a) :=
  mul_comm_of_mem_of_odd_of_odd ha ha hi hi

/-- The square of a homogeneous element of odd degree is `2`-torsion.
@isnad1 id=eq.2h5v.s7.dfb0a3691baf from=translated src=- shape=5b4f799f vocab=35818c63
-/
theorem two_nsmul_mul_self_of_odd {i : ℤ} {a : A} (ha : a ∈ 𝒜 i) (hi : Odd i) :
    2 • (a * a) = 0 := by
  rw [two_nsmul, ← sub_neg_eq_add, ← mul_self_eq_neg_of_odd ha hi, sub_self]

/-- In a graded commutative algebra, every homogeneous element of even degree is central.
@isnad1 id=mem.2h5v.s7.4a0b794276fa from=translated src=- shape=4f26d47d vocab=df042f97
-/
theorem mem_center_of_even [GradedAlgebra 𝒜] {i : ℤ} {a : A} (ha : a ∈ 𝒜 i) (hi : Even i) :
    a ∈ Subalgebra.center R A := by
  rw [Subalgebra.mem_center_iff]
  refine DirectSum.Decomposition.inductionOn 𝒜 ?_ ?_ ?_
  · simp
  · intro j b
    exact (mul_comm_of_mem_of_even_left ha b.2 hi).symm
  · intro b c hb hc
    rw [add_mul, mul_add, hb, hc]

/-- In a graded commutative algebra, a homogeneous element of even degree commutes with every
element.
@isnad1 id=commute.2h6v.s7.f9c5f5fa82a1 from=translated src=- shape=566199ca vocab=9d5592e5
-/
theorem commute_of_even [GradedAlgebra 𝒜] {i : ℤ} {a : A} (ha : a ∈ 𝒜 i) (hi : Even i)
    (b : A) : Commute a b :=
  (Subalgebra.mem_center_iff.mp (mem_center_of_even ha hi) b).symm

end IsGradedComm

namespace IsGradedCommStrict

variable {𝒜}

/-- Without `2`-torsion, graded commutativity is automatically strict.
@isnad1 id=isgraded.0h3v.s6.c57433fa7186 from=translated src=- shape=a2dec1e8 vocab=401e28bc
-/
theorem of_noZeroSMulDivisors [IsGradedComm 𝒜] [NoZeroSMulDivisors ℕ A] :
    IsGradedCommStrict 𝒜 where
  mul_self_of_odd ha hi := by
    have h := IsGradedComm.two_nsmul_mul_self_of_odd ha hi
    rcases smul_eq_zero.mp h with h | h
    · exact absurd h two_ne_zero
    · exact h

end IsGradedCommStrict

end DG
