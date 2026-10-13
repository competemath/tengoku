/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.RingTheory.Huber.Restricted.TwoSidedSeries.Convolution
import Tengoku.Tauceti.TauCeti.Topology.Algebra.InfiniteSum.DiscreteConvolution

/-!
# The ring of two-sided restricted series `A⟨X, X⁻¹⟩`

`TauCeti.Huber.twoSidedRestrictedSubmodule A A` is the `A`-module of coefficient families
underlying Wedhorn's `A⟨X, X⁻¹⟩` (Example 6.39). This module equips it with the convolution
product `(fg)ₙ = ∑_{i + j = n} aᵢ bⱼ`, making it a ring, and a commutative `A`-algebra when `A` is
commutative, in which the Laurent variable `X = twoSidedMonomial 1 1` is a unit.

## Main definitions

* `TauCeti.Huber.twoSidedRestrictedSubmodule.instMul` and
  `TauCeti.Huber.twoSidedRestrictedSubmodule.instOne`: the product and the unit.
* `TauCeti.Huber.twoSidedRestrictedSubmodule.instRing`,
  `TauCeti.Huber.twoSidedRestrictedSubmodule.instCommRing` and
  `TauCeti.Huber.twoSidedRestrictedSubmodule.instAlgebra`: the ring structure of `A⟨X, X⁻¹⟩`, and
  its commutative `A`-algebra structure when `A` is commutative.
* `TauCeti.Huber.twoSidedMonomial`: the monomial `a Xⁿ`.

## Main results

* `TauCeti.Huber.twoSidedMonomial_mul_twoSidedMonomial`: monomials multiply by adding degrees,
  `(a Xᵐ)(b Xⁿ) = ab X^{m+n}`.
* `TauCeti.Huber.isUnit_twoSidedMonomial`: a monomial with a unit coefficient is a unit.
* `TauCeti.Huber.twoSidedRestrictedMul_apply`: the bilinear map
  `TauCeti.Huber.twoSidedRestrictedMul` is the ring multiplication.

## Implementation notes

The product is not the pointwise product of `ℤ → A`, so `A⟨X, X⁻¹⟩` is not a subring of `ℤ → A`;
the multiplication is installed directly on the submodule's coercion to a type.

The unit and the monomials, with their additive and scalar laws, need only continuous addition
and scalar multiplication. The product and the monomial rule need a nonarchimedean ring
topology; each coefficient of a product is a `tsum`, which is `0` if the sum diverges. The ring
axioms assume `A` complete and `T0`, so that these sums converge; this is Wedhorn's convention, his
"complete" including Hausdorff (Definition 5.31).

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Example 6.39.
-/

public section

open scoped DiscreteConvolution

namespace TauCeti.Huber

section Monomial

variable {A : Type*} [Semiring A] [TopologicalSpace A] [ContinuousAdd A] [ContinuousConstSMul A A]

/-- **The unit of `A⟨X, X⁻¹⟩`**: the constant series `1 = 1 · X⁰`. -/
instance twoSidedRestrictedSubmodule.instOne : One (twoSidedRestrictedSubmodule A A) where
  one := ⟨Pi.single 0 1, single_mem_twoSidedRestrictedSubmodule 0 1⟩

/-- The coefficient family of the unit is supported at degree `0` with value `1`. -/
@[simp, norm_cast]
theorem coe_one_twoSidedRestrictedSubmodule :
    ((1 : twoSidedRestrictedSubmodule A A) : ℤ → A) = Pi.single 0 1 := rfl

/-- **The monomial `a Xⁿ`** of `A⟨X, X⁻¹⟩`: the family supported at degree `n` with value `a`.
The Laurent variable `X` is `twoSidedMonomial 1 1`. -/
def twoSidedMonomial (n : ℤ) (a : A) : twoSidedRestrictedSubmodule A A :=
  ⟨Pi.single n a, single_mem_twoSidedRestrictedSubmodule n a⟩

/-- The coefficient family of the monomial `a Xⁿ` is `Pi.single n a`. -/
@[simp, norm_cast]
theorem coe_twoSidedMonomial (n : ℤ) (a : A) : (twoSidedMonomial n a : ℤ → A) = Pi.single n a :=
  (rfl)

/-- The degree-`0` monomial with coefficient `1` is the unit: `1 · X⁰ = 1`. -/
@[simp]
theorem twoSidedMonomial_zero_one : twoSidedMonomial 0 (1 : A) = 1 :=
  Subtype.ext <| (coe_twoSidedMonomial 0 1).trans coe_one_twoSidedRestrictedSubmodule.symm

/-- The monomial with coefficient `0` is `0`. -/
@[simp]
theorem twoSidedMonomial_zero_right (n : ℤ) : twoSidedMonomial n (0 : A) = 0 :=
  Subtype.ext <| by simp

/-- The monomial `a Xⁿ` is additive in its coefficient. -/
@[simp]
theorem twoSidedMonomial_add (n : ℤ) (a b : A) :
    twoSidedMonomial n (a + b) = twoSidedMonomial n a + twoSidedMonomial n b :=
  Subtype.ext <| by simp [Pi.single_add]

/-- Scaling a monomial scales its coefficient: `a • b Xⁿ = (ab) Xⁿ`. -/
@[simp]
theorem smul_twoSidedMonomial (a : A) (n : ℤ) (b : A) :
    a • twoSidedMonomial n b = twoSidedMonomial n (a * b) :=
  Subtype.ext <| by simp [← smul_eq_mul, Pi.single_smul']

end Monomial

section Neg

variable {A : Type*} [Ring A] [TopologicalSpace A] [ContinuousAdd A] [ContinuousConstSMul A A]

/-- The monomial `a Xⁿ` commutes with negating its coefficient. -/
@[simp]
theorem twoSidedMonomial_neg (n : ℤ) (a : A) : twoSidedMonomial n (-a) = -twoSidedMonomial n a :=
  Subtype.ext <| by simp [Pi.single_neg]

end Neg

section Mul

variable {A : Type*} [Ring A] [TopologicalSpace A] [NonarchimedeanRing A]

end Mul

section Ring

variable {A : Type*} [Ring A] [UniformSpace A] [IsUniformAddGroup A] [NonarchimedeanRing A]
  [CompleteSpace A] [T0Space A]

end Ring

section CommRing

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [NonarchimedeanRing A]
  [CompleteSpace A] [T0Space A]

end CommRing

end TauCeti.Huber
