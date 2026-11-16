/-
Copyright (c) 2026 Timothy Harvey and James Mitchell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timothy Harvey
-/
import Tengoku.Seed.Algebra.Group.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Inverse Semigroups: Definitions

This file defines inverse semigroups: semigroups in which every element `a` has a
unique inverse `b`, meaning `a * b * a = a` and `b * a * b = b`. The inverse is
axiomatized as a chosen operation `⁻¹` together with a uniqueness axiom.

## Main definitions

* `IsInverseOf`: `IsInverseOf b a` means `b` is a (von Neumann) inverse of `a`.
* `IsRegularElem`: an element is regular if it has an inner inverse.
* `InverseSemigroup`: a semigroup with an inverse operation `⁻¹` such that `a⁻¹`
  is the unique inverse of `a`.

## Main results

* `InverseSemigroup.isInverseOf_inv`: `a⁻¹` is an inverse of `a`.
* `InverseSemigroup.isRegularElem`: every element of an inverse semigroup is regular.

## References

* [J. M. Howie, *Fundamentals of Semigroup Theory*][howie1995]

The proofs formalized in this module closely follow the structure and logic
from lecture notes:

* J. D. Mitchell, *MT5863 Semigroup Theory* (lecture notes,
  University of St Andrews, 2026).
-/
namespace Tengoku.Semigroup end Tengoku.Semigroup open Tengoku.Semigroup
/-- `IsInverseOf b a` means `b` is a (von Neumann) inverse of `a`:
`a * b * a = a` and `b * a * b = b`.-/
def _root_.Tengoku.Semigroup.IsInverseOf {S : Type*} [Semigroup S] (b a : S) : Prop :=
  a * b * a = a ∧ b * a * b = b

/-- An element is (von Neumann) regular if it has an inner inverse.-/
def _root_.Tengoku.Semigroup.IsRegularElem {S : Type*} [Semigroup S] (a : S) : Prop :=
  ∃ x : S, a * x * a = a

/-- An **inverse semigroup**: a semigroup equipped with an inverse operation
`⁻¹` such that `a⁻¹` is an inverse of `a` and is the *only* inverse of `a`.-/
class _root_.Tengoku.Semigroup.InverseSemigroup (S : Type*) extends Semigroup S, Inv S where
  /-- `a⁻¹` is an inner inverse of `a`.-/
  mul_inv_mul : ∀ a : S, a * a⁻¹ * a = a
  /-- `a` is an inner inverse of `a⁻¹`.-/
  inv_mul_inv : ∀ a : S, a⁻¹ * a * a⁻¹ = a⁻¹
  /-- Inverses are unique.-/
  inv_unique : ∀ {a b : S}, a * b * a = a → b * a * b = b → b = a⁻¹

namespace Tengoku.Semigroup.InverseSemigroup

variable {S : Type*} [InverseSemigroup S] (a : S)

/-- In an inverse semigroup, `a⁻¹` is an inverse of `a`:
`a * a⁻¹ * a = a` and `a⁻¹ * a * a⁻¹ = a⁻¹`.
@isnad1 id=isinvers.0h2v.s4.8eb894ea1cdf from=translated src=- shape=8d0018bb vocab=ac02ed2c
-/
theorem isInverseOf_inv : IsInverseOf a⁻¹ a :=
  ⟨mul_inv_mul a, inv_mul_inv a⟩

/-- Every element of an inverse semigroup is (von Neumann) regular.
@isnad1 id=isregula.0h2v.s3.e5226be052e5 from=translated src=- shape=368b3242 vocab=3556b035
-/
theorem isRegularElem : IsRegularElem a :=
  ⟨a⁻¹, mul_inv_mul a⟩

end Tengoku.Semigroup.InverseSemigroup
-- Tengoku: root names of this library moved to Tengoku.Semigroup so they do not collide with other libraries (generated)
