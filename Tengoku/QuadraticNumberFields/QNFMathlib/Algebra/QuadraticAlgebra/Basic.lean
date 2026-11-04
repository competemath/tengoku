/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Tengoku.Seed.Algebra.QuadraticAlgebra.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Units of Quadratic Algebras

Material destined for mathlib.

Explicit units of `QuadraticAlgebra R a b` attached to elements of norm `±1`:
the relation `z * star z = N(z)` makes the (negated) conjugate an explicit
inverse.  Over `ℤ`, this also gives the usual `norm = ±1` unit criterion.
-/

namespace QuadraticAlgebra

variable {R : Type*} [CommRing R] {a b : R}

/-- The norm of `⟨x, y⟩ : QuadraticAlgebra R a b` in coordinates.
@isnad1 id=eq.0h5v.s7.5598035696ec from=translated src=- shape=b558feb3 vocab=ec03ef79
-/
-- Repository use: coordinate computations for units of `ℤ[√d]` and `ℤ[(1+√d)/2]`.
theorem norm_mk (x y : R) :
    norm (⟨x, y⟩ : QuadraticAlgebra R a b) = x * x + b * x * y - a * y * y :=
  rfl

/-- The unit of `QuadraticAlgebra R a b` attached to an element of norm `1`;
the inverse is the conjugate.-/
-- Repository use: explicit units of `ℤ[√d]` and `ℤ[(1+√d)/2]` from Pell-type solutions.
def unitOfNormOne (z : QuadraticAlgebra R a b) (h : norm z = 1) :
    (QuadraticAlgebra R a b)ˣ where
  val := z
  inv := star z
  val_inv := by rw [← algebraMap_norm_eq_mul_star, h, map_one]
  inv_val := by rw [mul_comm, ← algebraMap_norm_eq_mul_star, h, map_one]

/--
@isnad1 id=eq.1h4v.s7.3fc1357dfe75 from=translated src=- shape=65a2daa1 vocab=1cadc04d
-/
@[simp]
theorem val_unitOfNormOne (z : QuadraticAlgebra R a b) (h : norm z = 1) :
    (unitOfNormOne z h : QuadraticAlgebra R a b) = z :=
  rfl

/--
@isnad1 id=eq.1h4v.s7.67679480a750 from=translated src=- shape=24a066f7 vocab=c5b765a9
-/
@[simp]
theorem val_inv_unitOfNormOne (z : QuadraticAlgebra R a b) (h : norm z = 1) :
    (((unitOfNormOne z h)⁻¹ : (QuadraticAlgebra R a b)ˣ) : QuadraticAlgebra R a b) = star z :=
  rfl

/-- The unit of `QuadraticAlgebra R a b` attached to an element of norm `-1`;
the inverse is the negated conjugate.-/
-- Repository use: explicit units of `ℤ[√d]` from norm-`-1` Pell solutions.
def unitOfNormNegOne (z : QuadraticAlgebra R a b) (h : norm z = -1) :
    (QuadraticAlgebra R a b)ˣ where
  val := z
  inv := -star z
  val_inv := by rw [mul_neg, ← algebraMap_norm_eq_mul_star, h, map_neg, map_one, neg_neg]
  inv_val := by
    rw [neg_mul, mul_comm (star z) z, ← algebraMap_norm_eq_mul_star, h, map_neg, map_one, neg_neg]

/--
@isnad1 id=eq.1h4v.s7.b56892a8f9b6 from=translated src=- shape=4e50c208 vocab=187728d8
-/
@[simp]
theorem val_unitOfNormNegOne (z : QuadraticAlgebra R a b) (h : norm z = -1) :
    (unitOfNormNegOne z h : QuadraticAlgebra R a b) = z :=
  rfl

/--
@isnad1 id=eq.1h4v.s8.137acfcdf131 from=translated src=- shape=f53d1e22 vocab=8988b0de
-/
@[simp]
theorem val_inv_unitOfNormNegOne (z : QuadraticAlgebra R a b) (h : norm z = -1) :
    (((unitOfNormNegOne z h)⁻¹ : (QuadraticAlgebra R a b)ˣ) : QuadraticAlgebra R a b) =
      -star z :=
  rfl

section Int

variable {a b : ℤ}

/-- Over `ℤ`, an element of a quadratic algebra is a unit iff its norm is `±1`.
@isnad1 id=iff.0h3v.s8.a674d7953d4c from=translated src=- shape=679c201b vocab=1357c9ed
-/
-- Repository use: unit criteria for the two explicit quadratic-integer models.
theorem isUnit_iff_norm_eq_one_or_neg_one (z : QuadraticAlgebra ℤ a b) :
    IsUnit z ↔ norm z = 1 ∨ norm z = -1 :=
  isUnit_iff_norm_isUnit.trans Int.isUnit_iff

/-- Over `ℤ`, a nonpositive discriminant `b² + 4a ≤ 0` makes the norm
nonnegative: `4·N(z) = (2·re + b·im)² - (b² + 4a)·im²`.
@isnad1 id=le.1h3v.s7.08c7fd639c9c from=translated src=- shape=f3238337 vocab=82e824af
-/
-- Repository use: unit-group classification for imaginary quadratic orders.
theorem norm_nonneg_of_discr_nonpos (h : b ^ 2 + 4 * a ≤ 0) (z : QuadraticAlgebra ℤ a b) :
    0 ≤ norm z := by
  have hz := norm_def z
  nlinarith [sq_nonneg (2 * z.re + b * z.im), sq_nonneg z.im]

/-- Over `ℤ`, a discriminant `b² + 4a < -4` forces the unit group of
`QuadraticAlgebra ℤ a b` to be `{±1}`.
@isnad1 id=iff.1h3v.s7.8b8b45b898fe from=translated src=- shape=7746cd1e vocab=aac591e7
-/
-- Repository use: the `±1` unit classifications for `ℤ[√d]` (`d < -1`) and
-- `ℤ[(1+√d)/2]` (`d ≤ -7`) are instances of this single statement.
theorem isUnit_iff_eq_one_or_neg_one_of_discr_lt_neg_four (h : b ^ 2 + 4 * a < -4)
    (z : QuadraticAlgebra ℤ a b) : IsUnit z ↔ z = 1 ∨ z = -1 := by
  constructor
  · intro hz
    obtain ⟨x, y⟩ := z
    rcases Int.isUnit_iff.mp (isUnit_iff_norm_isUnit.mp hz) with hn | hn
    · rw [norm_mk] at hn
      have hy : y = 0 := by nlinarith [sq_nonneg (2 * x + b * y), sq_nonneg y]
      subst hy
      have hx : x * x = 1 := by linarith
      rcases mul_self_eq_one_iff.mp hx with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (by ext <;> simp)
    · have h0 : (0 : ℤ) ≤ norm (⟨x, y⟩ : QuadraticAlgebra ℤ a b) :=
        norm_nonneg_of_discr_nonpos (by linarith) _
      omega
  · rintro (rfl | rfl)
    · exact isUnit_one
    · exact isUnit_one.neg

end Int

end QuadraticAlgebra
