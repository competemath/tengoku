/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dimitris Mitsios
-/
module

import all Tengoku.Compply.CompPoly.Univariate.ToPoly.Impl
public import Tengoku.Compply.CompPoly.Univariate.Basic
public import Tengoku.Compply.CompPoly.Univariate.ToPoly.Impl
public import Tengoku.Seed.Algebra.Polynomial.Taylor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Formal Derivative and Taylor Shift of Computable Univariate Polynomials

Defines the formal derivative `CPolynomial.derivative` and the Taylor shift
`CPolynomial.taylor`, with proofs of their core properties.
-/

@[expose] public section

namespace CompPoly

namespace CPolynomial

/-- The formal derivative of a computable polynomial.
    Coefficient `n` of the result is `coeff p (n+1) * (n+1)`.-/
def derivative [Semiring R] [BEq R] [LawfulBEq R]
    (p : CPolynomial R) : CPolynomial R :=
  let arr : Array R :=
    (p.val.extract 1 p.val.size).mapIdx
      fun i c => c * (Nat.cast (i + 1) : R)
  ⟨(Raw.mk arr).trim, Raw.Trim.isCanonical_trim _⟩

/-- Coefficient formula for the derivative.
@isnad1 id=eq.0h3v.s6.b2782b604250 from=translated src=- shape=6c6b96c2 vocab=a97c2c5a
-/
theorem coeff_derivative [Semiring R] [BEq R] [LawfulBEq R]
    (p : CPolynomial R) (n : ℕ) :
    coeff (derivative p) n = coeff p (n + 1) * (↑(n + 1) : R) := by
  simp only [derivative, coeff, Raw.Trim.coeff_eq_coeff, Raw.coeff, Raw.mk]
  by_cases hn : n + 1 < Array.size p.val
  · unfold Array.getD
    simp only [Array.size_mapIdx, Array.size_extract, Nat.min_self,
          hn, dite_true]
    split
    · simp [Array.getElem_mapIdx, Array.getElem_extract, Nat.add_comm 1 n]
    · omega
  · unfold Array.getD
    simp only [Array.size_mapIdx, Array.size_extract, Nat.min_self,
          hn, dite_false]
    split
    · omega
    · simp

/-- The derivative of the zero polynomial is zero.
@isnad1 id=eq.0h1v.s6.9b5e21620519 from=translated src=- shape=ccb2376b vocab=5d39c93b
-/
theorem derivative_zero [Semiring R] [BEq R] [LawfulBEq R] :
    derivative (0 : CPolynomial R) = 0 := by
  rw [eq_zero_iff_coeff_zero]
  intro i
  rw [coeff_derivative, CPolynomial.coeff_zero]
  simp

/-- The derivative of a constant is zero.
@isnad1 id=eq.0h2v.s5.872c45120eb1 from=translated src=- shape=fb630f1a vocab=b05a45e2
-/
theorem derivative_C [Semiring R] [BEq R] [LawfulBEq R] (r : R) :
    derivative (C r) = 0 := by
  rw [eq_zero_iff_coeff_zero]
  intro i
  rw [coeff_derivative, CPolynomial.coeff_C]
  simp

/-- The derivative of a monomial.
@isnad1 id=eq.0h3v.s6.9ed8e53bb03d from=translated src=- shape=a4c0c1ad vocab=e24ed8fa
-/
theorem derivative_monomial [Semiring R] [BEq R] [LawfulBEq R]
    [DecidableEq R] (n : ℕ) (r : R) :
    derivative (monomial n r) =
      monomial (n - 1) (r * (↑n : R)) := by
  rw [eq_iff_coeff]
  intro i
  rw [coeff_derivative, coeff_monomial, coeff_monomial]
  split_ifs <;> simp_all
  · omega
  · have : n = 0 := by omega
    simp [this]

/-- The derivative distributes over addition.
@isnad1 id=eq.0h3v.s7.bf8d68174640 from=translated src=- shape=d6f30d67 vocab=9b22d2c1
-/
theorem derivative_add [Semiring R] [BEq R] [LawfulBEq R] [DecidableEq R]
    (p q : CPolynomial R) :
    derivative (p + q) = derivative p + derivative q := by
  rw [eq_iff_coeff]
  intro i
  simp only [coeff_derivative, coeff_add]
  exact right_distrib _ _ _

/-- The computable derivative matches Mathlib's `Polynomial.derivative` under `toPoly`.
@isnad1 id=eq.0h2v.s7.3386ffb8dad8 from=translated src=- shape=d66bb44b vocab=5c633802
-/
theorem derivative_toPoly [Semiring R] [BEq R] [LawfulBEq R] (p : CPolynomial R) :
    (derivative p).toPoly = Polynomial.derivative (R := R) p.toPoly := by
  apply Polynomial.ext
  intro n
  simp only [Polynomial.coeff_derivative, CPolynomial.toPoly,
    Raw.coeff_toPoly, CPolynomial.coeff_derivative]
  push_cast; ring_nf

/-- The derivative satisfies the Leibniz product rule.
@isnad1 id=eq.0h3v.s7.81083d2f715b from=translated src=- shape=72bbf9b2 vocab=f2ae81eb
-/
theorem derivative_mul [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] (p q : CPolynomial R) :
    derivative (p * q) = derivative p * q + p * derivative q := by
  apply ringEquiv.injective
  change (derivative (p * q)).toPoly = (derivative p * q + p * derivative q).toPoly
  rw [derivative_toPoly, toPoly_mul, toPoly_add, toPoly_mul, toPoly_mul,
    derivative_toPoly, derivative_toPoly, Polynomial.derivative_mul]

/-- The Taylor shift `taylor a p = p(X + a)`.-/
def taylor [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (a : R) (p : CPolynomial R) : CPolynomial R :=
  (support p).sum fun m => C (p.coeff m) * (X + C a) ^ m

/-- The computable Taylor shift matches `Polynomial.taylor` under `toPoly`.
@isnad1 id=eq.0h3v.s7.62d70a8f74c1 from=translated src=- shape=b67ed651 vocab=db4cf57d
-/
theorem taylor_toPoly [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (a : R) (p : CPolynomial R) :
    (taylor a p).toPoly = Polynomial.taylor a p.toPoly := by
  unfold taylor
  rw [toPoly_sum, Polynomial.taylor_apply, Polynomial.comp, Polynomial.eval₂_eq_sum,
    Polynomial.sum, ← support_toPoly]
  apply Finset.sum_congr rfl
  intro m _
  rw [toPoly_mul, toPoly_pow, toPoly_add, C_toPoly, X_toPoly, C_toPoly, coeff_toPoly]

/-- The Taylor shift of zero is zero.
@isnad1 id=eq.0h2v.s6.6a7951dec62b from=translated src=- shape=d5691dee vocab=f28741cb
-/
theorem taylor_zero [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (a : R) : taylor a (0 : CPolynomial R) = 0 := by
  unfold taylor
  rw [(support_empty_iff 0).mpr rfl, Finset.sum_empty]

/-- The constant coefficient of the Taylor shift is evaluation at the shift point.
@isnad1 id=eq.0h3v.s5.37451cbb4bf2 from=translated src=- shape=1f031930 vocab=1be13ad9
-/
theorem taylor_coeff_zero [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] [DecidableEq R]
    (a : R) (p : CPolynomial R) : coeff (taylor a p) 0 = eval a p := by
  rw [coeff_toPoly, taylor_toPoly, Polynomial.taylor_coeff_zero, eval_toPoly]

end CPolynomial

end CompPoly
