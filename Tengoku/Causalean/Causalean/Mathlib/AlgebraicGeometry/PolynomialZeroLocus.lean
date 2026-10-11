/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Tengoku

/-!
# Zero loci of real multivariate polynomials

This file defines real zero loci and records their behavior under finite products of
multivariate polynomials.
-/

@[expose] public section

open scoped BigOperators

namespace Causalean.Mathlib.AlgebraicGeometry

variable {σ κ : Type*}

/-- For [a real multivariate polynomial](hyp:p), its [real zero locus](goal) is the set of real
assignments at which the polynomial evaluates to zero. -/
def mvPolynomialZeroLocus (p : MvPolynomial σ ℝ) : Set (σ → ℝ) :=
  {x | MvPolynomial.eval x p = 0}

/-- For [a finite set of polynomial indices](hyp:s) and [an indexed family of real multivariate
polynomials](hyp:p), the [zero locus of their product equals the union of their zero loci](goal).
@isnad1 id=eq.0h4v.s6.ba501c563ab2 from=translated src=- shape=c8f5fc46 vocab=1544b338
-/
theorem mvPolynomialZeroLocus_finset_prod
    (s : Finset κ) (p : κ → MvPolynomial σ ℝ) :
    mvPolynomialZeroLocus (∏ i ∈ s, p i) =
      ⋃ i ∈ s, mvPolynomialZeroLocus (p i) := by
  ext x
  simp only [mvPolynomialZeroLocus, Set.mem_ofPred_eq, MvPolynomial.eval_prod,
    Finset.prod_eq_zero_iff]
  simp

/-- For [a finite index set](hyp:s) and [an indexed family of real multivariate
polynomials](hyp:p), if [every indexed factor is nonzero](hyp:h), then [their finite product is
nonzero](goal).
@isnad1 id=ne.1h4v.s7.41bc23f8021d from=translated src=- shape=2ed312aa vocab=215a5169
-/
theorem mvPolynomial_finset_prod_ne_zero
    (s : Finset κ) (p : κ → MvPolynomial σ ℝ)
    (h : ∀ i ∈ s, p i ≠ 0) :
    (∏ i ∈ s, p i) ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr h

/-- For [a finite-type-indexed family of real multivariate polynomials](hyp:p), the [zero locus
of the product over all indices equals the union of all factor zero loci](goal).
@isnad1 id=eq.0h3v.s6.b303300d8f19 from=translated src=- shape=4ec22951 vocab=a1b7db76
-/
theorem mvPolynomialZeroLocus_fintype_prod [Fintype κ]
    (p : κ → MvPolynomial σ ℝ) :
    mvPolynomialZeroLocus (∏ i, p i) = ⋃ i, mvPolynomialZeroLocus (p i) := by
  simpa using mvPolynomialZeroLocus_finset_prod (Finset.univ) p

/-- For [a finite-type-indexed family of real multivariate polynomials](hyp:p), if [every member
is nonzero](hyp:h), then [the product over the whole index type is nonzero](goal).
@isnad1 id=ne.1h3v.s7.d22d21c6db25 from=translated src=- shape=8edd3d15 vocab=9238c3e3
-/
theorem mvPolynomial_fintype_prod_ne_zero [Fintype κ]
    (p : κ → MvPolynomial σ ℝ) (h : ∀ i, p i ≠ 0) :
    (∏ i, p i) ≠ 0 := by
  apply mvPolynomial_finset_prod_ne_zero Finset.univ p
  simpa using h

/-- Given [a finite set of indices](hyp:s) and [a polynomial for every member of its finite
subtype](hyp:p), the [zero locus of the subtype product equals the union of the subtype-indexed
zero loci](goal).
@isnad1 id=eq.0h4v.s7.48ce50a94c79 from=translated src=- shape=13a069a0 vocab=16e87d23
-/
theorem mvPolynomialZeroLocus_subtype_prod
    (s : Finset κ) (p : {i // i ∈ s} → MvPolynomial σ ℝ) :
    mvPolynomialZeroLocus (∏ i, p i) = ⋃ i, mvPolynomialZeroLocus (p i) := by
  exact mvPolynomialZeroLocus_fintype_prod p

/-- Given [a finite set of indices](hyp:s), [a polynomial for every member of its finite
subtype](hyp:p), and [a proof that every factor is nonzero](hyp:h), the [product of the
subtype-indexed factors is nonzero](goal).
@isnad1 id=ne.1h4v.s7.1d48a1abbc15 from=translated src=- shape=5d8c6a07 vocab=b45b5d6d
-/
theorem mvPolynomial_subtype_prod_ne_zero
    (s : Finset κ) (p : {i // i ∈ s} → MvPolynomial σ ℝ)
    (h : ∀ i, p i ≠ 0) :
    (∏ i, p i) ≠ 0 := by
  exact mvPolynomial_fintype_prod_ne_zero p h

end Causalean.Mathlib.AlgebraicGeometry
