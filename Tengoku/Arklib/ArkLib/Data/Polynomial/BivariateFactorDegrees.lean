/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jieyi Long, Quang Dao
-/
module

public import Tengoku
public import Tengoku.Seed.RingTheory.Polynomial.UniqueFactorization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Degree sums for bivariate factors

The sum of either axis degree over distinct normalized factors of a nonzero polynomial is
bounded by the corresponding degree of that polynomial. Here `R[X][Y]` has outer variable `Y`:
`natDegree` measures `Y`, whereas `degreeX` measures the coefficient variable `X`.
The bounds also hold after selecting any subset of the distinct factors.

The finite-product lemmas work over an integral domain. The normalized-factor bounds additionally
require normalization and unique factorization for the bivariate polynomial ring.

## Implementation references

Adapted from Jieyi Long (`jieyilong`), `BCHKSUniversalFactorSums.lean`, lines 15–123, and
`BCHKSFactorPigeon.lean`, lines 277–302, in the Apache-2.0 licensed better-codes development:
https://github.com/proximity-prize/proximity-prize/blob/19bc7d3e21b2261257e1961acd720b2c395d87e1/ProximityPrize/SubmissionLower/BCHKSUniversalFactorSums.lean

Changes: use the existing CompPoly degree API, generalize finite products to indexed families,
weaken field assumptions to domain and factorization assumptions, and generalize the
positive-degree filter to an arbitrary subset. No donor `LocalMathlib` modules are copied.
-/

@[expose] public section

open Polynomial
open scoped Polynomial.Bivariate

namespace Polynomial.Bivariate

noncomputable section

variable {R : Type*} [CommRing R] [IsDomain R]

variable [DecidableEq R] [NormalizationMonoid R[X][Y]] [UniqueFactorizationMonoid R[X][Y]]

omit [IsDomain R] in
/-- The product of the distinct normalized factors divides the original nonzero polynomial.-/
theorem normalizedFactors_toFinset_prod_dvd (p : R[X][Y]) (hp : p ≠ 0) :
    (UniqueFactorizationMonoid.normalizedFactors p).toFinset.prod id ∣ p := by
  classical
  exact (Multiset.toFinset_prod_dvd_prod _).trans
    (UniqueFactorizationMonoid.prod_normalizedFactors hp).dvd

end

end Polynomial.Bivariate
