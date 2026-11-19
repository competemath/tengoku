/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.OddSchwartzAntiderivative
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.PVFourier

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Fourier transform of the canonical principal-value distribution

This file closes the final uniqueness step in the Fourier characterization of
`p.v. (1 / x)`.  The analytic distribution identities are proved in
`PVFourier`; the required one-dimensional Schwartz antiderivative theorem is
proved in `OddSchwartzAntiderivative`.
-/

open MeasureTheory FourierTransform
open scoped SchwartzMap

namespace QuadraticCarleson

/-- With Mathlib's Fourier-transform normalization,
`𝓕 (p.v. (1 / x)) = -π i sign`.
@isnad1 id=eq.0h0v.s8.214325ce551f from=translated src=- shape=9a1d1880 vocab=f5ab97d2
-/
theorem fourier_principalValueOneDiv :
    𝓕 principalValueOneDiv =
      (-((Real.pi : ℂ) * Complex.I)) • signTemperedDistribution :=
  fourier_principalValueOneDiv_of_odd_schwartz_antiderivatives
    exists_schwartz_antiderivative_of_odd

/-- The direct symmetric-limit construction of `p.v. (1 / x)` agrees with
the equivalent inverse-Fourier construction.
@isnad1 id=eq.0h0v.s5.bb1697a51d73 from=translated src=- shape=9094f7d5 vocab=b5cd9d12
-/
theorem principalValueOneDiv_eq_FourierCandidate :
    principalValueOneDiv = principalValueOneDivFourierCandidate :=
  principalValueOneDiv_eq_FourierCandidate_of_odd_schwartz_antiderivatives
    exists_schwartz_antiderivative_of_odd

end QuadraticCarleson
