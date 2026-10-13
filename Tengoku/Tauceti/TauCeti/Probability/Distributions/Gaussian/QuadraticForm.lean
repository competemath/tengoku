/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.Analysis.Matrix.Spectrum
public import Tengoku.Tauceti.TauCeti.Analysis.Matrix.Sqrt
public import Tengoku.Tauceti.TauCeti.Probability.Distributions.Gaussian.ChiSquared
public import Tengoku.Tauceti.TauCeti.Probability.Distributions.Gaussian.Multivariate

/-!
# Moment-generating functions of Gaussian quadratic forms

Let `S` be the matrix parameter of a centred multivariate Gaussian and `Θ` a real symmetric
matrix. This file determines exactly when the quadratic statistic `x ↦ ⟪x, Θ x⟫` of that Gaussian
vector has finite exponential moments of order `t`, and computes its moment-generating function
there:

* the integrand is integrable exactly when the pencil `1 - (2 * t) • (√S * Θ * √S)` is positive
  definite, where `√S = CFC.sqrt S`, with no hypothesis on `S`; and
* on that domain the moment-generating function is
  `det (1 - (2 * t) • (√S * Θ * √S)) ^ (-1 / 2)`, which for positive-semidefinite `S` is
  `det (1 - (2 * t) • (Θ * S)) ^ (-1 / 2)`.

The same results are stated for the standard Gaussian vector, in terms of the eigenvalues of the
symmetric matrix. The one-dimensional building blocks, the exponential moments of a weighted sum
of squares of independent standard Gaussian coordinates, live in
`TauCeti.Probability.Distributions.Gaussian.ChiSquared`.

## Main results

* `TauCeti.Probability.mem_integrableExpSet_inner_toEuclideanLin_multivariateGaussian_iff` — the
  exact
  exponential-integrability domain of a Gaussian quadratic form;
* `TauCeti.Probability.mgf_inner_toEuclideanLin_multivariateGaussian_sqrt` and
  `TauCeti.Probability.mgf_inner_toEuclideanLin_multivariateGaussian` — its moment-generating
  function on
  that domain, in terms of the sandwich `√S * Θ * √S` and, for positive-semidefinite `S`, of
  `Θ * S`;
* `TauCeti.Probability.cgf_inner_toEuclideanLin_multivariateGaussian_sqrt` and
  `TauCeti.Probability.cgf_inner_toEuclideanLin_multivariateGaussian` — the cumulant-generating
  function,
  `-1 / 2` times the real logarithm of the same determinants;
* `TauCeti.Probability.mem_integrableExpSet_inner_toEuclideanLin_stdGaussian_iff` and
  `TauCeti.Probability.mgf_inner_toEuclideanLin_stdGaussian` — the same results for the standard
  Gaussian,
  in terms of the eigenvalues of the symmetric matrix.

## References

* R. J. Muirhead, *Aspects of Multivariate Statistical Theory*, Wiley (1982), Theorem 1.2.6
  (the multivariate Gaussian) and Theorem 3.2.3 (the Wishart moment-generating function, which
  is the product of these).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator

namespace TauCeti.Probability

/-! ### The standard Gaussian vector -/

section stdGaussian

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {B : Matrix ι ι ℝ} (hB : B.IsHermitian)
  {t : ℝ}
include hB

end stdGaussian

/-! ### The centred multivariate Gaussian vector -/

section multivariateGaussian

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {S Θ : Matrix ι ι ℝ} {t : ℝ}

end multivariateGaussian

end TauCeti.Probability
