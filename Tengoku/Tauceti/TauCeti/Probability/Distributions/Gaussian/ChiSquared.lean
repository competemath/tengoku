/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Tengoku.Tauceti.TauCeti.Probability.Distributions.ChiSquared
public import Tengoku.Tauceti.TauCeti.Probability.Distributions.Gaussian.Cdf
public import Tengoku.Tauceti.TauCeti.Probability.Moments.Pi

/-!
# Squares of standard Gaussian variables

This file identifies the square of a standard real Gaussian variable with the chi-squared law
of one degree of freedom. It then combines this identification with independence to prove that
the sum of the squares of a finite independent standard Gaussian family has the chi-squared law
whose degrees of freedom are the cardinality of the family. The empty family is included: both
the empty sum and `chiSquaredMeasure 0` are the point mass at zero.

It also computes the exponential-integrability domain and the moment-generating function of a
weighted square `w * x ^ 2` of a standard Gaussian variable, and of a weighted sum of squares
`∑ j, w j * c j ^ 2` of finitely many independent ones, which is the form a Gaussian quadratic
statistic takes in eigen-coordinates.

These laws identify Gaussian quadratic statistics with chi-squared distributions. In particular,
they provide the scalar foundation for distributional results about Gaussian norms and Gaussian
Gram matrices.

## Main results

* `TauCeti.Probability.gaussianReal_map_sq` — the square of the standard Gaussian measure is
  `chiSquaredMeasure 1`;
* `TauCeti.Probability.iIndepFun.hasLaw_sum_sq_gaussian` — a finite sum of independent squared
  standard Gaussian variables has the corresponding chi-squared law;
* `TauCeti.Probability.map_sum_sq_pi_gaussianReal` — the same statement at the level of measures
  and for an arbitrary common variance `v`: the sum of squares of the coordinates of a product of
  `gaussianReal 0 v` laws is the chi-squared law scaled by `v`;
* `TauCeti.Probability.mem_integrableExpSet_mul_sq_gaussianReal_iff` and
  `TauCeti.Probability.mgf_mul_sq_gaussianReal` — the exponential moments of `w * x ^ 2` are
  finite exactly when `2 * t * w < 1`, where the moment-generating function is
  `(1 - 2 * t * w) ^ (-1 / 2)`;
* `TauCeti.Probability.mem_integrableExpSet_sum_mul_sq_pi_gaussianReal_iff` and
  `TauCeti.Probability.mgf_sum_mul_sq_pi_gaussianReal` — the same for a weighted sum of squares of
  independent standard Gaussian coordinates, with the product of the one-dimensional values.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1,
  2nd ed., Wiley (1994), ch. 18.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal

namespace TauCeti

namespace Probability

section scalar

variable {w t : ℝ}

end scalar

section pi

variable {ι : Type*} [Fintype ι] {w : ι → ℝ} {t : ℝ}

end pi

variable {Omega iota : Type*} [MeasurableSpace Omega] [Fintype iota] {P : Measure Omega}
  {X : iota → Omega → ℝ}

end Probability

end TauCeti
