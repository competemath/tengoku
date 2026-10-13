/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.Probability.Distributions.Gaussian.QuadraticForm
public import Tengoku.Tauceti.TauCeti.Probability.Distributions.Wishart.Basic
public import Tengoku.Tauceti.TauCeti.Probability.Distributions.Wishart.Nonsingular

import Tengoku.Tauceti.TauCeti.Analysis.SpecialFunctions.MultivariateGamma.Divergence
import Tengoku.Tauceti.TauCeti.Analysis.SpecialFunctions.MultivariateGamma.Integral
import Tengoku.Tauceti.TauCeti.LinearAlgebra.Matrix.InvSub
import Tengoku.Tauceti.TauCeti.Probability.Moments.Pi

/-!
# Exponential moments of the Wishart families

A symmetric matrix `Θ` pairs with a Wishart matrix `A` through the real trace statistic
`A ↦ trace (Θ * A)`; by `selfAdjoint.inner_eq_trace_mul` this is the Frobenius inner product of
the symmetric subspace, so it is the pairing that `MeasureTheory.charFun` uses there. This file
determines exactly when that statistic has finite exponential moments under each of the two
Wishart families, and computes its moment- and cumulant-generating functions. Both answers are
governed by one matrix, the pencil `1 - (2 * t) • (√S * Θ * √S)`: at a positive Gaussian-Gram
degree, and for the density family at a positive-definite scale and a degree in the classical
range `p - 1 < n`, the moment is finite exactly when that pencil is positive definite, and there
the transform is a negative half-power of its determinant, with the degree as exponent.
Gaussian-Gram degree zero is the one exception, where the law is a Dirac mass and every order has
a finite moment whether or not the pencil is positive definite.

For the Gaussian-Gram family, writing the law as the image of a product of `ν` centred Gaussian
factors turns the trace statistic into a sum of `ν` independent Gaussian quadratic forms, which
reduces all three answers to the one-factor answers of
`TauCeti.Probability.Distributions.Gaussian.QuadraticForm`. The factors being identically
distributed, the domain of the sum is their common domain; the moment-generating function is the
`ν`-th power of the one-factor one; and the cumulant-generating function is `ν` times the
one-factor one. At degree zero the law is a Dirac mass and the statistic vanishes identically, so
the domain is all of `ℝ` and the transforms are constant; those statements need no hypothesis and
are recorded separately.

For the nonsingular density family the computation is the multivariate Gamma integral instead.
Tilting the density by `exp (t * trace (Θ * A))` replaces the inverse scale `S⁻¹` in its
exponential weight by `S⁻¹ - (2 * t) • Θ`, which is the congruence of the pencil by
`(CFC.sqrt S)⁻¹` and so positive definite exactly when the pencil is. Where it is, the tilted
density is again a Wishart density, at the scale `(S⁻¹ - (2 * t) • Θ)⁻¹`, and the ratio of the
two normalizing constants is the determinant power; where it is not, the cone integral diverges.

## Main results

* `TauCeti.Probability.mem_integrableExpSet_trace_mul_wishartGramMeasure_iff` — at a positive
  degree, the
  exact exponential-integrability domain of the trace statistic;
* `TauCeti.Probability.mgf_trace_mul_wishartGramMeasure_sqrt` and
  `TauCeti.Probability.mgf_trace_mul_wishartGramMeasure` — its moment-generating function on that
  domain, in
  terms of the sandwich `√S * Θ * √S` and, for positive-semidefinite `S`, of `Θ * S`;
* `TauCeti.Probability.cgf_trace_mul_wishartGramMeasure_sqrt` and
  `TauCeti.Probability.cgf_trace_mul_wishartGramMeasure` — the matching cumulant-generating
  functions;
* `TauCeti.Probability.integral_exp_neg_trace_mul_wishartGramMeasure` — the Laplace transform over
  the
  positive-semidefinite cone, the specialization of the moment-generating function to `t = -1`;
* `TauCeti.Probability.mem_integrableExpSet_trace_mul_nonsingularWishartMeasure_iff`,
  `TauCeti.Probability.mgf_trace_mul_nonsingularWishartMeasure` with its sandwich form
  `TauCeti.Probability.mgf_trace_mul_nonsingularWishartMeasure_sqrt`,
  `TauCeti.Probability.cgf_trace_mul_nonsingularWishartMeasure` and
  `TauCeti.Probability.integral_exp_neg_trace_mul_nonsingularWishartMeasure` — the same four results
  for the
  nonsingular density family, with its real degree in place of the natural one.

## References

* R. J. Muirhead, *Aspects of Multivariate Statistical Theory*, Wiley (1982), Theorem 3.2.3.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

open scoped RealInnerProductSpace Matrix MatrixOrder

namespace TauCeti.Probability

variable {p ν : ℕ} {S : Matrix (Fin p) (Fin p) ℝ}
  {Θ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)} {t : ℝ}

/-! ### Degree zero -/

/-- At degree zero the Gaussian-Gram law is a Dirac mass at the origin, so the trace statistic has
finite exponential moments of every order. -/
theorem integrableExpSet_trace_mul_wishartGramMeasure_zero
    (Θ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) (S : Matrix (Fin p) (Fin p) ℝ) :
    integrableExpSet (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace)
      (wishartGramMeasure 0 S) = Set.univ := by
  refine Set.eq_univ_of_forall fun t ↦ ?_
  rw [integrableExpSet, Set.mem_ofPred_eq, wishartGramMeasure_zero]
  exact integrable_dirac' (selfAdjoint.continuous_exp_trace_mul_coe Θ t).stronglyMeasurable
    enorm_lt_top

/-- At degree zero the trace statistic vanishes almost everywhere, so its moment-generating
function is constantly `1`. -/
theorem mgf_trace_mul_wishartGramMeasure_zero
    (Θ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) (S : Matrix (Fin p) (Fin p) ℝ)
    (t : ℝ) :
    mgf (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace)
      (wishartGramMeasure 0 S) t = 1 := by
  rw [mgf, wishartGramMeasure_zero,
    integral_dirac' _ _ (selfAdjoint.continuous_exp_trace_mul_coe Θ t).stronglyMeasurable]
  simp

/-- At degree zero the cumulant-generating function is constantly `0`. -/
theorem cgf_trace_mul_wishartGramMeasure_zero
    (Θ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) (S : Matrix (Fin p) (Fin p) ℝ)
    (t : ℝ) :
    cgf (fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ↦
        ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace)
      (wishartGramMeasure 0 S) t = 0 := by
  rw [cgf, mgf_trace_mul_wishartGramMeasure_zero, Real.log_one]

/-! ### The exponential-integrability domain -/

/-! ### The moment- and cumulant-generating functions -/

/-! ### The Laplace transform on the positive-semidefinite cone -/

/-! ### The nonsingular density family -/

variable {n : ℝ}

/-! #### The exponential-integrability domain -/

/-! #### The moment- and cumulant-generating functions -/

/-! #### The Laplace transform on the positive-semidefinite cone -/

end TauCeti.Probability
