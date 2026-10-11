/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# The law of `‖P z‖²` for an orthogonal projection `P` is `χ²_{rank P}`

Let `E` be a finite-dimensional real inner-product space and let `P : E →L[ℝ] E`
be an *orthogonal projection*, i.e. self-adjoint (`IsSelfAdjoint P`) and idempotent
(`P ∘L P = P`).  If `z` is a standard Gaussian on `E`, then `‖P z‖²` is distributed
as `χ²_r` where `r = rank P = finrank ℝ (range P)`:

  `(stdGaussian E).map (fun z => ‖P z‖ ^ 2) = chiSqDist (finrank ℝ (range P))`.

## Proof outline

Let `S := LinearMap.range P`, a finite-dimensional inner-product subspace of `E`,
and fix a linear isometry `ι : S ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r)` with
`r = finrank ℝ S` (the standard orthonormal basis of `S`).  Corestrict `P` to a
continuous linear map `Pc : E →L[ℝ] S` and set `Q := ι ∘L Pc : E → EuclideanSpace`.

1. `Q` is a *coisometry*: `Q.adjoint` is an isometric embedding, equivalently
   `⟪Q.adjoint s, Q.adjoint t⟫_E = ⟪s, t⟫`.  The crux is that the adjoint of the
   corestriction `Pc` is the subspace inclusion (uses self-adjoint + idempotent +
   `P w = w` for `w ∈ range P`).
2. Hence `(stdGaussian E).map Q` is a centered Gaussian with covariance the inner
   product, so it equals `stdGaussian (EuclideanSpace ℝ (Fin r))`
   (`Measure.ext_of_charFun`, mirroring `stdGaussian_map_linearIsometryEquiv`).
3. `‖Q z‖ = ‖P z‖` (`ι` is an isometry and corestriction preserves the norm), and
   the law of `‖·‖²` under `stdGaussian (EuclideanSpace ℝ (Fin r))` is `chiSqDist r`
   by `stdGaussian_map_normSq`.

Main result: `stdGaussian_map_normSq_orthogonalProjection`.
-/

module
public import Tengoku.Causalean.Causalean.Stat.CLT.ChiSquared

/-! # Chi-Squared Law for Projected Gaussians

This file proves that the squared norm of an orthogonal projection of a standard
finite-dimensional Gaussian vector has a chi-squared distribution. The degrees of
freedom are the dimension of the projection range.

The public theorem is `stdGaussian_map_normSq_orthogonalProjection`: if a
continuous linear map `P` is self-adjoint and idempotent, then the law of
`‖P z‖²` under `stdGaussian` is `chiSqDist` with degrees of freedom
`finrank ℝ (range P)`. -/

public section

open MeasureTheory ProbabilityTheory Complex Causalean.Mathlib
open scoped RealInnerProductSpace

namespace Causalean.Stat

local notation "stdGaussian" => Causalean.Mathlib.stdGaussian
local notation "covarianceBilin_stdGaussian" =>
  Causalean.Mathlib.covarianceBilin_stdGaussian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end Causalean.Stat
