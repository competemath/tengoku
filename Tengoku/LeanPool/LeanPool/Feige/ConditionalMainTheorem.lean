/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
module

public import Tengoku.LeanPool.LeanPool.Feige.GeometryBridge
public import Tengoku.LeanPool.LeanPool.Feige.Sharpness

/-!
# Conditional assembly of the unit-slack theorem

This module states the `δ = 1` specialization of the paper's main result in
terms of three structural inputs.  The reduction and extremal construction
are fully discharged: Theorem 2.1, the simplex/exponential identification
of (2.1), and the `α = 0` centroid-halfspace inequality are the only inputs.
-/

@[expose] public section

namespace Feige

/-- The `δ = 1` specialization of Theorem 1.1, assembled from Theorem 2.1
and the two geometric facts identifying and bounding the Dirichlet
statistic.
@isnad1 id=isoptima.3h1v.s4.e3af5d424972 from=translated src=- shape=5b820a20 vocab=38cad33f
-/
theorem sharp_unit_slack_feige_of_paper_inputs
    {n : ℕ}
    (hcal : UniversalCalibration
      (dirichletK : (Fin n → ℝ) → ℝ))
    (hid : SimplexExponentialIdentification n)
    (hcentroid : SimplexCentroidHalfspaceProperty (ι := Fin n)) :
    IsOptimalFixedDimensionalFeigeBound n (sharpConstant n) := by
  exact sharpConstant_is_optimal_of_structural_inputs
    (dirichletK : (Fin n → ℝ) → ℝ) hcal
    (dirichletK_largeSumBridge_of_simplex hid hcentroid)

end Feige
