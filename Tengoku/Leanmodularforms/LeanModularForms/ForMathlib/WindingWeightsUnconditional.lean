/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tengoku
import Tengoku.Leanmodularforms.LeanModularForms.ForMathlib.ArcFTCLimit
import Tengoku.Leanmodularforms.LeanModularForms.ForMathlib.WindingWeightProofs

/-!
# Unconditional Winding Weights Assembly

Computes the generalized winding number at `i` on the fundamental-domain boundary from
a `SingleCrossingData` with FTC limit `-(πi)`.

## Main results

* `hasWindingNumber_atI_of_scd` — winding number at `i` is `-1/2`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

/-- Winding number at `i` is `-1/2` from `SingleCrossingData` with limit `-(πi)`.
@isnad1 id=hasgener.1h4v.s6.f9ab330e9643 from=translated src=- shape=f7d67e71 vocab=590690c7
-/
theorem hasWindingNumber_atI_of_scd
    {γ : PiecewiseC1Path x y} (D : SingleCrossingData γ I)
    (hL : D.L = -(↑Real.pi * I)) :
    HasGeneralizedWindingNumber γ I (-1/2) := by
  convert D.hasWindingNumber using 1
  rw [hL]
  field_simp [ofReal_ne_zero.mpr Real.pi_ne_zero]

end
