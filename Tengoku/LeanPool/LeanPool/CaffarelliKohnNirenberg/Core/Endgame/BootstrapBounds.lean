/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Endgame.Bootstrap
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Endgame.MorreyScaling
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Endgame.SourceComponents

/-! # Numerical bounds for the first Morrey improvement

The constants in Adams' estimate and in lowering the integrability exponent
are retained. This gives a bound determined by the source bounds, not by a
new existential constant chosen after the solution.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.Step3 CKN.Core.Step4

noncomputable section
namespace CKN.Core.Endgame

/-- The order-two Adams coefficient after lowering integrability to three. -/
def bootstrapOrderTwoCoefficient : ℝ≥0∞ :=
  volume (parabolicCylinder 0 0 1) ^ (1 / 3 - 5 / 66 : ℝ) *
    parabolicAdamsPotentialConstant 2 (6 / 5) (25 / 11)

/-- The order-one Adams coefficient after lowering integrability to three. -/
def bootstrapOrderOneCoefficient : ℝ≥0∞ :=
  volume (parabolicCylinder 0 0 1) ^ (1 / 3 - 1 / 18 : ℝ) *
    parabolicAdamsPotentialConstant 1 3 (25 / 6)

/-- The numerical velocity bound determined by the two source bounds. -/
def bootstrapSourceMorreyBound (KF KG : ℝ≥0∞) : ℝ≥0∞ :=
  3000 * (bootstrapOrderTwoCoefficient * KF) +
    900000 * (bootstrapOrderOneCoefficient * KG +
      (bootstrapOrderOneCoefficient * KG + bootstrapOrderOneCoefficient * KG))

/-- Both coefficients and hence the resulting bound are finite. -/
theorem bootstrapSourceMorreyBound_lt_top {KF KG : ℝ≥0∞}
    (hKF : KF < ⊤) (hKG : KG < ⊤) : bootstrapSourceMorreyBound KF KG < ⊤ := by
  have h₂ : bootstrapOrderTwoCoefficient < ⊤ := ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      Integration.volume_parabolicCylinder_lt_top.ne)
    (adams_potential_constant_lt_top (by norm_num) (by norm_num)
      (by norm_num) (by norm_num))
  have h₁ : bootstrapOrderOneCoefficient < ⊤ := ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      Integration.volume_parabolicCylinder_lt_top.ne)
    (adams_potential_constant_lt_top (by norm_num) (by norm_num)
      (by norm_num) (by norm_num))
  unfold bootstrapSourceMorreyBound
  have hF := ENNReal.mul_lt_top h₂ hKF
  have hG := ENNReal.mul_lt_top h₁ hKG
  finiteness

end CKN.Core.Endgame
