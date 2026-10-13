/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/
module

public import Tengoku.LeanPool.LeanPool.PoincareThreeBody.DelaunayAnchorChart
public import Tengoku.LeanPool.LeanPool.PoincareThreeBody.EnergyLeafObstruction
public import Tengoku

/-!
# Local energy leaves at the rational anchor

The interior elliptic action region contains a product box around the rational anchor in
energy/first-action coordinates.  Shrinking the first-action side to an interval ensures that
the whole straight energy-leaf segment back to the anchor remains in the region.
-/

@[expose] public section

namespace LeanPool.PoincareThreeBody

open Set

/-- The first action used at the rational anchor. -/
noncomputable def delaunayAnchorFirstAction : ℝ :=
  1 / Real.sqrt 3

theorem energyLeafAction_anchor :
    energyLeafAction (-2) delaunayAnchorFirstAction = delaunayAnchorAction := by
  funext coordinate
  fin_cases coordinate
  · rfl
  · have hsqrtPos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
    have hsqrtSq : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    change -1 / (2 * (1 / Real.sqrt 3) ^ 2) - (-2) = (1 / 2 : ℝ)
    have hsquare : (1 / Real.sqrt 3 : ℝ) ^ 2 = 1 / 3 := by
      field_simp [hsqrtPos.ne']
      exact hsqrtSq.symm
    rw [hsquare]
    norm_num

/-- The straight energy-leaf action is jointly analytic in energy and first action away from
`L = 0`. -/
theorem analyticAt_energyLeafAction_parameters
    {energy firstAction : ℝ} (hfirstAction : firstAction ≠ 0) :
    AnalyticAt ℝ
      (fun parameters : ℝ × ℝ ↦ energyLeafAction parameters.1 parameters.2)
      (energy, firstAction) := by
  rw [analyticAt_pi_iff]
  intro coordinate
  fin_cases coordinate
  · exact analyticAt_snd
  · change AnalyticAt ℝ
      (fun parameters : ℝ × ℝ ↦
        -1 / (2 * parameters.2 ^ 2) - parameters.1) (energy, firstAction)
    have hdenominator : AnalyticAt ℝ
        (fun parameters : ℝ × ℝ ↦ 2 * parameters.2 ^ 2)
        (energy, firstAction) :=
      analyticAt_const.mul (analyticAt_snd.pow 2)
    have hdenominatorNe : 2 * firstAction ^ 2 ≠ 0 := by
      positivity
    exact analyticAt_const.div hdenominator hdenominatorNe |>.sub analyticAt_fst

/-- On the interior part of the anchor chart, angle independence identifies the phase value with
the action-section representative. -/
theorem IsFirstIntegralFamily.delaunayAnchorChart_eq_leadingActionCoefficient
    {δ : ℝ} {F : ℝ → PhaseSpace → ℝ}
    (hδ : 0 < δ) (hanalytic : IsJointlyAnalytic δ F)
    (hfirstIntegral : IsFirstIntegralFamily δ F)
    {parameters : DelaunayAnchorParameters}
    (haction : parameters.1 ∈ ProgradeEllipticActions)
    (hapoapsis : parameters.1 0 ^ 2 *
      (1 + eccentricityFromActions parameters.1) < 1) :
    F 0 (delaunayAnchorChart parameters) =
      leadingActionCoefficient F parameters.1 := by
  have hfirstAction : 0 < parameters.1 0 :=
    haction.1.trans haction.2
  have heccentricity : 0 < eccentricityFromActions parameters.1 :=
    eccentricityFromActions_pos haction
  have heccentricityOne : eccentricityFromActions parameters.1 < 1 :=
    eccentricityFromActions_lt_one haction
  have hvalue :=
    IsFirstIntegralFamily.leadingActionCoefficient_eq_liftedDelaunayPhasePoint
      hδ hanalytic hfirstIntegral hfirstAction heccentricity
      heccentricityOne hapoapsis
      (eccentricMeanAnomaly (eccentricityFromActions parameters.1) parameters.2.1,
        parameters.2.2)
  rw [actions_from_eccentricityFromActions haction] at hvalue
  unfold delaunayAnchorChart
  rw [delaunayActionSectionAtAnomaly_eq_liftedDelaunayPhasePoint haction]
  exact hvalue.symm

/-- The mass-zero Hamiltonian in the anchor chart is the Delaunay Hamiltonian of its action
parameters. -/
theorem hamiltonian_zero_delaunayAnchorChart
    {parameters : DelaunayAnchorParameters}
    (haction : parameters.1 ∈ ProgradeEllipticActions) :
    hamiltonian 0 (delaunayAnchorChart parameters) =
      delaunayHamiltonian parameters.1 := by
  have hfirstAction : parameters.1 0 ≠ 0 :=
    (haction.1.trans haction.2).ne'
  have heccentricity : 0 ≤ eccentricityFromActions parameters.1 :=
    eccentricityFromActions_nonneg parameters.1
  have heccentricityOne : eccentricityFromActions parameters.1 < 1 :=
    eccentricityFromActions_lt_one haction
  unfold delaunayAnchorChart
  rw [delaunayActionSectionAtAnomaly_eq_liftedDelaunayPhasePoint haction,
    hamiltonian_zero_liftedDelaunayPhasePoint hfirstAction heccentricity
      heccentricityOne]
  rw [actions_from_eccentricityFromActions haction]

end LeanPool.PoincareThreeBody
