import Tengoku.NavierStokesEuler.Euler.CylinderEndpointBudget
import Tengoku.NavierStokesEuler.Euler.CylinderTerminalAmplitude

/-!
Actual fixed-Hq mixed-word estimates for unit terminal data. The spatial
radius is unchanged; the coordinate/velocity use two shifts and the true
time derivative uses three. Every inverse guard is source-only.
-/

noncomputable section

namespace EulerCylinderDirichlet.Coefficients.EndpointBudget

open Set ContinuousLinearMap InnerProductSpace EulerSmoothLimit
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerLpCylinderRectangular
  EulerTimeLp EulerGevrey EulerParameterWordGevrey EulerFixedEvolutionSobolev
open scoped ContDiff BoundedContinuousFunction

variable (P : ℝ) [Fact (0 < P)] {T : ℝ} {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {D : Coefficients T U E} {ι : Type*} [Fintype ι] {q : ℕ}
  (L : EndpointBudget D ι q) (directions : ι → LiftTangent)
  (hdir : ∀ i, ‖directions i‖ ≤ 1)
  (Y : CylinderL2 P U) (hY : ContDiff ℝ ∞ (fun a : LiftTangent => translate P a Y))
  (d : ℕ) (hYb : ∀ n, block directions q (fun a : LiftTangent => translate P a Y) n 0 ≤ majorant L.R d n)

include hY hYb in
omit [CompleteSpace U] [CompleteSpace E] in
theorem constant_unit_bound (n : ℕ) :
    block directions q (fun a : LiftTangent => pathTranslate P a
      (ContinuousMap.const (Icc (0 : ℝ) T) (T⁻¹ • Y))) n 0 ≤ T⁻¹*majorant L.R d n := by
  have hs := block_smul_le directions q T⁻¹
    (fun a : LiftTangent => pathTranslate P a (ContinuousMap.const (Icc (0 : ℝ) T) Y))
    (constantPath_orbit_contDiff P Y hY) n 0
  rw [abs_of_nonneg (inv_nonneg.mpr D.time_pos.le)] at hs
  have hb := (constantPath_block_le (K := Icc (0 : ℝ) T) P directions q Y hY n 0).trans (hYb n)
  have he : ContinuousMap.const (Icc (0 : ℝ) T) (T⁻¹ • Y) =
      T⁻¹ • ContinuousMap.const (Icc (0 : ℝ) T) Y := rfl
  rw [he]
  simp only [map_smul]
  exact hs.trans (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr D.time_pos.le))

include hdir hY hYb

omit [CompleteSpace U] [CompleteSpace E] in
theorem forcing_unit_bound (n : ℕ) :
    block directions q (fun a : LiftTangent => pathTranslate P a (D.endpointForcing P Y)) n 0 ≤
      endpointForcingCost ι q T L.Rc L.C₁*majorant L.R d n := by
  let Z := ContinuousMap.const (Icc (0 : ℝ) T) (T⁻¹ • Y)
  have hz : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a Z) :=
    endpointConstant_orbit_contDiff P Y hY
  have hp := product_orbit_block_bound P D.Q₁ L.frameDerivative_smooth directions hdir q Z hz
    L.Rc L.C₁ L.R T⁻¹ L.Rc_nonneg L.C₁_nonneg (inv_nonneg.mpr D.time_pos.le)
    L.radius_bounds.2 L.frameDerivative_bound d (L.constant_unit_bound P directions Y hY d hYb) n
  have hs := block_smul_le directions q (2 : ℝ)
    (fun a : LiftTangent => pathTranslate P a (fullMultiplierMap P D.Q₁ Z))
    (product_orbit_contDiff P D.Q₁ L.frameDerivative_smooth Z hz) n 0
  have he : D.endpointForcing P Y = (2 : ℝ) • fullMultiplierMap P D.Q₁ Z := rfl
  rw [he]
  simp only [map_smul]
  apply (hs.trans (mul_le_mul_of_nonneg_left hp (abs_nonneg (2 : ℝ)))).trans_eq
  unfold endpointForcingCost
  norm_num
  ring

end EulerCylinderDirichlet.Coefficients.EndpointBudget
