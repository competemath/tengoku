import Tengoku.NavierStokesEuler.Euler.SobolevHeat
import Tengoku

/-! Jointly continuous positive-time heat kernels with an explicit integrable parabolic bound. -/

noncomputable section

namespace EulerSobolevHeat

open EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerGaussianCylinderHeat MeasureTheory Set Metric
open intervalIntegral
open scoped Topology NNReal

variable (period : ℝ) [Fact (0 < period)]

/-- A local name for the inherited Sobolev normed group avoids repeated subtype-instance expansion. -/
local instance sobolevNormedGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace period q) := inferInstance

/-- A local name for the inherited Sobolev scalar structure. -/
local instance sobolevNormedSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace period q) := inferInstance

/-- The ordinary Sobolev heat flow is a contraction in its input field. -/
theorem heatOperator_dist_le {q : ℕ} (v : ℝ≥0) (u z : SobolevSpace period q) :
    dist (heatOperator period q v u) (heatOperator period q v z) ≤ dist u z := by
  rw [dist_eq_norm, ← map_sub, dist_eq_norm]
  exact heatOperator_bound period v (u - z)

/-- Strong continuity and contraction imply joint continuity of the actual Sobolev heat flow. -/
theorem heatOperator_joint_continuous (q : ℕ) :
    Continuous (fun p : ℝ≥0 × SobolevSpace period q => heatOperator period q p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := (Metric.continuousAt_iff.mp (heatOperator_continuous period p.2).continuousAt)
    (ε / 2) (by linarith)
  refine ⟨min δ (ε / 2), lt_min hδ (by linarith), ?_⟩
  intro z hz
  have ht : dist z.1 p.1 < δ := (show dist z.1 p.1 ≤ dist z p from le_max_left _ _).trans_lt (lt_min_iff.mp hz).1
  have hf : dist z.2 p.2 < ε / 2 := (show dist z.2 p.2 ≤ dist z p from le_max_right _ _).trans_lt (lt_min_iff.mp hz).2
  have h := dist_triangle (heatOperator period q z.1 z.2) (heatOperator period q z.1 p.2)
    (heatOperator period q p.1 p.2)
  have h1 := heatOperator_dist_le period z.1 z.2 p.2
  have h2 := hd ht
  linarith

/-- The scalar coefficient multiplying the inverse square root in the heat-kernel bound. -/
def parabolicConstant (ν : ℝ) : ℝ := gaussianAbsMoment 1 / Real.sqrt (2 * ν)

/-- The explicit integrable majorant for one-derivative heat smoothing. -/
def parabolicKernelBound (ν t : ℝ) : ℝ := 1 + parabolicConstant ν * t ^ (-(1 / 2 : ℝ))

/-- The scalar parabolic majorant is nonnegative on positive times. -/
theorem parabolicKernelBound_nonneg (ν t : ℝ) (ht : 0 < t) : 0 ≤ parabolicKernelBound ν t := by
  unfold parabolicKernelBound parabolicConstant
  have hm := gaussianAbsMoment_nonneg 1
  positivity

/-- The scalar heat majorant is genuinely integrable at time zero. -/
theorem parabolicKernelBound_integrable (ν T : ℝ) (hT : 0 ≤ T) :
    IntegrableOn (parabolicKernelBound ν) (Ioc 0 T) := by
  have hr : IntervalIntegrable (fun t : ℝ => t ^ (-(1 / 2 : ℝ))) volume 0 T :=
    intervalIntegrable_rpow' (by norm_num)
  have h : IntervalIntegrable (parabolicKernelBound ν) volume 0 T :=
    intervalIntegrable_const.add (hr.const_mul (parabolicConstant ν))
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp h

/-- The exact kernel mass is T plus the square-root parabolic contribution. -/
theorem parabolicKernelBound_integral (ν T : ℝ) (hT : 0 ≤ T) :
    (∫ t in Ioc 0 T, parabolicKernelBound ν t) = T + 2 * parabolicConstant ν * Real.sqrt T := by
  rw [← intervalIntegral.integral_of_le hT]
  unfold parabolicKernelBound
  rw [intervalIntegral.integral_add intervalIntegrable_const
    ((intervalIntegrable_rpow' (by norm_num : -1 < -(1 / 2 : ℝ))).const_mul (parabolicConstant ν)),
    intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by norm_num : -1 < -(1 / 2 : ℝ)))]
  norm_num
  rw [← Real.sqrt_eq_rpow]
  ring

end EulerSobolevHeat
