import Tengoku.OpenaiMath.OAI.MathematicalPhysics.CriticalSK.DisorderTransfer
import Tengoku.OpenaiMath.OAI.MathematicalPhysics.CriticalSK.OrientationLimits

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

open scoped ENNReal NNReal

open scoped BigOperators NNReal

open scoped BigOperators

open scoped BigOperators InnerProductSpace

open Module

open Matrix Polynomial

open scoped BigOperators Topology

open Filter

open scoped BigOperators NNReal ENNReal Topology Pointwise Matrix.Norms.Elementwise

open Set Metric MeasureTheory MeasureTheory.Measure

open scoped ENNReal NNReal BigOperators

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric

open scoped NNReal ENNReal BigOperators

open scoped NNReal ENNReal

open ProbabilityTheory

open Metric Set MeasureTheory

open scoped ENNReal Pointwise

open MeasureTheory Filter Set Real

open Finset Real

open scoped BigOperators ENNReal Topology

open Set MeasureTheory

open scoped BigOperators ENNReal

open MeasureTheory

open Finset Real Filter

open scoped Topology

namespace CriticalSK

section

lemma gaussian_inverse_sqrt_bound {s v : ℝ} (hs : 0 < s) (hv : 1/(2*s) ≤ v) :
    (Real.sqrt (2*Real.pi*v))⁻¹ ≤ Real.sqrt s := by
  have hv0 : 0 < v := (by positivity : (0:ℝ) < 1/(2*s)).trans_le hv
  have hp : 1 ≤ Real.pi := by linarith [Real.two_le_pi]
  have hprod : 1 ≤ 2*Real.pi*v*s := by
    have hh := (div_le_iff₀ (by positivity : (0:ℝ) < 2*s)).mp hv
    have hhs : 0 ≤ 2*v*s := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hp hhs]
  have hr : 1 ≤ Real.sqrt (2*Real.pi*v)*Real.sqrt s := by
    rw [← Real.sqrt_mul (by positivity)]
    simpa using Real.sqrt_le_sqrt hprod
  rw [inv_eq_one_div,div_le_iff₀ (Real.sqrt_pos.mpr (by positivity))]
  nlinarith

open Set MeasureTheory Filter

def naturalSmallBallConstant (L : ℝ) : ℝ := 4*Real.sqrt L*Real.exp (6*(L*Real.sqrt L))

end

open Set MeasureTheory Filter

instance disorderLaw_probability (n : ℕ) : IsProbabilityMeasure (disorderLaw n) := by
  unfold disorderLaw
  infer_instance

lemma naturalSmallBallConstant_pos {L : ℝ} (hL : 0 < L) : 0 < naturalSmallBallConstant L := by
  unfold naturalSmallBallConstant
  positivity

lemma exists_spectral_failure_parameter {α : ℝ} (hα : 0 < α) :
    ∃ h : ℝ, 0 ≤ h ∧ 32*Real.exp (-h^2) < α := by
  have hh : Tendsto (fun h : ℝ => -h^2) atTop atBot :=
    tendsto_neg_atTop_atBot.comp (tendsto_pow_atTop (by norm_num : 2 ≠ 0))
  have ht : Tendsto (fun h : ℝ => 32*Real.exp (-h^2)) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_atBot.comp hh).const_mul 32
  exact ((eventually_ge_atTop 0).and (ht.eventually (gt_mem_nhds hα))).exists

end CriticalSK

end

end OAI
