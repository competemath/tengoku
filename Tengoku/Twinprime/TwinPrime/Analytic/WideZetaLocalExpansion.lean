import Tengoku.Twinprime.TwinPrime.Analytic.WideLocalLogDerivativeExpansion
import Tengoku.Twinprime.TwinPrime.Analytic.ZetaLocalExpansion

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Regularized zeta zero expansions on radius 17/16

The expansion uses the actual zeros of the entire regularization `Z` on
radius `5/4`. Its remainder has constant `288` on radius `17/16`. A
companion statement keeps the pole exactly when returning to zeta itself.
-/

noncomputable section

open Metric MeromorphicOn

namespace TwinPrime.Analytic

/-- Jensen counts the actual zeros of the entire regularization on the
closed radius-5/4 disk, with multiplicity and no pole contribution.
@isnad1 id=le.1h1v.s8.8ba92514221c from=translated src=- shape=b962b587 vocab=c3b2b4ff
-/
theorem sum_divisor_regularizedZeta_le_log_height (c : ℂ) (hc : c.re = 2) :
    (((∑ᶠ u, divisor regularizedRiemannZeta (closedBall c (5 / 4)) u) : ℤ) : ℝ) ≤
      (Real.log 16 + 2 * Real.log (‖c‖ + 2)) / Real.log (6 / 5) := by
  let M : ℝ := 4 * (‖c‖ + 2) ^ 2
  have hn := norm_nonneg c
  have hM : 1 ≤ M := by dsimp [M]; nlinarith [sq_nonneg ‖c‖]
  have hcenter := one_quarter_le_norm_regularizedRiemannZeta_center c hc
  have hcenter0 : 0 < ‖regularizedRiemannZeta c‖ := by linarith
  have hf : AnalyticOnNhd ℂ regularizedRiemannZeta (closedBall c |(3 / 2 : ℝ)|) :=
    fun w _ => differentiable_regularizedRiemannZeta.analyticAt w
  have hbound : ∀ w ∈ sphere c |(3 / 2 : ℝ)|, ‖regularizedRiemannZeta w‖ ≤ M := by
    intro w hw
    have ht := norm_regularizedRiemannZeta_le_on_closedBall c (3 / 2)
      (by rw [hc]; norm_num) w (sphere_subset_closedBall
        (by simpa only [abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)] using hw))
    have ht' : ‖regularizedRiemannZeta w‖ ≤
        regularizedZetaGrowthBudget (1 / 2) (‖c‖ + 3 / 2) := by
      simpa only [hc, show (2 : ℝ) - 3 / 2 = 1 / 2 by norm_num] using ht
    exact ht'.trans (regularizedZetaGrowthBudget_half_le c)
  have hj := hf.sum_divisor_le (r := (5 / 4 : ℝ)) (R := (3 / 2 : ℝ))
    (by norm_num) (by norm_num) hM (norm_pos_iff.mp hcenter0) hbound
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 5 / 4)] at hj
  norm_num at hj
  apply hj.trans
  apply div_le_div_of_nonneg_right _ (Real.log_nonneg (by norm_num))
  have hratio : M / ‖regularizedRiemannZeta c‖ ≤ 16 * (‖c‖ + 2) ^ 2 := by
    calc
      _ ≤ M / (1 / 4) := div_le_div_of_nonneg_left (by linarith) (by norm_num) hcenter
      _ = _ := by dsimp [M]; ring
  have hH : 0 < ‖c‖ + 2 := by positivity
  calc
    _ ≤ Real.log (16 * (‖c‖ + 2) ^ 2) :=
      Real.log_le_log (div_pos (by linarith) hcenter0) hratio
    _ = _ := by
      rw [Real.log_mul (by norm_num) (pow_ne_zero 2 hH.ne'), Real.log_pow]
      norm_num

end TwinPrime.Analytic
