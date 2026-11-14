import Tengoku.Twinprime.TwinPrime.Analytic.LFunctionGrowth
import Tengoku.Seed.Analysis.Complex.JensenFormula

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A uniform local zero-count bound for primitive Dirichlet L-functions

Jensen's inequality compares the disks of radii `5/4` and `3/2` around
any point on `Re(s)=2`. The center lower bound and circle growth bound
are proved independently. Zeros are counted with their analytic multiplicity.
-/

noncomputable section

open Metric MeromorphicOn

namespace TwinPrime.Analytic

/--
@isnad1 id=le.1h1v.s6.8cce9215e37e from=translated src=- shape=e5c25e48 vocab=ec4916d8
-/
theorem primitive_character_interval_constant_le_sq (q : ℕ) (hq : 1 < q) :
    Real.sqrt q * (1 + Real.log q) ≤ (q : ℝ) ^ 2 := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hl : 1 + Real.log (q : ℝ) ≤ q := by
    have h := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < q)
    linarith
  have hlog := Real.log_natCast_nonneg q
  calc
    _ ≤ (q : ℝ) * q := mul_le_mul (Real.sqrt_le_self_iff.mpr (Or.inr hq1)) hl
      (by positivity) (by positivity)
    _ = _ := by ring

/--
@isnad1 id=le.1h2v.s7.3e622b603f42 from=translated src=- shape=2547887b vocab=9987cec7
-/
theorem primitiveLFunctionGrowthBudget_half_le (q : ℕ) (hq : 1 < q) (s : ℂ) :
    primitiveLFunctionGrowthBudget q (1 / 2) (‖s‖ + 3 / 2) ≤
      4 * (q : ℝ) ^ 2 * (‖s‖ + 2) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hq2 : (1 : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith
  have hn := norm_nonneg s
  unfold primitiveLFunctionGrowthBudget
  calc
    _ ≤ 1 + (q : ℝ) ^ 2 * (1 + (‖s‖ + 3 / 2) / (1 / 2)) := by
      gcongr
      exact primitive_character_interval_constant_le_sq q hq
    _ ≤ _ := by nlinarith [mul_nonneg (sq_nonneg (q : ℝ)) hn]

/-- The divisor sum counts all zeros in the closed disk, with multiplicity.
The right side has explicit logarithmic conductor and height dependence.
@isnad1 id=le.3h3v.s8.80a02c937e23 from=translated src=- shape=9bc3db5e vocab=6693fb34
-/
theorem sum_divisor_LFunction_le_log_conductor_height {q : ℕ} [NeZero q]
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (s : ℂ) (hs : s.re = 2) :
    (((∑ᶠ u, divisor (DirichletCharacter.LFunction χ) (closedBall s (5 / 4)) u) : ℤ) : ℝ) ≤
      (Real.log 16 + 2 * Real.log q + Real.log (‖s‖ + 2)) / Real.log (6 / 5) := by
  let M := primitiveLFunctionGrowthBudget q (1 / 2) (‖s‖ + 3 / 2)
  have hM : 1 ≤ M := by
    have hlog := Real.log_natCast_nonneg q
    have hn := norm_nonneg s
    dsimp [M, primitiveLFunctionGrowthBudget]
    exact le_add_of_nonneg_right (by positivity)
  have hc : 1 / 4 ≤ ‖DirichletCharacter.LFunction χ s‖ :=
    one_quarter_le_norm_LFunction χ s (by rw [hs])
  have hcpos : 0 < ‖DirichletCharacter.LFunction χ s‖ := by linarith
  have han : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) (closedBall s |(3 / 2 : ℝ)|) :=
    fun z _ => (DirichletCharacter.differentiable_LFunction
      (primitive_character_ne_one hq χ hχ)).analyticAt z
  have hcircle : ∀ z ∈ sphere s |(3 / 2 : ℝ)|, ‖DirichletCharacter.LFunction χ z‖ ≤ M := by
    intro z hz
    have h := norm_LFunction_le_on_closedBall hq χ hχ s (3 / 2) (by rw [hs]; norm_num) z
      (sphere_subset_closedBall (by simpa only [abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)] using hz))
    simpa only [hs, show (2 : ℝ) - 3 / 2 = 1 / 2 by norm_num] using h
  have hj := han.sum_divisor_le (r := (5 / 4 : ℝ)) (R := (3 / 2 : ℝ))
    (by norm_num) (by norm_num) hM (norm_pos_iff.mp hcpos) hcircle
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 5 / 4)] at hj
  norm_num at hj
  apply hj.trans
  apply div_le_div_of_nonneg_right _ (Real.log_nonneg (by norm_num))
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hH : 0 < ‖s‖ + 2 := by positivity
  have hratio : M / ‖DirichletCharacter.LFunction χ s‖ ≤
      16 * (q : ℝ) ^ 2 * (‖s‖ + 2) := by
    calc
      _ ≤ M / (1 / 4) := div_le_div_of_nonneg_left (by linarith) (by norm_num) hc
      _ ≤ (4 * (q : ℝ) ^ 2 * (‖s‖ + 2)) / (1 / 4) :=
        div_le_div_of_nonneg_right (primitiveLFunctionGrowthBudget_half_le q hq s) (by norm_num)
      _ = _ := by ring
  calc
    _ ≤ Real.log (16 * (q : ℝ) ^ 2 * (‖s‖ + 2)) :=
      Real.log_le_log (div_pos (by linarith) hcpos) hratio
    _ = _ := by
      rw [Real.log_mul (by positivity) hH.ne',
        Real.log_mul (by norm_num) (pow_ne_zero 2 hq0.ne'), Real.log_pow]
      norm_num

end TwinPrime.Analytic
