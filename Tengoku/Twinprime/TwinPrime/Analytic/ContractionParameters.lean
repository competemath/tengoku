import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Choosing a fixed contraction parameter

The constants are fixed before the power cutoff is chosen. The limiting
coefficient tends to zero as the cutoff exponent tends to zero; the remaining
inverse-logarithm terms then disappear at infinity.
-/

noncomputable section

open Filter

namespace TwinPrime.Analytic

theorem exists_small_parameter_eventual_contraction (D J : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ᶠ x : ℝ in atTop,
      D * (δ + 2 / Real.log x) ^ 2 / (1 - δ) ^ 6 + J / Real.log x ≤ 1 / 2 := by
  have hcont : ContinuousAt (fun δ : ℝ => D * δ ^ 2 / (1 - δ) ^ 6) 0 := by
    fun_prop (disch := norm_num)
  have hzero : Tendsto (fun δ : ℝ => D * δ ^ 2 / (1 - δ) ^ 6) (nhds 0) (nhds 0) := by
    simpa using hcont.tendsto
  have hinv : Tendsto (fun t : ℝ => 1 / t) atTop (nhds 0) := by
    simpa only [one_div] using (tendsto_inv_atTop_zero : Tendsto (fun t : ℝ => t⁻¹) atTop (nhds 0))
  have hsmall := (hzero.comp hinv).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  obtain ⟨t, htcoef, ht⟩ := (hsmall.and (eventually_gt_atTop (2 : ℝ))).exists
  let δ := 1 / t
  have hδ0 : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ < 1 := by
    dsimp [δ]
    exact (div_lt_one (by linarith : 0 < t)).mpr (by linarith)
  have hδcoef : D * δ ^ 2 / (1 - δ) ^ 6 < 1 / 4 := htcoef
  have hrec : Tendsto (fun x : ℝ => (Real.log x)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have hshift : Tendsto (fun x : ℝ => δ + 2 / Real.log x) atTop (nhds δ) := by
    simpa only [div_eq_mul_inv, mul_zero, add_zero] using
      (tendsto_const_nhds.add (tendsto_const_nhds.mul hrec) :
        Tendsto (fun x : ℝ => δ + 2 * (Real.log x)⁻¹) atTop (nhds (δ + 2 * 0)))
  have hcoef : Tendsto
      (fun x : ℝ => D * (δ + 2 / Real.log x) ^ 2 / (1 - δ) ^ 6 + J / Real.log x)
      atTop (nhds (D * δ ^ 2 / (1 - δ) ^ 6)) := by
    have hfirst : Tendsto (fun x : ℝ => D * (δ + 2 / Real.log x) ^ 2 / (1 - δ) ^ 6)
        atTop (nhds (D * δ ^ 2 / (1 - δ) ^ 6)) :=
      (tendsto_const_nhds.mul (hshift.pow 2)).div_const ((1 - δ) ^ 6)
    have hsecond : Tendsto (fun x : ℝ => J / Real.log x) atTop (nhds 0) := by
      simpa only [div_eq_mul_inv, mul_zero] using tendsto_const_nhds.mul hrec
    simpa only [add_zero] using hfirst.add hsecond
  refine ⟨δ, hδ0, hδ1, ?_⟩
  exact (hcoef.eventually (gt_mem_nhds (by linarith : D * δ ^ 2 / (1 - δ) ^ 6 < 1 / 2))).mono
    (fun _ h => h.le)

end TwinPrime.Analytic
