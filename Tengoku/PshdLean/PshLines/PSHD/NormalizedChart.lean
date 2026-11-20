import Tengoku.PshdLean.PshLines.PSHD.ChartGeometry
import Tengoku.Seed.Analysis.Normed.Module.Normalize

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Normalized affine charts

The bounded-chart separation estimate in the energy argument of `pshd-vibe`,
Lemma 1.3, expressed on actual unit vectors.
-/

namespace PshLines.PSHD

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The affine lift above a unit vector has the expected Pythagorean norm.-/
theorem affineLift_norm_sq {e v : E} (he : ‖e‖ = 1)
    (hv : inner ℂ e v = 0) : ‖e + v‖ ^ 2 = 1 + ‖v‖ ^ 2 := by
  rw [norm_add_sq (𝕜 := ℂ), he, hv]
  simp

/-- An affine lift with perpendicular offset cannot vanish.-/
theorem affineLift_ne_zero {e v : E} (he : ‖e‖ = 1)
    (hv : inner ℂ e v = 0) : e + v ≠ 0 := by
  intro h
  have := affineLift_norm_sq he hv
  rw [h, norm_zero] at this
  nlinarith [sq_nonneg ‖v‖]

/-- Hermitian correlation in a normalized affine chart.-/
theorem normalized_affineLift_inner_norm {e v w : E} (he : ‖e‖ = 1)
    (hv : inner ℂ e v = 0) (hw : inner ℂ e w = 0) :
    ‖inner ℂ (NormedSpace.normalize (e + v)) (NormedSpace.normalize (e + w))‖ =
      ‖(1 : ℂ) + inner ℂ v w‖ /
        Real.sqrt ((1 + ‖v‖ ^ 2) * (1 + ‖w‖ ^ 2)) := by
  have hve : inner ℂ v e = 0 := (inner_eq_zero_symm).mpr hv
  have hi : inner ℂ (e + v) (e + w) = 1 + inner ℂ v w := by
    simp [inner_add_left, inner_add_right, hw, hve,
      inner_self_eq_norm_sq_to_K, he]
  have hd : Real.sqrt ((1 + ‖v‖ ^ 2) * (1 + ‖w‖ ^ 2)) =
      ‖e + v‖ * ‖e + w‖ := by
    rw [← affineLift_norm_sq he hv, ← affineLift_norm_sq he hw,
      ← mul_pow, Real.sqrt_sq (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  simp only [NormedSpace.normalize, RCLike.real_smul_eq_coe_smul (K := ℂ),
    inner_smul_left, inner_smul_right, norm_mul, hi, hd]
  simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/-- The normalized chart retains quantitative separation after forgetting phase.-/
theorem normalized_affineLift_correlation_lower_bound {e v w : E}
    (he : ‖e‖ = 1) (hv : inner ℂ e v = 0) (hw : inner ℂ e w = 0)
    (hv1 : ‖v‖ ≤ 1) (hw1 : ‖w‖ ≤ 1) :
    ‖v - w‖ ^ 2 / 4 ≤ 2 - 2 *
      ‖inner ℂ (NormedSpace.normalize (e + v)) (NormedSpace.normalize (e + w))‖ := by
  rw [normalized_affineLift_inner_norm he hv hw]
  exact affineChart_correlation_lower_bound hv1 hw1

/-- Phase choices over a bounded affine chart satisfy a Euclidean quadratic
separation estimate on the radius and chart parameters.-/
theorem normalized_affineLift_annulus_lower_bound {e v w : E}
    (he : ‖e‖ = 1) (hv : inner ℂ e v = 0) (hw : inner ℂ e w = 0)
    (hv1 : ‖v‖ ≤ 1) (hw1 : ‖w‖ ≤ 1)
    {R : ℝ} (hR : 0 ≤ R) {z t : ℂ}
    (hz : R / 2 ≤ ‖z‖) (ht : R / 2 ≤ ‖t‖) :
    (‖z‖ - ‖t‖) ^ 2 + (R ^ 2 / 16) * ‖v - w‖ ^ 2 ≤
      ‖z • NormedSpace.normalize (e + v) -
        t • NormedSpace.normalize (e + w)‖ ^ 2 := by
  have hsep := annulus_complex_smul_lower_bound
    (NormedSpace.norm_normalize (affineLift_ne_zero he hv))
    (NormedSpace.norm_normalize (affineLift_ne_zero he hw)) hR hz ht
  have hc := mul_le_mul_of_nonneg_left
    (normalized_affineLift_correlation_lower_bound he hv hw hv1 hw1)
    (show 0 ≤ R ^ 2 / 4 by positivity)
  nlinarith

/-- A lower Lipschitz estimate for any choice of phases over the bounded
radius--chart parameters, with their maximum product metric.-/
theorem normalized_affineLift_max_lower_bound {e v w : E}
    (he : ‖e‖ = 1) (hv : inner ℂ e v = 0) (hw : inner ℂ e w = 0)
    (hv1 : ‖v‖ ≤ 1) (hw1 : ‖w‖ ≤ 1)
    {R : ℝ} (hR : 0 ≤ R) {z t : ℂ}
    (hz : R / 2 ≤ ‖z‖) (ht : R / 2 ≤ ‖t‖) :
    min 1 (R / 4) * max |‖z‖ - ‖t‖| ‖v - w‖ ≤
      ‖z • NormedSpace.normalize (e + v) -
        t • NormedSpace.normalize (e + w)‖ := by
  have h := normalized_affineLift_annulus_lower_bound he hv hw hv1 hw1 hR hz ht
  let d := ‖z • NormedSpace.normalize (e + v) -
    t • NormedSpace.normalize (e + w)‖
  have hd : 0 ≤ d := norm_nonneg _
  have hrad : |‖z‖ - ‖t‖| ≤ d := by
    have hnon : 0 ≤ (R ^ 2 / 16) * ‖v - w‖ ^ 2 := by positivity
    nlinarith [sq_abs (‖z‖ - ‖t‖), abs_nonneg (‖z‖ - ‖t‖)]
  have hang : R / 4 * ‖v - w‖ ≤ d := by
    have hnon : 0 ≤ R / 4 * ‖v - w‖ := by positivity
    nlinarith [sq_nonneg (‖z‖ - ‖t‖)]
  rw [mul_max_of_nonneg _ _ (le_min (by norm_num) (by positivity))]
  apply max_le
  · calc
      _ ≤ 1 * |‖z‖ - ‖t‖| :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) (abs_nonneg _)
      _ ≤ d := by simpa using hrad
  · exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _)).trans hang

end PshLines.PSHD
