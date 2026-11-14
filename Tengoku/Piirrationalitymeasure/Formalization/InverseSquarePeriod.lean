import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Weighted unit-period estimates used in (6.25). -/

namespace PiIrrationality

open MeasureTheory Set

theorem inverse_square_shift_le {k u : ℝ} (hk : 0 < k) (hu : 0 ≤ u) :
    1 / (k + u) ^ 2 ≤ 1 / k ^ 2 := by
  apply one_div_le_one_div_of_le (sq_pos_of_pos hk)
  nlinarith

theorem inverse_square_shift_abs_sub_le {k u : ℝ} (hk : 0 < k)
    (hu : u ∈ Icc (0 : ℝ) 1) :
    |1 / (k + u) ^ 2 - 1 / k ^ 2| ≤ 2 / k ^ 3 := by
  rw [abs_of_nonpos (sub_nonpos.mpr (inverse_square_shift_le hk hu.1)), neg_sub]
  have hku : 0 < k + u := by linarith [hu.1]
  apply (le_div_iff₀ (pow_pos hk 3)).mpr
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hku)).mp
  field_simp
  nlinarith [mul_nonneg (sq_nonneg k) (sub_nonneg.mpr hu.2),
    mul_nonneg (mul_nonneg hk.le hu.1) (show 0 ≤ 4 - u by linarith [hu.2])]

theorem continuousOn_inverse_square_shift {k : ℝ} (hk : 0 < k) :
    ContinuousOn (fun u : ℝ => 1 / (k + u) ^ 2) (uIcc (0 : ℝ) 1) := by
  apply continuousOn_const.div (by fun_prop)
  intro u hu
  have hu0 : 0 ≤ u := by simpa using (show u ∈ Icc (0 : ℝ) 1 by simpa using hu).1
  exact pow_ne_zero _ (by linarith)

theorem intervalIntegral_abs_mul_le {f w : ℝ → ℝ} {C : ℝ}
    (hf : IntervalIntegrable f volume 0 1) (hw : ContinuousOn w (uIcc (0 : ℝ) 1))
    (hC : ∀ u ∈ Icc (0 : ℝ) 1, |w u| ≤ C) :
    |∫ u in (0 : ℝ)..1, f u * w u| ≤ (∫ u in (0 : ℝ)..1, |f u|) * C := by
  calc
    _ ≤ ∫ u in (0 : ℝ)..1, |f u * w u| :=
      intervalIntegral.abs_integral_le_integral_abs (by norm_num)
    _ = ∫ u in (0 : ℝ)..1, |f u| * |w u| := by simp only [abs_mul]
    _ ≤ ∫ u in (0 : ℝ)..1, |f u| * C := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        (hf.abs.mul_continuousOn hw.abs) (hf.abs.mul_const C)
      intro u hu
      exact mul_le_mul_of_nonneg_left (hC u hu) (abs_nonneg _)
    _ = _ := intervalIntegral.integral_mul_const C _

theorem inverse_square_period_error {f g : ℝ → ℝ} {k : ℝ}
    (hk : 0 < k) (hf : IntervalIntegrable f volume 0 1)
    (hg : IntervalIntegrable g volume 0 1) :
    |(∫ u in (0 : ℝ)..1, f u / (k + u) ^ 2) -
        (∫ u in (0 : ℝ)..1, g u) / k ^ 2| ≤
      (∫ u in (0 : ℝ)..1, |f u - g u|) / k ^ 2 +
        (∫ u in (0 : ℝ)..1, |g u|) * (2 / k ^ 3) := by
  have hw := continuousOn_inverse_square_shift hk
  have he : (∫ u in (0 : ℝ)..1, f u / (k + u) ^ 2) -
      (∫ u in (0 : ℝ)..1, g u) / k ^ 2 =
      (∫ u in (0 : ℝ)..1, (f u - g u) * (1 / (k + u) ^ 2)) +
        ∫ u in (0 : ℝ)..1, g u * (1 / (k + u) ^ 2 - 1 / k ^ 2) := by
    have hw' : ContinuousOn (fun u : ℝ => 1 / (k + u) ^ 2 - 1 / k ^ 2)
        (uIcc (0 : ℝ) 1) := hw.sub continuousOn_const
    rw [← intervalIntegral.integral_add ((hf.sub hg).mul_continuousOn hw)
      (hg.mul_continuousOn hw')]
    rw [← intervalIntegral.integral_div, ← intervalIntegral.integral_sub
      (by simpa only [div_eq_mul_inv, one_mul] using hf.mul_continuousOn hw)
      (hg.div_const (k ^ 2))]
    apply intervalIntegral.integral_congr
    intro u _
    ring
  rw [he]
  apply (abs_add_le _ _).trans
  apply add_le_add
  · have hbound := intervalIntegral_abs_mul_le (hf.sub hg) hw (C := 1 / k ^ 2)
        (fun u hu => by
          rw [abs_of_nonneg (by positivity : 0 ≤ 1 / (k + u) ^ 2)]
          exact inverse_square_shift_le hk hu.1)
    simpa only [div_eq_mul_inv, one_mul] using hbound
  · exact intervalIntegral_abs_mul_le hg (hw.sub continuousOn_const)
      (fun _ hu => inverse_square_shift_abs_sub_le hk hu)

end PiIrrationality
