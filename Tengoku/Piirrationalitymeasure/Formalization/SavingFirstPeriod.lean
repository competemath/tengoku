import Tengoku.Piirrationalitymeasure.Formalization.SavingPeriodDifference

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The first period has a uniform linear error despite the weight at zero. -/

namespace PiIrrationality

open MeasureTheory Set Filter

theorem savingCandidatePerturbation_bounds {h : ℝ × ℝ} (hh : parameterNormOne h ≤ 1) :
    0 ≤ 1857 + h.1 ∧ 0 ≤ 3714 + h.2 ∧
      0 ≤ (1857 + h.1) + 2 * (3714 + h.2) - 5570 ∧
      1857 + h.1 ≤ 5571 ∧ 3714 + h.2 ≤ 5571 := by
  have hx : |h.1| ≤ 1 := by
    dsimp [parameterNormOne] at hh
    linarith [abs_nonneg h.2]
  have hy : |h.2| ≤ 1 := by
    dsimp [parameterNormOne] at hh
    linarith [abs_nonneg h.1]
  obtain ⟨hx0, hx1⟩ := abs_le.mp hx
  obtain ⟨hy0, hy1⟩ := abs_le.mp hy
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem savingCandidateDensityDifference_integrable {h : ℝ × ℝ}
    (hh : parameterNormOne h ≤ 1) :
    IntegrableOn (fun t => savingDensity (1857 + h.1) (3714 + h.2) 5570 t -
      savingDensity 1857 3714 5570 t) (Ioi (0 : ℝ)) := by
  obtain ⟨ha, hb, hq, _, _⟩ := savingCandidatePerturbation_bounds hh
  exact (savingDensity_integrableOn ha hb (by norm_num) hq).sub
    (savingDensity_integrableOn (by norm_num) (by norm_num) (by norm_num) (by norm_num))

theorem savingCandidateDensityDifference_initial_zero {h : ℝ × ℝ}
    (hh : parameterNormOne h ≤ 1) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (1 / 22288)) :
    savingDensity (1857 + h.1) (3714 + h.2) 5570 t - savingDensity 1857 3714 5570 t = 0 := by
  obtain ⟨ha, hb, hq, haK, hbK⟩ := savingCandidatePerturbation_bounds hh
  rcases ht.1.eq_or_lt with ht0 | ht0
  · simp [← ht0, savingDensity]
  have he : t ≤ 1 / (4 * ((5571 : ℝ) + 1)) := by norm_num; exact ht.2
  rw [savingDensity_initial_zero ha hb (by norm_num) (by norm_num) haK hbK (by norm_num)
    hq ht0 he,
    savingDensity_initial_zero (by norm_num) (by norm_num) (by norm_num)
      (by norm_num : (0 : ℝ) ≤ 5571) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) ht0 he]
  norm_num

theorem savingPeriodDifference_zero_bound {h : ℝ × ℝ} (hh : parameterNormOne h ≤ 1) :
    |savingPeriodDifference 1857 3714 5570 h 0| ≤
      (22288 : ℝ) ^ 2 * savingTranslationConstant 1857 3714 5570 * parameterNormOne h := by
  let f : ℝ → ℝ := fun t => savingDensity (1857 + h.1) (3714 + h.2) 5570 t -
    savingDensity 1857 3714 5570 t
  let g : ℝ → ℝ := fun t => translatedSavingChi 1857 3714 5570 (t • h) t -
    translatedSavingChi 1857 3714 5570 0 t
  have hfg (t : ℝ) : f t = g t / t ^ 2 := by
    simpa only [f, g, Int.cast_ofNat, Nat.cast_zero, zero_add] using
      savingDensity_shifted_difference 1857 3714 5570 h 0 t
  have hi : IntervalIntegrable f volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr
      ((savingCandidateDensityDifference_integrable hh).mono_set (fun _ ht => ht.1))
  have hj : IntervalIntegrable g volume 0 1 := by
    simpa only [g, zero_add] using
      (translatedSavingChi_affine_intervalIntegrable 1857 3714 5570 0 h).sub
        (translatedSavingChi_intervalIntegrable 1857 3714 5570 0)
  have hp : ∀ t ∈ Icc (0 : ℝ) 1, |f t| ≤ (22288 : ℝ) ^ 2 * |g t| := by
    intro t ht
    by_cases hsmall : t ≤ 1 / 22288
    · rw [show f t = 0 from savingCandidateDensityDifference_initial_zero hh ⟨ht.1, hsmall⟩]
      simp only [abs_zero]
      positivity
    · have ht0 : 0 < t := by linarith
      have hsq : 1 / t ^ 2 ≤ (22288 : ℝ) ^ 2 := by
        have hs : (1 / 22288 : ℝ) ^ 2 ≤ t ^ 2 := by nlinarith
        have hb := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < (1 / 22288) ^ 2) hs
        norm_num at hb ⊢
        exact hb
      rw [hfg, abs_div, abs_of_pos (sq_pos_of_pos ht0), div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right hsq (abs_nonneg _)
  have hg : (∫ t in (0 : ℝ)..1, |g t|) ≤
      savingTranslationConstant 1857 3714 5570 * parameterNormOne h := by
    simpa only [g, zero_add] using
      translatedSavingChi_integral_affine_translation 0 h
        (by norm_num : (1857 : ℝ) ≠ 0) (by norm_num : (3714 : ℝ) ≠ 0)
        (by norm_num : (1857 : ℝ) + 2 * 3714 - 5570 ≠ 0)
        (by norm_num [parameterNormOne]) hh
  have he : savingPeriodDifference 1857 3714 5570 h 0 = ∫ t in (0 : ℝ)..1, f t := by
    unfold savingPeriodDifference
    simp only [zero_add]
    apply intervalIntegral.integral_congr
    intro t _
    exact (hfg t).symm
  rw [he]
  calc
    _ ≤ ∫ t in (0 : ℝ)..1, |f t| :=
      intervalIntegral.abs_integral_le_integral_abs (by norm_num)
    _ ≤ ∫ t in (0 : ℝ)..1, (22288 : ℝ) ^ 2 * |g t| :=
      intervalIntegral.integral_mono_on (by norm_num) hi.abs (hj.abs.const_mul _) hp
    _ = (22288 : ℝ) ^ 2 * ∫ t in (0 : ℝ)..1, |g t| :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ (22288 : ℝ) ^ 2 *
        (savingTranslationConstant 1857 3714 5570 * parameterNormOne h) := by gcongr
    _ = _ := by ring

end PiIrrationality
