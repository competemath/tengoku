import Tengoku.Piirrationalitymeasure.Formalization.SavingTranslationBounds
import Tengoku.Piirrationalitymeasure.Formalization.InverseSquarePeriod
import Tengoku.Piirrationalitymeasure.Formalization.PeriodIntegral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Actual period contributions and their uniform error bound in (6.22)--(6.25). -/

namespace PiIrrationality

open MeasureTheory Set Filter

noncomputable def savingPeriodDifference (a b c : ℝ) (h : ℝ × ℝ) (k : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..1,
    (translatedSavingChi a b c ((k + u) • h) u - translatedSavingChi a b c 0 u) /
      (k + u) ^ 2

/--
@isnad1 id=interval.0h5v.s6.6238eba799dd from=translated src=- shape=3417e051 vocab=287a2ca5
-/
theorem translatedSavingChi_affine_intervalIntegrable (a b c : ℝ) (z w : ℝ × ℝ) :
    IntervalIntegrable (fun u => translatedSavingChi a b c (z + u • w) u) volume 0 1 := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
  have hm : Measurable (fun u => translatedSavingChi a b c (z + u • w) u) := by
    unfold translatedSavingChi savingChi
    apply Measurable.ite _ measurable_const measurable_const
    apply measurableSet_lt <;> fun_prop
  have hi : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc (0 : ℝ) 1) volume :=
    integrableOn_const (by simp)
  apply hi.mono' hm.aestronglyMeasurable
  exact Eventually.of_forall fun u => by
    rw [translatedSavingChi, Real.norm_eq_abs, abs_of_nonneg (savingChi_nonneg _ _ _)]
    exact savingChi_le_one _ _ _

/--
@isnad1 id=eq.0h6v.s7.12b7072dd335 from=translated src=- shape=ee6fe476 vocab=52a5fe11
-/
theorem savingDensity_shifted_difference (a b c : ℤ) (h : ℝ × ℝ) (k : ℕ) (u : ℝ) :
    savingDensity ((a : ℝ) + h.1) ((b : ℝ) + h.2) c ((k : ℝ) + u) -
        savingDensity a b c ((k : ℝ) + u) =
      (translatedSavingChi a b c (((k : ℝ) + u) • h) u -
        translatedSavingChi a b c 0 u) / ((k : ℝ) + u) ^ 2 := by
  have hshift : savingChi (((a : ℝ) + h.1) * ((k : ℝ) + u))
      (((b : ℝ) + h.2) * ((k : ℝ) + u)) ((c : ℝ) * ((k : ℝ) + u)) =
      translatedSavingChi a b c (((k : ℝ) + u) • h) u := by
    have hmul (m : ℤ) (x : ℝ) : ((m : ℝ) + x) * ((k : ℝ) + u) =
        ((m : ℝ) * u + ((k : ℝ) + u) * x) + ((m * (k : ℤ) : ℤ) : ℝ) := by
      push_cast
      ring
    rw [hmul a h.1, hmul b h.2,
      show (c : ℝ) * ((k : ℝ) + u) = (c : ℝ) * u + ((c * (k : ℤ) : ℤ) : ℝ) by
        push_cast; ring,
      savingChi_add_int]
    rfl
  unfold savingDensity
  rw [hshift, savingChi_integer_periodic]
  simp only [translatedSavingChi, Prod.fst_zero, Prod.snd_zero, add_zero]
  exact (sub_div _ _ _).symm

/--
@isnad1 id=hassum.7h4v.s8.5f92aab5de13 from=translated src=- shape=fd8cdbf3 vocab=a0ecf3b1
-/
theorem savingOmega_difference_hasSum (a b c : ℤ) (h : ℝ × ℝ)
    (ha : 0 ≤ (a : ℝ)) (hb : 0 ≤ (b : ℝ)) (hc : 0 ≤ (c : ℝ))
    (hq : 0 ≤ (a : ℝ) + 2 * b - c)
    (hah : 0 ≤ (a : ℝ) + h.1) (hbh : 0 ≤ (b : ℝ) + h.2)
    (hqh : 0 ≤ ((a : ℝ) + h.1) + 2 * ((b : ℝ) + h.2) - c) :
    HasSum (fun k : ℕ => savingPeriodDifference a b c h k)
      (savingOmega ((a : ℝ) + h.1) ((b : ℝ) + h.2) c - savingOmega a b c) := by
  have hi := savingDensity_integrableOn hah hbh hc hqh
  have hj := savingDensity_integrableOn ha hb hc hq
  have hs := hasSum_integral_shifted_periods (hi.sub hj)
  simp only [Pi.sub_apply] at hs
  rw [integral_sub hi hj] at hs
  convert hs using 1
  · funext k
    unfold savingPeriodDifference
    apply intervalIntegral.integral_congr
    intro u _
    exact (savingDensity_shifted_difference a b c h k u).symm
  · rfl

/--
@isnad1 id=le.6h5v.s8.51807e23ea30 from=translated src=- shape=b8cc76e5 vocab=a9d19b2f
-/
theorem savingPeriodDifference_error {a b c k : ℝ} (h : ℝ × ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hq : a + 2 * b - c ≠ 0)
    (hk : 0 < k) (hh : parameterNormOne h ≤ 1)
    (hkh : parameterNormOne (k • h) ≤ 1) :
    |savingPeriodDifference a b c h k -
        (translatedSavingMeasure a b c (k • h) - translatedSavingMeasure a b c 0) / k ^ 2| ≤
      3 * savingTranslationConstant a b c * parameterNormOne h / k ^ 2 := by
  let f : ℝ → ℝ := fun u => translatedSavingChi a b c ((k + u) • h) u -
    translatedSavingChi a b c 0 u
  let g : ℝ → ℝ := fun u => translatedSavingChi a b c (k • h) u -
    translatedSavingChi a b c 0 u
  have hi : IntervalIntegrable f volume 0 1 := by
    simpa only [f, add_smul] using
      (translatedSavingChi_affine_intervalIntegrable a b c (k • h) h).sub
        (translatedSavingChi_intervalIntegrable a b c 0)
  have hj : IntervalIntegrable g volume 0 1 :=
    (translatedSavingChi_intervalIntegrable a b c (k • h)).sub
      (translatedSavingChi_intervalIntegrable a b c 0)
  have hfg : (∫ u in (0 : ℝ)..1, |f u - g u|) ≤
      savingTranslationConstant a b c * parameterNormOne h := by
    simpa only [f, g, sub_sub_sub_cancel_right, add_smul] using
      translatedSavingChi_integral_affine_translation (k • h) h ha hb hq hkh hh
  have hg : (∫ u in (0 : ℝ)..1, |g u|) ≤
      savingTranslationConstant a b c * (k * parameterNormOne h) := by
    simpa only [g, sub_zero, parameterNormOne_smul, abs_of_pos hk] using
      translatedSavingChi_integral_translation 0 (k • h) ha hb hq
        (by norm_num [parameterNormOne]) hkh
  have hgm : (∫ u in (0 : ℝ)..1, g u) =
      translatedSavingMeasure a b c (k • h) - translatedSavingMeasure a b c 0 :=
    intervalIntegral.integral_sub (translatedSavingChi_intervalIntegrable a b c (k • h))
      (translatedSavingChi_intervalIntegrable a b c 0)
  have he := inverse_square_period_error hk hi hj
  rw [hgm] at he
  apply he.trans
  calc
    _ ≤ savingTranslationConstant a b c * parameterNormOne h / k ^ 2 +
        (savingTranslationConstant a b c * (k * parameterNormOne h)) * (2 / k ^ 3) := by
      exact add_le_add (div_le_div_of_nonneg_right hfg (sq_nonneg _))
        (mul_le_mul_of_nonneg_right hg (by positivity))
    _ = _ := by field_simp; ring

end PiIrrationality
