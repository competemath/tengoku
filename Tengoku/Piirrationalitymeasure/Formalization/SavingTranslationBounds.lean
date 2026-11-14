import Tengoku.Piirrationalitymeasure.Formalization.FloorDisagreementIntegral
import Tengoku.Piirrationalitymeasure.Formalization.TranslatedSavingMeasure

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Uniform translation estimates (6.15)--(6.16). -/

namespace PiIrrationality

open MeasureTheory Set Filter

noncomputable def parameterNormOne (z : ℝ × ℝ) : ℝ := |z.1| + |z.2|

/--
@isnad1 id=le.0h1v.s3.4519e0eba62c from=translated src=- shape=70dff6bb vocab=f6333cac
-/
theorem parameterNormOne_nonneg (z : ℝ × ℝ) : 0 ≤ parameterNormOne z :=
  add_nonneg (abs_nonneg _) (abs_nonneg _)

/--
@isnad1 id=le.0h2v.s5.ac251cdf3e37 from=translated src=- shape=f24af865 vocab=e03d9ad7
-/
theorem parameterNormOne_sub_le (z w : ℝ × ℝ) :
    parameterNormOne (z - w) ≤ parameterNormOne z + parameterNormOne w := by
  dsimp [parameterNormOne]
  linarith [abs_sub z.1 w.1, abs_sub z.2 w.2]

/--
@isnad1 id=eq.0h2v.s5.c58fd9fd8e44 from=translated src=- shape=9b3301b0 vocab=518ecfa4
-/
theorem parameterNormOne_smul (s : ℝ) (z : ℝ × ℝ) :
    parameterNormOne (s • z) = |s| * parameterNormOne z := by
  dsimp [parameterNormOne]
  rw [abs_mul, abs_mul]
  ring

noncomputable def savingTranslationConstant (a b c : ℝ) : ℝ :=
  floorChangeConstant a + floorChangeConstant b + 2 * floorChangeConstant (a + 2 * b - c)

/--
@isnad1 id=le.0h3v.s4.a624e4af5496 from=translated src=- shape=ac9c39a3 vocab=1056ba42
-/
theorem savingTranslationConstant_nonneg (a b c : ℝ) : 0 ≤ savingTranslationConstant a b c := by
  unfold savingTranslationConstant
  linarith [floorChangeConstant_nonneg a, floorChangeConstant_nonneg b,
    floorChangeConstant_nonneg (a + 2 * b - c)]

/--
@isnad1 id=le.0h6v.s8.b2a4a8ccde39 from=translated src=- shape=cbb5f8ca vocab=360a8902
-/
theorem translatedSavingChi_abs_sub_le_floors (a b c : ℝ) (z w : ℝ × ℝ) (u : ℝ) :
    |translatedSavingChi a b c (z + w) u - translatedSavingChi a b c z u| ≤
      floorDisagreement (a * u + (z.1 + 1 / 2)) (a * u + (z.1 + 1 / 2) + w.1) +
      floorDisagreement (b * u + z.2) (b * u + z.2 + w.2) +
      floorDisagreement ((a + 2 * b - c) * u + (1 / 2 + z.1 + 2 * z.2))
        ((a + 2 * b - c) * u + (1 / 2 + z.1 + 2 * z.2) + (w.1 + 2 * w.2)) := by
  have h := savingChi_abs_sub_le_floorDisagreement (a * u + z.1) (b * u + z.2) (c * u)
    (a * u + (z.1 + w.1)) (b * u + (z.2 + w.2)) (c * u)
  have hz : floorDisagreement (c * u) (c * u) = 0 := by simp [floorDisagreement]
  rw [hz, add_zero] at h
  rw [abs_sub_comm]
  dsimp only [translatedSavingChi, Prod.fst_add, Prod.snd_add]
  convert h using 1 <;> congr 1 <;> ring

/--
@isnad1 id=integrab.1h5v.s6.57357d6ad4ae from=translated src=- shape=ce735ed0 vocab=96da7e4a
-/
theorem translatedSavingChi_perturbation_integrable (a b c : ℝ) (z : ℝ × ℝ)
    {w : ℝ → ℝ × ℝ} (hw : Measurable w) :
    IntegrableOn (fun u => |translatedSavingChi a b c (z + w u) u -
      translatedSavingChi a b c z u|) (Ioc (0 : ℝ) 1) := by
  have hm : Measurable (fun u => translatedSavingChi a b c (z + w u) u) := by
    unfold translatedSavingChi savingChi
    apply Measurable.ite _ measurable_const measurable_const
    apply measurableSet_lt <;> fun_prop
  have hi : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc (0 : ℝ) 1) volume :=
    integrableOn_const (by simp)
  apply hi.mono' (hm.sub (measurable_translatedSavingChi a b c z)).abs.aestronglyMeasurable
  exact Eventually.of_forall fun u => by
    rw [Real.norm_eq_abs, abs_abs]
    exact savingChi_abs_sub_le_one _ _ _ _ _ _

/--
@isnad1 id=le.8h6v.s7.199ac36486e0 from=translated src=- shape=0adc5088 vocab=07f0433b
-/
theorem translatedSavingChi_integral_perturbation {a b c r : ℝ} (z : ℝ × ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hq : a + 2 * b - c ≠ 0)
    (hz : parameterNormOne z ≤ 1) (hr0 : 0 ≤ r) (hr2 : r ≤ 2)
    {w : ℝ → ℝ × ℝ} (hw : Measurable w)
    (hwr : ∀ u ∈ Icc (0 : ℝ) 1, parameterNormOne (w u) ≤ r) :
    (∫ u in (0 : ℝ)..1, |translatedSavingChi a b c (z + w u) u -
      translatedSavingChi a b c z u|) ≤ savingTranslationConstant a b c * r := by
  let A (u : ℝ) := floorDisagreement (a * u + (z.1 + 1 / 2))
    (a * u + (z.1 + 1 / 2) + (w u).1)
  let B (u : ℝ) := floorDisagreement (b * u + z.2) (b * u + z.2 + (w u).2)
  let Q (u : ℝ) := floorDisagreement ((a + 2 * b - c) * u + (1 / 2 + z.1 + 2 * z.2))
    ((a + 2 * b - c) * u + (1 / 2 + z.1 + 2 * z.2) + ((w u).1 + 2 * (w u).2))
  have hAi : IntegrableOn A (Ioc (0 : ℝ) 1) :=
    integrableOn_floorDisagreement (by fun_prop) (by fun_prop)
  have hBi : IntegrableOn B (Ioc (0 : ℝ) 1) :=
    integrableOn_floorDisagreement (by fun_prop) (by fun_prop)
  have hQi : IntegrableOn Q (Ioc (0 : ℝ) 1) :=
    integrableOn_floorDisagreement (by fun_prop) (by fun_prop)
  have hz1 : |z.1| ≤ 1 := by have := abs_nonneg z.2; exact le_trans (by dsimp [parameterNormOne]; linarith) hz
  have hz2 : |z.2| ≤ 1 := by have := abs_nonneg z.1; exact le_trans (by dsimp [parameterNormOne]; linarith) hz
  have hA : (∫ u in (0 : ℝ)..1, A u) ≤ floorChangeConstant a * r := by
    refine integral_floorDisagreement_uniform ha ?_ hr0 (by linarith) (by fun_prop) ?_
    · have h := abs_add_le z.1 (1 / 2 : ℝ)
      norm_num at h
      linarith
    · intro u hu
      have h := hwr u hu
      dsimp [parameterNormOne] at h
      linarith [abs_nonneg (w u).2]
  have hB : (∫ u in (0 : ℝ)..1, B u) ≤ floorChangeConstant b * r := by
    apply integral_floorDisagreement_uniform hb (by linarith) hr0 (by linarith) (by fun_prop)
    intro u hu
    have h := hwr u hu
    dsimp [parameterNormOne] at h
    linarith [abs_nonneg (w u).1]
  have hQ : (∫ u in (0 : ℝ)..1, Q u) ≤ floorChangeConstant (a + 2 * b - c) * (2 * r) := by
    refine integral_floorDisagreement_uniform hq ?_ (by positivity) (by linarith) (by fun_prop) ?_
    · have h1 := abs_add_le (1 / 2 : ℝ) z.1
      have h2 := abs_add_le (1 / 2 + z.1) (2 * z.2)
      rw [abs_mul] at h2
      norm_num at h1 h2
      linarith
    · intro u hu
      have h := hwr u hu
      dsimp [parameterNormOne] at h
      have hsum := abs_add_le (w u).1 (2 * (w u).2)
      rw [abs_mul] at hsum
      norm_num at hsum
      linarith [abs_nonneg (w u).1]
  have hmono : (∫ u in Ioc (0 : ℝ) 1, |translatedSavingChi a b c (z + w u) u -
      translatedSavingChi a b c z u|) ≤ ∫ u in Ioc (0 : ℝ) 1, A u + B u + Q u := by
    apply setIntegral_mono_on (translatedSavingChi_perturbation_integrable a b c z hw)
      ((hAi.add hBi).add hQi) measurableSet_Ioc
    intro u _
    exact translatedSavingChi_abs_sub_le_floors a b c z (w u) u
  rw [integral_add (f := fun u => A u + B u) (hAi.add hBi) hQi, integral_add hAi hBi] at hmono
  rw [intervalIntegral.integral_of_le (by norm_num)] at hA hB hQ ⊢
  unfold savingTranslationConstant
  nlinarith [hmono]

/--
@isnad1 id=le.5h5v.s7.3d2280bfd2c5 from=translated src=- shape=c6e3fcd0 vocab=b6c0c7b0
-/
theorem translatedSavingChi_integral_translation {a b c : ℝ} (z z' : ℝ × ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hq : a + 2 * b - c ≠ 0)
    (hz : parameterNormOne z ≤ 1) (hz' : parameterNormOne z' ≤ 1) :
    (∫ u in (0 : ℝ)..1, |translatedSavingChi a b c z' u - translatedSavingChi a b c z u|) ≤
      savingTranslationConstant a b c * parameterNormOne (z' - z) := by
  have hr2 : parameterNormOne (z' - z) ≤ 2 := by
    linarith [parameterNormOne_sub_le z' z]
  have h := translatedSavingChi_integral_perturbation z ha hb hq hz
    (parameterNormOne_nonneg (z' - z)) hr2 (measurable_const (a := z' - z))
    (fun _ _ => le_rfl)
  have he : z + (z' - z) = z' := by abel
  simpa only [he] using h

/--
@isnad1 id=le.5h5v.s7.a62e1274d861 from=translated src=- shape=b6d6c69a vocab=32298163
-/
theorem translatedSavingChi_integral_affine_translation {a b c : ℝ} (z w : ℝ × ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hq : a + 2 * b - c ≠ 0)
    (hz : parameterNormOne z ≤ 1) (hw : parameterNormOne w ≤ 1) :
    (∫ u in (0 : ℝ)..1, |translatedSavingChi a b c (z + u • w) u -
      translatedSavingChi a b c z u|) ≤ savingTranslationConstant a b c * parameterNormOne w := by
  apply translatedSavingChi_integral_perturbation z ha hb hq hz
    (parameterNormOne_nonneg w) (by linarith) (by fun_prop)
  intro u hu
  rw [parameterNormOne_smul, abs_of_nonneg hu.1]
  exact mul_le_of_le_one_left (parameterNormOne_nonneg w) hu.2

/--
@isnad1 id=interval.0h4v.s5.ab42940f771c from=translated src=- shape=16a1dc2e vocab=f22b64a4
-/
theorem translatedSavingChi_intervalIntegrable (a b c : ℝ) (z : ℝ × ℝ) :
    IntervalIntegrable (translatedSavingChi a b c z) volume 0 1 := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
  have hi : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc (0 : ℝ) 1) volume :=
    integrableOn_const (by simp)
  apply hi.mono' (measurable_translatedSavingChi a b c z).aestronglyMeasurable
  exact Eventually.of_forall fun u => by
    rw [translatedSavingChi, Real.norm_eq_abs, abs_of_nonneg (savingChi_nonneg _ _ _)]
    exact savingChi_le_one _ _ _

/--
@isnad1 id=le.5h5v.s7.c67c02a2a7f9 from=translated src=- shape=98afcfa3 vocab=bb083306
-/
theorem translatedSavingMeasure_abs_sub_le {a b c : ℝ} (z z' : ℝ × ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hq : a + 2 * b - c ≠ 0)
    (hz : parameterNormOne z ≤ 1) (hz' : parameterNormOne z' ≤ 1) :
    |translatedSavingMeasure a b c z' - translatedSavingMeasure a b c z| ≤
      savingTranslationConstant a b c * parameterNormOne (z' - z) := by
  unfold translatedSavingMeasure
  rw [← intervalIntegral.integral_sub (translatedSavingChi_intervalIntegrable a b c z')
    (translatedSavingChi_intervalIntegrable a b c z)]
  have hn := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
    (f := fun u => translatedSavingChi a b c z' u - translatedSavingChi a b c z u)
    (by norm_num : (0 : ℝ) ≤ 1)
  simp only [Real.norm_eq_abs] at hn
  exact hn.trans (translatedSavingChi_integral_translation z z' ha hb hq hz hz')

end PiIrrationality
