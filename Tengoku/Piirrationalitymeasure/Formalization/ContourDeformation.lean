import Tengoku.Piirrationalitymeasure.Formalization.ComplexDensityPrimitive
import Tengoku.Piirrationalitymeasure.Formalization.SmoothContourLift

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Deformation of the actual integral to the two oriented square-root lifts. -/

namespace PiIrrationality

/--
@isnad1 id=interval.2h4v.s7.c0c45dc7f314 from=translated src=- shape=90685a6d vocab=a970dcd0
-/
theorem complexDensity_path_integrable (n : ℕ) {g : ℝ → ℂ} {a b : ℝ}
    (hg : ContDiff ℝ 1 g) (hB : ∀ u ∈ Set.uIcc a b, ‖g u‖ < 5) :
    IntervalIntegrable (fun u => complexDensity n (g u) * deriv g u)
      MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro u hu
  exact (((complexDensity_differentiableAt n (hB u hu)).continuousAt.comp
    hg.continuous.continuousAt).mul hg.continuous_deriv_one.continuousAt).continuousWithinAt

/--
@isnad1 id=eq.3h5v.s7.6b7194e0b70f from=translated src=- shape=dcead4ed vocab=c242bfd3
-/
theorem complexDensity_path_primitive (n : ℕ) {F : ℂ → ℂ}
    (hF : ∀ z : ℂ, ‖z‖ < 5 → HasDerivAt F (complexDensity n z) z)
    {g : ℝ → ℂ} {a b : ℝ} (hg : ContDiff ℝ 1 g)
    (hB : ∀ u ∈ Set.uIcc a b, ‖g u‖ < 5) :
    (∫ u in a..b, complexDensity n (g u) * deriv g u) = F (g b) - F (g a) := by
  exact complex_primitive_path_integral (fun u hu => hF _ (hB u hu))
    (fun u _ => (hg.differentiable (by norm_num) u).hasDerivAt)
    (complexDensity_path_integrable n hg hB)

/--
@isnad1 id=lt.1h1v.s5.d8746faddded from=translated src=- shape=7576d777 vocab=570e3832
-/
theorem verticalSegment_norm_lt_five {s : ℝ} (hs : s ∈ Set.uIcc (-2 : ℝ) 2) :
    ‖verticalSegment s‖ < 5 := by
  have hs' : -2 ≤ s ∧ s ≤ 2 := by simpa using hs
  have hsq := Complex.sq_norm (verticalSegment s)
  norm_num [verticalSegment, Complex.normSq_apply] at hsq
  change ‖verticalSegment s‖ ^ 2 = 1 + s * s at hsq
  nlinarith [norm_nonneg (verticalSegment s),
    mul_nonneg (by linarith : 0 ≤ s + 2) (by linarith : 0 ≤ 2 - s)]

/--
@isnad1 id=hasderiv.0h1v.s5.4e3ffcb68720 from=translated src=- shape=297e8ec8 vocab=740d1fc3
-/
theorem verticalSegment_hasDerivAt (s : ℝ) : HasDerivAt verticalSegment Complex.I s := by
  convert! (((hasDerivAt_id s).ofReal_comp.mul_const Complex.I).const_add (-1)) using 1 <;>
    simp [verticalSegment]

/--
@isnad1 id=eq.1h2v.s7.683e94206819 from=translated src=- shape=6cdf22b7 vocab=f3b0c9c1
-/
theorem paperIntegral_primitive (n : ℕ) {F : ℂ → ℂ}
    (hF : ∀ z : ℂ, ‖z‖ < 5 → HasDerivAt F (complexDensity n z) z) :
    paperIntegral n = Complex.I * (F (-1 + 2 * Complex.I) - F (-1 - 2 * Complex.I)) := by
  have h := complex_primitive_path_integral
    (fun s hs => hF (verticalSegment s) (verticalSegment_norm_lt_five hs))
    (fun s _ => verticalSegment_hasDerivAt s)
    ((verticalDensity_continuous n).mul_const Complex.I |>.intervalIntegrable (-2) 2)
  simp only [complexDensity_vertical, intervalIntegral.integral_mul_const] at h
  have he : verticalSegment 2 = -1 + 2 * Complex.I ∧
      verticalSegment (-2) = -1 - 2 * Complex.I := by
    constructor <;> norm_num [verticalSegment] <;> ring
  rw [he.1, he.2] at h
  rw [← h, paperIntegral]
  calc
    -(∫ s : ℝ in (-2)..2, verticalDensity n s) =
        (Complex.I * Complex.I) * (∫ s : ℝ in (-2)..2, verticalDensity n s) := by
      rw [Complex.I_mul_I, neg_one_mul]
    _ = _ := by ring

noncomputable def densityPathIntegral (n : ℕ) (g : ℝ → ℂ) : ℂ :=
  ∫ u in (0 : ℝ)..1, complexDensity n (g u) * deriv g u

/--
@isnad1 id=interval.2h2v.s7.491f04ea9cf9 from=translated src=- shape=726cb935 vocab=6174b08f
-/
theorem smoothTauPlus_density_integrable (n : ℕ) {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    IntervalIntegrable (fun u => complexDensity n (smoothTauPlus e u) * deriv (smoothTauPlus e) u)
      MeasureTheory.volume 0 1 := by
  apply complexDensity_path_integrable n (smoothTauPlus_contDiff he0 he1)
  intro u hu
  have hu' : 0 ≤ u ∧ u ≤ 1 := by simpa using hu
  exact smoothTauPlus_norm_lt_five he0 he1 hu'.1 hu'.2

/--
@isnad1 id=interval.2h2v.s7.57d722062053 from=translated src=- shape=726cb935 vocab=a36038ef
-/
theorem smoothTauMinus_density_integrable (n : ℕ) {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    IntervalIntegrable (fun u => complexDensity n (smoothTauMinus e u) * deriv (smoothTauMinus e) u)
      MeasureTheory.volume 0 1 := by
  apply complexDensity_path_integrable n (smoothTauMinus_contDiff he0 he1)
  intro u hu
  have hu' : 0 ≤ u ∧ u ≤ 1 := by simpa using hu
  exact smoothTauMinus_norm_lt_five he0 he1 hu'.1 hu'.2

/--
@isnad1 id=eq.2h2v.s5.aa6d8a3c2da8 from=translated src=- shape=8b792575 vocab=954ce894
-/
theorem paperIntegral_deformed (n : ℕ) {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    paperIntegral n = Complex.I * (-densityPathIntegral n (smoothTauPlus e) +
      densityPathIntegral n (smoothTauMinus e)) := by
  obtain ⟨F, hF⟩ := complexDensity_primitive n
  have hp : densityPathIntegral n (smoothTauPlus e) = F (-1 - 2 * Complex.I) - F 0 := by
    have h := complexDensity_path_primitive n hF (smoothTauPlus_contDiff he0 he1)
      (a := 0) (b := 1) (fun u hu => smoothTauPlus_norm_lt_five he0 he1
        (by simpa using hu.1) (by simpa using hu.2))
    simpa only [densityPathIntegral, smoothTauPlus_at_zero, smoothTauPlus_at_one] using h
  have hm : densityPathIntegral n (smoothTauMinus e) = F (-1 + 2 * Complex.I) - F 0 := by
    have h := complexDensity_path_primitive n hF (smoothTauMinus_contDiff he0 he1)
      (a := 0) (b := 1) (fun u hu => smoothTauMinus_norm_lt_five he0 he1
        (by simpa using hu.1) (by simpa using hu.2))
    simpa only [densityPathIntegral, smoothTauMinus_at_zero, smoothTauMinus_at_one] using h
  rw [paperIntegral_primitive n hF, hp, hm]
  ring

end PiIrrationality
