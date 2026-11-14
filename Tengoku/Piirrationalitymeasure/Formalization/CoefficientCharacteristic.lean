import Tengoku.Piirrationalitymeasure.Formalization.CoefficientCircle
import Tengoku.Piirrationalitymeasure.Formalization.CoefficientMoments

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Characteristic functions of the actual tilted lattice distributions. -/

namespace PiIrrationality

open MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable def coefficientChar (x t : ℝ) : ℂ :=
  SComplex ((x : ℂ) * Complex.exp ((t : ℂ) * Complex.I)) / (SReal x : ℂ)

noncomputable def coefficientCenteredChar (x t : ℝ) : ℂ :=
  coefficientChar x t * Complex.exp (((-coefficientMean x * t : ℝ) : ℂ) * Complex.I)

/--
@isnad1 id=eq.1h2v.s5.535583c8ba62 from=translated src=- shape=c0d7191f vocab=f6f6c1e9
-/
theorem coefficient_circle_norm {x : ℝ} (hx0 : 0 ≤ x) (t : ℝ) :
    ‖(x : ℂ) * Complex.exp ((t : ℂ) * Complex.I)‖ = x := by
  simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0]

/--
@isnad1 id=hassum.2h3v.s6.12aa7c9cb280 from=translated src=- shape=a44339be vocab=d75f2c9d
-/
theorem coefficientProbability_fourier_sum {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (n : ℕ) (t : ℝ) :
    HasSum (fun k => (coefficientProbability x n k : ℂ) *
      Complex.exp ((k : ℂ) * (t : ℂ) * Complex.I)) (coefficientChar x t ^ n) := by
  have hz : ‖(x : ℂ) * Complex.exp ((t : ℂ) * Complex.I)‖ < 1 := by
    rwa [coefficient_circle_norm hx0]
  have h := (ratSeries_hasSum_pow (SComplex_hasSum hz) n).div_const ((SReal x ^ n : ℝ) : ℂ)
  convert! h using 1
  · ext k
    have he : Complex.exp ((k : ℂ) * (t : ℂ) * Complex.I) =
        Complex.exp ((t : ℂ) * Complex.I) ^ k := by
      rw [mul_assoc, Complex.exp_nat_mul]
    rw [he]
    simp only [coefficientProbability, Complex.ofReal_div, Complex.ofReal_mul,
      Complex.ofReal_pow, Complex.ofReal_ratCast, mul_pow]
    ring
  · simp only [coefficientChar, div_pow, Complex.ofReal_pow]

/--
@isnad1 id=integrab.0h2v.s6.6297b0e489e1 from=translated src=- shape=56345380 vocab=0c4947ae
-/
theorem pmf_nat_integrable_cexp (p : PMF ℕ) (t : ℝ) :
    Integrable (fun k : ℕ => Complex.exp ((t : ℂ) * (k : ℂ) * Complex.I)) p.toMeasure := by
  apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
  exact Filter.Eventually.of_forall (fun k => by simp [Complex.norm_exp])

/--
@isnad1 id=eq.2h3v.s6.1009a02c52bc from=translated src=- shape=bd59e3fc vocab=ec57b194
-/
theorem coefficientLaw_charFun {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (n : ℕ) (t : ℝ) :
    charFun ((coefficientLaw x hx0 hx1 n).toMeasure.map (fun k : ℕ => (k : ℝ))) t =
      coefficientChar x t ^ n := by
  rw [charFun_apply_real, integral_map (by fun_prop) (by fun_prop)]
  simp only [Complex.ofReal_natCast]
  rw [PMF.integral_eq_tsum _ _ (pmf_nat_integrable_cexp _ t)]
  convert! (coefficientProbability_fourier_sum hx0 hx1 n t).tsum_eq using 1
  apply tsum_congr
  intro k
  simp only [coefficientLaw_toReal, RCLike.real_smul_eq_coe_mul, mul_comm (t : ℂ)]
  rfl

/--
@isnad1 id=eq.2h2v.s6.02589ac1e830 from=translated src=- shape=f8e54289 vocab=3fbfdc3b
-/
theorem coefficientLaw_centered_charFun {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (t : ℝ) :
    charFun ((coefficientLaw x hx0 hx1 1).toMeasure.map
      (fun k : ℕ => (k : ℝ) - coefficientMean x)) t = coefficientCenteredChar x t := by
  have hf : (fun k : ℕ => (k : ℝ) - coefficientMean x) =
      (fun y : ℝ => y + (-coefficientMean x)) ∘ (fun k : ℕ => (k : ℝ)) := by
    ext k
    simp [sub_eq_add_neg]
  rw [hf, ← Measure.map_map (by fun_prop) (by fun_prop), charFun_map_add_const,
    coefficientLaw_charFun hx0 hx1, pow_one]
  simp only [coefficientCenteredChar, RCLike.inner_apply, conj_trivial,
    mul_comm t (-coefficientMean x)]

/--
@isnad1 id=le.2h2v.s5.e42522b35bad from=translated src=- shape=dba80fe6 vocab=e30e50c1
-/
theorem coefficientChar_norm_le_one {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (t : ℝ) :
    ‖coefficientChar x t‖ ≤ 1 := by
  have : IsProbabilityMeasure
      ((coefficientLaw x hx0 hx1 1).toMeasure.map (fun k : ℕ => (k : ℝ))) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  have h := norm_charFun_le_one
    (μ := (coefficientLaw x hx0 hx1 1).toMeasure.map (fun k : ℕ => (k : ℝ))) t
  simpa only [coefficientLaw_charFun hx0 hx1, pow_one] using h

/--
@isnad1 id=eq.0h2v.s4.e71e86d23e66 from=translated src=- shape=6bb5e8cb vocab=8062d261
-/
theorem coefficientCenteredChar_norm (x t : ℝ) :
    ‖coefficientCenteredChar x t‖ = ‖coefficientChar x t‖ := by
  simp only [coefficientCenteredChar, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

/--
@isnad1 id=ne.2h1v.s5.7d03454ee9cb from=translated src=- shape=cf6f55c1 vocab=a27a2ae2
-/
theorem exp_mul_I_ne_one {t : ℝ} (ht0 : 0 < |t|) (htπ : |t| ≤ Real.pi) :
    Complex.exp ((t : ℂ) * Complex.I) ≠ 1 := by
  intro he
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp he
  have h := congrArg Complex.im hn
  norm_num at h
  have hn0 : n = 0 := by
    by_contra hn0
    rcases lt_or_gt_of_ne hn0 with hnneg | hnpos
    · have hn1 : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
      nlinarith [Real.pi_pos, (abs_le.mp htπ).1]
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      nlinarith [Real.pi_pos, (abs_le.mp htπ).2]
  simp [hn0] at h
  simp [h] at ht0

/--
@isnad1 id=lt.4h2v.s6.3fcf5cd425d6 from=translated src=- shape=76cd8926 vocab=dfe411dc
-/
theorem coefficientChar_norm_strict {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    {t : ℝ} (ht0 : 0 < |t|) (htπ : |t| ≤ Real.pi) : ‖coefficientChar x t‖ < 1 := by
  have hz : ‖(x : ℂ) * Complex.exp ((t : ℂ) * Complex.I)‖ < 1 := by
    rwa [coefficient_circle_norm hx0.le]
  have hne : (x : ℂ) * Complex.exp ((t : ℂ) * Complex.I) ≠ (x : ℂ) := by
    intro heq
    apply exp_mul_I_ne_one ht0 htπ
    apply mul_left_cancel₀ (show (x : ℂ) ≠ 0 by exact_mod_cast hx0.ne')
    simpa only [mul_one] using heq
  have hs := SComplex_norm_strict hz
    (by simpa only [coefficient_circle_norm hx0.le] using hne)
  rw [coefficient_circle_norm hx0.le] at hs
  simpa only [coefficientChar, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (SReal_pos hx0.le hx1), div_lt_one (SReal_pos hx0.le hx1)] using hs

/--
@isnad1 id=continuo.2h1v.s5.56a018b12017 from=translated src=- shape=2c15df1c vocab=fa059389
-/
theorem coefficientChar_continuous {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Continuous (coefficientChar x) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hz : ‖(x : ℂ) * Complex.exp ((t : ℂ) * Complex.I)‖ < 1 := by
    rwa [coefficient_circle_norm hx0]
  have hc : ContinuousAt (fun s : ℝ => (x : ℂ) * Complex.exp ((s : ℂ) * Complex.I)) t :=
    by fun_prop
  convert! ((SComplex_continuousAt hz).comp
    (f := fun s : ℝ => (x : ℂ) * Complex.exp ((s : ℂ) * Complex.I)) hc).div_const
    (SReal x : ℂ) using 1

/--
@isnad1 id=continuo.2h1v.s5.c57dd2d3f912 from=translated src=- shape=2c15df1c vocab=9399478e
-/
theorem coefficientCenteredChar_continuous {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Continuous (coefficientCenteredChar x) := by
  unfold coefficientCenteredChar
  exact (coefficientChar_continuous hx0 hx1).mul (by fun_prop)

/--
@isnad1 id=lt.4h2v.s6.be1a759631cc from=translated src=- shape=76cd8926 vocab=62026051
-/
theorem coefficientCenteredChar_norm_strict {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    {t : ℝ} (ht0 : 0 < |t|) (htπ : |t| ≤ Real.pi) :
    ‖coefficientCenteredChar x t‖ < 1 := by
  rw [coefficientCenteredChar_norm]
  exact coefficientChar_norm_strict hx0 hx1 ht0 htπ

end PiIrrationality
