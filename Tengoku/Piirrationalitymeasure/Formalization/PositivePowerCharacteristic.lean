import Tengoku.Piirrationalitymeasure.Formalization.PositivePowerMoments
import Tengoku.Piirrationalitymeasure.Formalization.CoefficientCharacteristic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Characteristic functions and strict aperiodicity for arbitrary positive powers. -/

namespace PiIrrationality.PositivePower

open MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable def characteristic (u v d : ℕ) (x t : ℝ) : ℂ :=
  complexValue u v d ((x : ℂ) * Complex.exp ((t : ℂ) * Complex.I)) /
    (realValue u v d x : ℂ)

noncomputable def centeredCharacteristic (u v d : ℕ) (x t : ℝ) : ℂ :=
  characteristic u v d x t * Complex.exp (((-mean u v d x * t : ℝ) : ℂ) * Complex.I)

variable (u v : ℕ) {d : ℕ} (hd : 0 < d)

include hd in
/--
@isnad1 id=hassum.3h6v.s6.93a25093870e from=translated src=- shape=9678eacc vocab=3bd9a162
-/
theorem probability_fourier_sum {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (n : ℕ) (t : ℝ) :
    HasSum (fun k => (probability u v d x n k : ℂ) *
      Complex.exp ((k : ℂ) * (t : ℂ) * Complex.I)) (characteristic u v d x t ^ n) := by
  have hz : ‖(x : ℂ) * Complex.exp ((t : ℂ) * Complex.I)‖ < 1 := by
    rwa [coefficient_circle_norm hx0]
  have h := (ratSeries_hasSum_pow (series_hasSum u v hd hz) n).div_const
    ((realValue u v d x ^ n : ℝ) : ℂ)
  convert! h using 1
  · ext k
    have he : Complex.exp ((k : ℂ) * (t : ℂ) * Complex.I) =
        Complex.exp ((t : ℂ) * Complex.I) ^ k := by
      rw [mul_assoc, Complex.exp_nat_mul]
    rw [he]
    simp only [probability, Complex.ofReal_div, Complex.ofReal_mul,
      Complex.ofReal_pow, Complex.ofReal_ratCast, mul_pow]
    ring
  · simp only [characteristic, complexValue, PComplex, div_pow, Complex.ofReal_pow]

/--
@isnad1 id=eq.3h6v.s6.f06e04b82f1d from=translated src=- shape=be9c9fac vocab=358870f9
-/
theorem law_charFun {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (n : ℕ) (t : ℝ) :
    charFun ((law u v hd x hx0 hx1 n).toMeasure.map (fun k : ℕ => (k : ℝ))) t =
      characteristic u v d x t ^ n := by
  rw [charFun_apply_real, integral_map (by fun_prop) (by fun_prop)]
  simp only [Complex.ofReal_natCast]
  rw [PMF.integral_eq_tsum _ _ (pmf_nat_integrable_cexp _ t)]
  convert! (probability_fourier_sum u v hd hx0 hx1 n t).tsum_eq using 1
  apply tsum_congr
  intro k
  simp only [law_toReal, RCLike.real_smul_eq_coe_mul, mul_comm (t : ℂ)]
  rfl

/--
@isnad1 id=eq.3h5v.s6.3eb28239cbec from=translated src=- shape=7f19d008 vocab=12e89991
-/
theorem law_centered_charFun {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (t : ℝ) :
    charFun ((law u v hd x hx0 hx1 1).toMeasure.map
      (fun k : ℕ => (k : ℝ) - mean u v d x)) t = centeredCharacteristic u v d x t := by
  have hf : (fun k : ℕ => (k : ℝ) - mean u v d x) =
      (fun y : ℝ => y + (-mean u v d x)) ∘ (fun k : ℕ => (k : ℝ)) := by
    ext k
    simp [sub_eq_add_neg]
  rw [hf, ← Measure.map_map (by fun_prop) (by fun_prop), charFun_map_add_const,
    law_charFun u v hd hx0 hx1, pow_one]
  simp only [centeredCharacteristic, RCLike.inner_apply, conj_trivial,
    mul_comm t (-mean u v d x)]

/--
@isnad1 id=eq.0h5v.s4.82bfe25de9d5 from=translated src=- shape=e427bb6e vocab=a6a52200
-/
theorem centeredCharacteristic_norm (x t : ℝ) :
    ‖centeredCharacteristic u v d x t‖ = ‖characteristic u v d x t‖ := by
  simp only [centeredCharacteristic, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

include hd in
/--
@isnad1 id=lt.5h5v.s6.ff24003c74c2 from=translated src=- shape=9f52d341 vocab=5d0f151b
-/
theorem characteristic_norm_strict {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    {t : ℝ} (ht0 : 0 < |t|) (htπ : |t| ≤ Real.pi) :
    ‖characteristic u v d x t‖ < 1 := by
  have hz : ‖(x : ℂ) * Complex.exp ((t : ℂ) * Complex.I)‖ < 1 := by
    rwa [coefficient_circle_norm hx0.le]
  have hne : (x : ℂ) * Complex.exp ((t : ℂ) * Complex.I) ≠ (x : ℂ) := by
    intro heq
    apply exp_mul_I_ne_one ht0 htπ
    apply mul_left_cancel₀ (show (x : ℂ) ≠ 0 by exact_mod_cast hx0.ne')
    simpa only [mul_one] using heq
  have hs := complexValue_norm_strict u v hd hz
    (by simpa only [coefficient_circle_norm hx0.le] using hne)
  rw [coefficient_circle_norm hx0.le] at hs
  simpa only [characteristic, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (realValue_pos u v d hx0.le hx1),
    div_lt_one (realValue_pos u v d hx0.le hx1)] using hs

/--
@isnad1 id=continuo.2h4v.s5.6b7e8bd76d59 from=translated src=- shape=19ade655 vocab=4471ece1
-/
theorem characteristic_continuous {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Continuous (characteristic u v d x) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hz : ‖(x : ℂ) * Complex.exp ((t : ℂ) * Complex.I)‖ < 1 := by
    rwa [coefficient_circle_norm hx0]
  have hc : ContinuousAt (fun s : ℝ => (x : ℂ) * Complex.exp ((s : ℂ) * Complex.I)) t :=
    by fun_prop
  convert! ((complexValue_continuousAt u v d hz).comp
    (f := fun s : ℝ => (x : ℂ) * Complex.exp ((s : ℂ) * Complex.I)) hc).div_const
    (realValue u v d x : ℂ) using 1

/--
@isnad1 id=continuo.2h4v.s5.3950769e937d from=translated src=- shape=19ade655 vocab=3a5b9ced
-/
theorem centeredCharacteristic_continuous {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Continuous (centeredCharacteristic u v d x) := by
  unfold centeredCharacteristic
  exact (characteristic_continuous u v hx0 hx1).mul (by fun_prop)

include hd in
/--
@isnad1 id=lt.5h5v.s6.63da2a0d9c70 from=translated src=- shape=9f52d341 vocab=5be8d558
-/
theorem centeredCharacteristic_norm_strict {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    {t : ℝ} (ht0 : 0 < |t|) (htπ : |t| ≤ Real.pi) :
    ‖centeredCharacteristic u v d x t‖ < 1 := by
  rw [centeredCharacteristic_norm]
  exact characteristic_norm_strict u v hd hx0 hx1 ht0 htπ

end PiIrrationality.PositivePower
