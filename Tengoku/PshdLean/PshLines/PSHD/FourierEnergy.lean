import Tengoku.PshdLean.PshLines.PSHD.GaussianEnergy
import Tengoku.PshdLean.PshLines.PSHD.FourierDifference
import Tengoku.PshdLean.PshLines.PSHD.RieszEnergy
import Tengoku.Seed.MeasureTheory.Function.JacobianOneDim
import Tengoku.Seed.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Fourier representation of Riesz energy

The identity `I_s(μ) = b ∫ |μ̂|² |ζ|^{s-d}` used in `pshd-vibe`, Lemma 1.4,
proved by Gaussian subordination of the Riesz kernel.
-/

noncomputable section

open MeasureTheory Set Real
open scoped ENNReal

namespace PshLines.PSHD

/-- The Gamma integral with a positive decay rate, as a lower Lebesgue integral.-/
theorem lintegral_rpow_mul_exp_neg_mul_Ioi {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    ∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ (a - 1) * exp (-(c * t))) =
      ENNReal.ofReal ((1 / c) ^ a * Gamma a) := by
  rw [← integral_rpow_mul_exp_neg_mul_Ioi ha hc, ofReal_integral_eq_lintegral_ofReal]
  · have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := a - 1) (b := c)
      (by linarith) one_pos hc
    simpa [neg_mul, IntegrableOn] using this
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have : 0 < t := ht
    positivity

/-- Without decay the Gamma integrand has infinite integral.-/
theorem lintegral_rpow_Ioi_eq_top {a : ℝ} (ha : 0 < a) :
    ∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ (a - 1)) = ⊤ := by
  by_contra hne
  set L := ∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ (a - 1))
  have hΓ : 0 < Gamma a := Gamma_pos_of_pos ha
  set M : ℝ := L.toReal / Gamma a + 1
  have hM : 0 < M := by positivity
  set c : ℝ := (M ^ a⁻¹)⁻¹
  have hc : 0 < c := by positivity
  have hle : ENNReal.ofReal ((1 / c) ^ a * Gamma a) ≤ L := by
    rw [← lintegral_rpow_mul_exp_neg_mul_Ioi ha hc]
    refine setLIntegral_mono' measurableSet_Ioi fun t ht ↦ ?_
    have ht : 0 < t := ht
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : exp (-(c * t)) ≤ 1 := exp_le_one_iff.mpr (by nlinarith)
    have h2 : 0 ≤ t ^ (a - 1) := by positivity
    nlinarith
  have hpow : (1 / c) ^ a = M := by
    simp only [c, one_div, inv_inv]
    exact rpow_inv_rpow hM.le ha.ne'
  rw [hpow] at hle
  have := (ENNReal.ofReal_le_iff_le_toReal hne).mp hle
  have hlt : L.toReal < M * Gamma a := by
    simp only [M, add_mul, div_mul_cancel₀ _ hΓ.ne']
    linarith
  linarith

/-- The Gamma integral after the substitution `t ↦ t⁻¹`.-/
theorem lintegral_rpow_mul_exp_neg_div_Ioi {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    ∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ (-a - 1) * exp (-(c / t))) =
      ENNReal.ofReal ((1 / c) ^ a * Gamma a) := by
  have himage : (fun x : ℝ ↦ x⁻¹) '' Ioi 0 = Ioi 0 := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact inv_pos.mpr (show (0 : ℝ) < x from hx)
    · intro hy
      exact ⟨y⁻¹, show (0 : ℝ) < y⁻¹ from inv_pos.mpr hy, inv_inv y⟩
  have hderiv : ∀ x ∈ Ioi (0 : ℝ),
      HasDerivWithinAt (fun x : ℝ ↦ x⁻¹) (-(x ^ 2)⁻¹) (Ioi 0) x :=
    fun x hx ↦ (hasDerivAt_inv (ne_of_gt hx)).hasDerivWithinAt
  have hinj : InjOn (fun x : ℝ ↦ x⁻¹) (Ioi 0) := fun x _ y _ h ↦ inv_injective h
  have h := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hderiv hinj
    (fun t ↦ ENNReal.ofReal (t ^ (a - 1) * exp (-(c * t))))
  rw [himage, lintegral_rpow_mul_exp_neg_mul_Ioi ha hc] at h
  rw [h]
  refine setLIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
  have hx : 0 < x := hx
  rw [← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  rw [abs_neg, abs_of_pos (by positivity), inv_rpow hx.le, ← rpow_neg hx.le, div_eq_mul_inv,
    ← mul_assoc, ← rpow_natCast, ← rpow_neg hx.le, ← rpow_add hx]
  congr 2
  push_cast
  ring

/-- Gaussian subordination of the Riesz kernel, including the diagonal value `⊤`.-/
theorem inv_ofReal_rpow_eq_lintegral {s r : ℝ} (hs : 0 < s) (hr : 0 ≤ r) :
    (ENNReal.ofReal r ^ s)⁻¹ =
      ENNReal.ofReal (π ^ (s / 2) / Gamma (s / 2)) *
        ∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ (s / 2 - 1) * exp (-(π * r ^ 2 * t))) := by
  have hs2 : 0 < s / 2 := by positivity
  have hΓ : 0 < Gamma (s / 2) := Gamma_pos_of_pos hs2
  rcases hr.eq_or_lt with rfl | hr
  · simp only [ENNReal.ofReal_zero, ENNReal.zero_rpow_of_pos hs, ENNReal.inv_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_mul,
      neg_zero, exp_zero, mul_one]
    rw [lintegral_rpow_Ioi_eq_top hs2, ENNReal.mul_top]
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  · have hc : 0 < π * r ^ 2 := by positivity
    rw [lintegral_rpow_mul_exp_neg_mul_Ioi hs2 hc, ← ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_rpow_of_pos hr, ← ENNReal.ofReal_inv_of_pos (by positivity)]
    congr 1
    rw [one_div, inv_rpow hc.le, mul_rpow pi_pos.le (by positivity), ← rpow_natCast,
      ← rpow_mul hr.le]
    field_simp
    ring_nf

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

/-- A real Gaussian on a finite-dimensional inner product space is integrable.-/
theorem integrable_exp_neg_mul_sq_norm {b : ℝ} (hb : 0 < b) :
    Integrable (fun ξ : E ↦ exp (-(b * ‖ξ‖ ^ 2))) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := E)
    (b := (b : ℂ)) (by simpa using hb) 0 (0 : E)
  refine h.norm.congr (Filter.Eventually.of_forall fun ξ ↦ ?_)
  simp only [zero_mul, add_zero]
  rw [← Complex.ofReal_pow, ← Complex.ofReal_neg, ← Complex.ofReal_mul, Complex.norm_exp_ofReal]
  ring_nf

/-- Gaussian testing of the difference distribution, expressed through the transform.-/
theorem lintegral_prod_exp_neg_eq (μ : Measure E) [IsFiniteMeasure μ] {t : ℝ} (ht : 0 < t) :
    ∫⁻ p : E × E, ENNReal.ofReal (exp (-(π * ‖p.1 - p.2‖ ^ 2 * t))) ∂μ.prod μ =
      ENNReal.ofReal (t ^ (-(Module.finrank ℝ E / 2 : ℝ))) *
        ∫⁻ ζ, ENNReal.ofReal (‖measureFourier μ ζ‖ ^ 2 * exp (-(π / t * ‖ζ‖ ^ 2))) := by
  set ν := (μ.prod μ).map (fun p : E × E ↦ p.1 - p.2) with hν
  have hbt : 0 < π / t := by positivity
  have hG := integral_measureFourier_mul_gaussian ν (b := ((π / t : ℝ) : ℂ))
    (by simpa using hbt)
  simp only [hν, measureFourier_map_sub] at hG
  rw [← hν] at hG
  have hreal : ∫ ξ, ‖measureFourier μ ξ‖ ^ 2 * exp (-(π / t * ‖ξ‖ ^ 2)) =
      t ^ (Module.finrank ℝ E / 2 : ℝ) * ∫ x, exp (-(π * ‖x‖ ^ 2 * t)) ∂ν := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_mul, ← integral_complex_ofReal, ← integral_complex_ofReal]
    convert hG using 1
    · congr 1
      funext ξ
      push_cast [Complex.ofReal_exp]
      ring_nf
    · rw [← integral_const_mul]
      congr 1
      funext x
      rw [Complex.ofReal_cpow ht.le]
      have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast pi_pos.ne'
      have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
      push_cast [Complex.ofReal_exp]
      congr 1
      · congr 1
        field_simp
      · congr 1
        field_simp
  have hint₁ : Integrable (fun x : E ↦ exp (-(π * ‖x‖ ^ 2 * t))) ν := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) (Filter.Eventually.of_forall fun x ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    exact exp_le_one_iff.mpr (by
      have := mul_nonneg (mul_nonneg pi_pos.le (sq_nonneg ‖x‖)) ht.le
      linarith)
  have hint₂ : Integrable (fun ξ : E ↦ ‖measureFourier μ ξ‖ ^ 2 * exp (-(π / t * ‖ξ‖ ^ 2))) := by
    refine ((integrable_exp_neg_mul_sq_norm hbt).const_mul ((μ.real univ) ^ 2)).mono'
      (by
        have := measurable_measureFourier μ
        fun_prop) (Filter.Eventually.of_forall fun ξ ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    gcongr
    exact norm_measureFourier_le μ ξ
  have hmeas : Measurable (fun p : E × E ↦ p.1 - p.2) := by fun_prop
  rw [← lintegral_map (f := fun x : E ↦ ENNReal.ofReal (exp (-(π * ‖x‖ ^ 2 * t))))
      (by fun_prop) hmeas, ← hν,
    ← ofReal_integral_eq_lintegral_ofReal hint₁ (Filter.Eventually.of_forall fun _ ↦ (exp_pos _).le),
    ← ofReal_integral_eq_lintegral_ofReal hint₂
      (Filter.Eventually.of_forall fun _ ↦ by positivity),
    ← ENNReal.ofReal_mul (by positivity), hreal, ← mul_assoc, ← rpow_add ht]
  simp

/-- The positive constant in the Fourier representation of Riesz energy.-/
def rieszFourierConstant (d s : ℝ) : ℝ :=
  π ^ (s / 2) / Gamma (s / 2) * ((1 / π) ^ ((d - s) / 2) * Gamma ((d - s) / 2))

theorem rieszFourierConstant_pos {d s : ℝ} (hs : 0 < s) (hsd : s < d) :
    0 < rieszFourierConstant d s := by
  have h1 := Gamma_pos_of_pos (show 0 < s / 2 by positivity)
  have h2 := Gamma_pos_of_pos (show 0 < (d - s) / 2 by linarith)
  unfold rieszFourierConstant
  have := pi_pos
  positivity

/-- **Fourier representation of Riesz energy.** For a finite measure on a
finite-dimensional real inner product space of dimension `d` and `0 < s < d`,
`I_s(μ) = b_{d,s} ∫ |μ̂(ζ)|² |ζ|^{s-d} dζ`, including infinite values.-/
theorem rieszEnergy_eq_lintegral_measureFourier (μ : Measure E) [IsFiniteMeasure μ]
    {s : ℝ} (hs : 0 < s) (hsd : s < Module.finrank ℝ E) :
    rieszEnergy s μ =
      ENNReal.ofReal (rieszFourierConstant (Module.finrank ℝ E) s) *
        ∫⁻ ζ, ENNReal.ofReal (‖measureFourier μ ζ‖ ^ 2 * ‖ζ‖ ^ (s - Module.finrank ℝ E)) := by
  set d : ℝ := (Module.finrank ℝ E : ℝ) with hd
  have hdpos : 0 < Module.finrank ℝ E := by
    have : (0 : ℝ) < Module.finrank ℝ E := hs.trans hsd
    exact_mod_cast this
  have : Nontrivial E := Module.nontrivial_of_finrank_pos hdpos
  set K : ℝ := π ^ (s / 2) / Gamma (s / 2)
  have hK : 0 ≤ K := by
    have := Gamma_pos_of_pos (show 0 < s / 2 by positivity)
    have := pi_pos
    positivity
  set a : ℝ := (d - s) / 2
  have ha : 0 < a := by simp only [a]; linarith
  have hfour := measurable_measureFourier μ
  -- Step 1: subordinate the kernel.
  have step1 : rieszEnergy s μ = ENNReal.ofReal K *
      ∫⁻ t in Ioi 0, ∫⁻ p : E × E,
        ENNReal.ofReal (t ^ (s / 2 - 1) * exp (-(π * ‖p.1 - p.2‖ ^ 2 * t))) ∂μ.prod μ := by
    unfold rieszEnergy
    simp_rw [edist_dist, dist_eq_norm]
    simp_rw [inv_ofReal_rpow_eq_lintegral hs (norm_nonneg _)]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    rw [lintegral_lintegral_swap]
    exact (by fun_prop : Measurable fun q : (E × E) × ℝ ↦
      ENNReal.ofReal (q.2 ^ (s / 2 - 1) * exp (-(π * ‖q.1.1 - q.1.2‖ ^ 2 * q.2)))).aemeasurable
  -- Step 2: Gaussian duality for each positive parameter.
  have step2 : ∫⁻ t in Ioi 0, ∫⁻ p : E × E,
        ENNReal.ofReal (t ^ (s / 2 - 1) * exp (-(π * ‖p.1 - p.2‖ ^ 2 * t))) ∂μ.prod μ =
      ∫⁻ t in Ioi 0, ∫⁻ ζ,
        ENNReal.ofReal (t ^ (-a - 1) * exp (-(π * ‖ζ‖ ^ 2 / t)) *
          ‖measureFourier μ ζ‖ ^ 2) := by
    refine setLIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
    have ht : 0 < t := ht
    simp_rw [ENNReal.ofReal_mul (rpow_nonneg ht.le _)]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_prod_exp_neg_eq μ ht,
      ← mul_assoc, ← ENNReal.ofReal_mul (rpow_nonneg ht.le _), ← rpow_add ht,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    funext ζ
    rw [← ENNReal.ofReal_mul (rpow_nonneg ht.le _)]
    congr 1
    have hexp : -(π / t * ‖ζ‖ ^ 2) = -(π * ‖ζ‖ ^ 2 / t) := by ring
    rw [hexp]
    have hpow : s / 2 - 1 + -(d / 2) = -a - 1 := by simp only [a]; ring
    rw [hpow]
    ring
  -- Step 3: exchange and evaluate the inverted Gamma integral.
  have step3 : ∫⁻ t in Ioi 0, ∫⁻ ζ,
        ENNReal.ofReal (t ^ (-a - 1) * exp (-(π * ‖ζ‖ ^ 2 / t)) *
          ‖measureFourier μ ζ‖ ^ 2) =
      ∫⁻ ζ, ENNReal.ofReal ((1 / π) ^ a * Gamma a) *
        ENNReal.ofReal (‖measureFourier μ ζ‖ ^ 2 * ‖ζ‖ ^ (s - d)) := by
    rw [lintegral_lintegral_swap (by
      exact (by fun_prop : Measurable fun q : ℝ × E ↦
        ENNReal.ofReal (q.1 ^ (-a - 1) * exp (-(π * ‖q.2‖ ^ 2 / q.1)) *
          ‖measureFourier μ q.2‖ ^ 2)).aemeasurable)]
    have hne : ∀ᵐ ζ : E ∂volume, ζ ≠ 0 := by
      simp [ae_iff, measure_singleton]
    refine lintegral_congr_ae (hne.mono fun ζ hζ ↦ ?_)
    have hζ : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ
    have hc : 0 < π * ‖ζ‖ ^ 2 := by positivity
    simp_rw [ENNReal.ofReal_mul' (sq_nonneg ‖measureFourier μ ζ‖)]
    rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, lintegral_rpow_mul_exp_neg_div_Ioi ha hc,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hpow : (1 / (π * ‖ζ‖ ^ 2)) ^ a = (1 / π) ^ a * ‖ζ‖ ^ (s - d) := by
      rw [one_div, mul_inv, mul_rpow (by positivity) (by positivity), ← one_div,
        inv_rpow (by positivity), ← rpow_natCast, ← rpow_mul hζ.le, ← rpow_neg hζ.le]
      congr 2
      simp only [a]
      push_cast
      ring
    rw [hpow]
    ring
  rw [step1, step2, step3, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc,
    ← ENNReal.ofReal_mul hK]
  rfl

end PshLines.PSHD
