module

public import Tengoku

public section

open MeasureTheory

-- Upstreaming status: looks ready for upstreaming; pay attention to the correct file to move to!

-- Put after `setIntegral_re_add_im`

/--
@isnad1 id=eq.0h4v.s7.0e9bc8f757e6 from=translated src=- shape=e1e7e9e4 vocab=1a35bfa1
-/
lemma starRingEnd_div_mul_eq_norm {α 𝕜 : Type*} [RCLike 𝕜] {f : α → 𝕜} (x : α) :
    starRingEnd 𝕜 (f x / ‖f x‖) * f x = ‖f x‖ := by
  simp only [div_eq_inv_mul, map_mul, map_inv₀, RCLike.conj_ofReal, mul_assoc, RCLike.conj_mul]
  norm_cast
  rcases eq_or_ne (‖f x‖) 0 with hx | hx
  · simp [hx]
  · field_simp

-- move to Mathlib.Analysis.Normed.Module.Basic, next to nnnorm_algebraMap'
/--
@isnad1 id=eq.0h3v.s7.60f04e35f7c8 from=translated src=- shape=83faff20 vocab=e07bf56e
-/
lemma enorm_algebraMap' {𝕜 : Type*} (𝕜' : Type*) [NormedField 𝕜] [SeminormedRing 𝕜']
    [NormedAlgebra 𝕜 𝕜'] [NormOneClass 𝕜'] (x : 𝕜) : ‖(algebraMap 𝕜 𝕜') x‖ₑ = ‖x‖ₑ := by
  simp [enorm_eq_nnnorm]

/--
@isnad1 id=eq.1h4v.s7.0ac05295cd53 from=translated src=- shape=8d2d666a vocab=c1520e40
-/
lemma enorm_integral_norm_eq_integral_enorm {α 𝕜 : Type*} [MeasurableSpace α] [RCLike 𝕜]
    {μ : Measure α} {f : α → 𝕜} (hf : Integrable f μ) : ‖∫ x, ‖f x‖ ∂μ‖ₑ = ∫⁻ x, ‖f x‖ₑ ∂μ := by
  simp_rw [enorm_eq_nnnorm]
  rw [lintegral_coe_eq_integral]
  · simp only [coe_nnnorm, ENNReal.ofReal, ENNReal.coe_inj]
    have : |∫ (a : α), ‖f a‖ ∂μ| = ∫ (a : α), ‖f a‖ ∂μ :=
      abs_eq_self.2 (integral_nonneg (fun _ ↦ by positivity))
    aesop
  · simpa only [coe_nnnorm] using hf.norm

/--
@isnad1 id=eq.1h4v.s8.26354b933f57 from=translated src=- shape=50f4b215 vocab=b3daf716
-/
lemma enorm_integral_starRingEnd_mul_eq_lintegral_enorm
    {𝕜 : Type*} [RCLike 𝕜] {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → 𝕜}
    (hf : Integrable f μ) :
    ‖∫ x, starRingEnd 𝕜 (f x / ‖f x‖) * f x ∂μ‖ₑ = ∫⁻ x, ‖f x‖ₑ ∂μ := by
  simp_rw [starRingEnd_div_mul_eq_norm, integral_ofReal, enorm_algebraMap',
    enorm_integral_norm_eq_integral_enorm hf]

/--
@isnad1 id=eq.0h5v.s8.dab251c3c4ef from=translated src=- shape=39661136 vocab=fb191c27
-/
lemma enorm_integral_mul_starRingEnd_comm
    {𝕜 : Type*} [RCLike 𝕜] {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → 𝕜} :
    ‖∫ x, f x * starRingEnd 𝕜 (g x) ∂μ‖ₑ = ‖∫ x, g x * starRingEnd 𝕜 (f x) ∂μ‖ₑ := by
  rw [← RCLike.enorm_conj, ← integral_conj]; congr! 3; simp [mul_comm]

-- Like this it fits copy-paste next to setIntegral_union
section SetIntegral_Union_2

variable {X E : Type*} [MeasurableSpace X]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f : X → E} {s t : Set X} {μ : Measure X}

/--
@isnad1 id=eq.3h6v.s7.6c7835f55440 from=translated src=- shape=f2ac109f vocab=cb85503b
-/
theorem MeasureTheory.setIntegral_union_2
    (hst : Disjoint s t) (ht : MeasurableSet t) (hfst : IntegrableOn f (s ∪ t) μ) :
    ∫ x in s ∪ t, f x ∂μ = ∫ x in s, f x ∂μ + ∫ x in t, f x ∂μ :=
  setIntegral_union hst ht hfst.left_of_union hfst.right_of_union

end SetIntegral_Union_2
