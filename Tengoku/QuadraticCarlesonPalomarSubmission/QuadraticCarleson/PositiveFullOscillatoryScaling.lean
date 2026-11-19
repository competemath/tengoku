import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.PositiveFullOscillatoryEndpoint

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Arbitrary positive thresholds for the full oscillatory endpoint

Genuine scalar homogeneity of the proved oscillatory action reduces the
threshold `α > 0` to the normalized theorem, with the exact source modular
`∫ (|f|/α) log₁(|f|/α)` and the same universal constant.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace QuadraticCarleson
namespace PositiveFullOscillatoryEndpoint

open OscillatoryReduction

/-- Complex scalar homogeneity of the actual height series, proved through
its established L¹ high-pass integral representation.
@isnad1 id=eq.2h4v.s6.8ee9bad46e68 from=translated src=- shape=b8446426 vocab=452e4c5c
-/
theorem paperOscillatoryAction_const_mul (lam : ℝ) (hlam : lam ≠ 0)
    {f : ℝ → ℂ} (hf : Integrable f) (c : ℂ) (x : ℝ) :
    paperOscillatoryAction lam hlam (fun y ↦ c * f y) x =
      c * paperOscillatoryAction lam hlam f x := by
  rw [paperOscillatoryAction_eq_integral_of_integrable lam hlam (hf.const_mul c),
    paperOscillatoryAction_eq_integral_of_integrable lam hlam hf,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  ring

/-- The unrestricted nonzero-real modulation supremum is genuinely
homogeneous; no measurability of the supremum is needed for this identity.
@isnad1 id=eq.1h3v.s6.872c44ae144b from=translated src=- shape=db620ef1 vocab=01cd53c2
-/
theorem paperOscillatoryMaximal_const_mul {f : ℝ → ℂ} (hf : Integrable f)
    (c : ℂ) (x : ℝ) :
    paperOscillatoryMaximal (fun y ↦ c * f y) x = ‖c‖ₑ * paperOscillatoryMaximal f x := by
  unfold paperOscillatoryMaximal
  simp_rw [paperOscillatoryAction_const_mul _ _ hf, enorm_mul]
  exact (ENNReal.mul_iSup _ _).symm

noncomputable def normalizedOscillatoryInput (α : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (α : ℂ)⁻¹ * f x

/--
@isnad1 id=measurab.1h2v.s4.9ae06072b7fa from=translated src=- shape=dae56b0c vocab=20f476fb
-/
theorem measurable_normalizedOscillatoryInput {f : ℝ → ℂ} (hf : Measurable f) (α : ℝ) :
    Measurable (normalizedOscillatoryInput α f) := measurable_const.mul hf

/--
@isnad1 id=integrab.1h2v.s6.544a662beb4c from=translated src=- shape=e31b38b5 vocab=26df64f9
-/
theorem integrable_normalizedOscillatoryInput {f : ℝ → ℂ} (hf : Integrable f) (α : ℝ) :
    Integrable (normalizedOscillatoryInput α f) := hf.const_mul _

/--
@isnad1 id=eq.1h3v.s5.8fafe082cff6 from=translated src=- shape=7558a819 vocab=d084e423
-/
theorem norm_normalizedOscillatoryInput {α : ℝ} (hα : 0 < α) (f : ℝ → ℂ) (x : ℝ) :
    ‖normalizedOscillatoryInput α f x‖ = ‖f x‖ / α := by
  simp only [normalizedOscillatoryInput, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hα]
  ring

/--
@isnad1 id=eq.2h3v.s6.f3287e067a3c from=translated src=- shape=d7ac4dc9 vocab=55309012
-/
theorem paperOscillatoryMaximal_normalizedInput {α : ℝ} (hα : 0 < α)
    {f : ℝ → ℂ} (hf : Integrable f) (x : ℝ) :
    paperOscillatoryMaximal (normalizedOscillatoryInput α f) x =
      paperOscillatoryMaximal f x / ENNReal.ofReal α := by
  change paperOscillatoryMaximal (fun y ↦ (α : ℂ)⁻¹ * f y) x = _
  rw [paperOscillatoryMaximal_const_mul hf]
  have hc : ‖(α : ℂ)⁻¹‖ₑ = (ENNReal.ofReal α)⁻¹ := by
    rw [← ofReal_norm, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hα,
      ENNReal.ofReal_inv_of_pos hα]
  rw [hc, div_eq_mul_inv, mul_comm]

/--
@isnad1 id=eq.2h2v.s6.f0c50860a609 from=translated src=- shape=55e6b4c6 vocab=005a7555
-/
theorem oscillatory_levelSet_eq_normalized {α : ℝ} (hα : 0 < α)
    {f : ℝ → ℂ} (hf : Integrable f) :
    {x | ENNReal.ofReal α < paperOscillatoryMaximal f x} =
      {x | 1 < paperOscillatoryMaximal (normalizedOscillatoryInput α f) x} := by
  ext x
  change ENNReal.ofReal α < paperOscillatoryMaximal f x ↔
    1 < paperOscillatoryMaximal (normalizedOscillatoryInput α f) x
  rw [paperOscillatoryMaximal_normalizedInput hα hf]
  simpa only [one_mul] using (ENNReal.lt_div_iff_mul_lt
    (a := paperOscillatoryMaximal f x) (b := ENNReal.ofReal α) (c := 1)
    (Or.inl (ENNReal.ofReal_pos.mpr hα).ne') (Or.inl ENNReal.ofReal_ne_top)).symm

/-- The full-real oscillatory endpoint in the source's exact arbitrary-
threshold form, with the same explicit universal constant.
@isnad1 id=le.3h2v.s7.ed58a64add91 from=translated src=- shape=2a621834 vocab=47959990
-/
theorem paperOscillatoryMaximal_levelSet_le_scaled_orlicz
    {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f) {α : ℝ} (hα : 0 < α) :
    volume {x | ENNReal.ofReal α < paperOscillatoryMaximal f x} ≤
      fullOscillatoryEndpointConstant * ∫⁻ x,
        ENNReal.ofReal ((‖f x‖ / α) * paperLog 1 (‖f x‖ / α)) := by
  have h := paperOscillatoryMaximal_levelSet_le_orlicz
    (measurable_normalizedOscillatoryInput hf α) (integrable_normalizedOscillatoryInput hfi α)
  rw [← oscillatory_levelSet_eq_normalized hα hfi] at h
  simpa only [norm_normalizedOscillatoryInput hα] using h

/--
@isnad1 id=le.1h2v.s6.926d3c647995 from=translated src=- shape=ddaba646 vocab=d6cf1636
-/
theorem paperOscillatoryMaximal_L0Infinity_levelSet_le_scaled_orlicz
    (f : L0Infinity) {α : ℝ} (hα : 0 < α) :
    volume {x | ENNReal.ofReal α < paperOscillatoryMaximal f x} ≤
      fullOscillatoryEndpointConstant * ∫⁻ x,
        ENNReal.ofReal ((‖f x‖ / α) * paperLog 1 (‖f x‖ / α)) :=
  paperOscillatoryMaximal_levelSet_le_scaled_orlicz f.measurable_toFun f.integrable hα

end PositiveFullOscillatoryEndpoint
end QuadraticCarleson
