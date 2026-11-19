import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.CanonicalScaleAtoms
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.OscillatoryReductionL1

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exact integration and oscillatory recombination of canonical scale slices

Disjoint spatial scales give equality of the total absolute integral, not
just a bound. The resulting genuine Bochner interchange is specialized to
each dyadic height, each finite low-height kernel, and the all-height action.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace QuadraticCarleson
namespace CanonicalScaleAtoms

open CalderonZygmundDyadicStopping CalderonZygmundStoppingIntervals
open PositiveLowFullEstimate OscillatoryReduction LowKernelLevelSummation

/-- Exact kernel-weighted mass packing across scales, valid without a
finiteness hypothesis.
@isnad1 id=eq.2h4v.s7.11eda687b53d from=translated src=- shape=53f42477 vocab=8c44798e
-/
theorem tsum_lintegral_enorm_kernel_mul_scale
    {A : ℕ → ℝ} {f K : ℝ → ℂ} (hf : Measurable f) (hK : Measurable K) (k : ℕ) :
    (∑' j : ℤ, ∫⁻ y, ‖K y * stoppingScaleLevelBadPart A f j k y‖ₑ) =
      ∫⁻ y, ‖K y * canonicalLevelBadPart A f k y‖ₑ := by
  rw [← lintegral_tsum
    (f := fun j : ℤ ↦ fun y ↦ ‖K y * stoppingScaleLevelBadPart A f j k y‖ₑ) (fun j ↦
    (hK.mul (measurable_stoppingScaleLevelBadPart hf j k)).enorm.aemeasurable)]
  simp only [enorm_mul, ENNReal.tsum_mul_left, tsum_enorm_stoppingScaleLevelBadPart]

/-- A precise Bochner interchange rule. Its sole integrability requirement
is on the actual combined input, and all concrete kernels below discharge it.
@isnad1 id=eq.3h4v.s7.f83a140ecb92 from=translated src=- shape=2a57d022 vocab=8bcc65dd
-/
theorem integral_kernel_mul_canonicalLevelBadPart_eq_tsum
    {A : ℕ → ℝ} {f K : ℝ → ℂ} (hf : Measurable f) (hK : Measurable K) (k : ℕ)
    (hKi : Integrable (fun y ↦ K y * canonicalLevelBadPart A f k y)) :
    (∫ y, K y * canonicalLevelBadPart A f k y) =
      ∑' j : ℤ, ∫ y, K y * stoppingScaleLevelBadPart A f j k y := by
  have hs : (∑' j : ℤ, ∫⁻ y, ‖K y * stoppingScaleLevelBadPart A f j k y‖ₑ) ≠ ∞ := by
    rw [tsum_lintegral_enorm_kernel_mul_scale hf hK k]
    exact hKi.hasFiniteIntegral.ne
  rw [← integral_tsum
    (f := fun j : ℤ ↦ fun y ↦ K y * stoppingScaleLevelBadPart A f j k y) (fun j ↦
    (hK.mul (measurable_stoppingScaleLevelBadPart hf j k)).aestronglyMeasurable) hs]
  apply integral_congr_ae
  filter_upwards with y
  rw [tsum_mul_left, tsum_stoppingScaleLevelBadPart]

/--
@isnad1 id=eq.3h3v.s7.cac10aff3b95 from=translated src=- shape=801d3711 vocab=8ada6b25
-/
theorem integral_canonicalLevelBadPart_eq_tsum_scale
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    {k : ℕ} (hAk : 0 ≤ A k) :
    (∫ y, canonicalLevelBadPart A f k y) =
      ∑' j : ℤ, ∫ y, stoppingScaleLevelBadPart A f j k y := by
  simpa only [one_mul] using integral_kernel_mul_canonicalLevelBadPart_eq_tsum
    (K := fun _ ↦ 1) hf measurable_const k
    (by simpa only [one_mul] using integrable_canonicalLevelBadPart hf hfi hAk)

/--
@isnad1 id=eq.4h6v.s8.a987f2e1cac8 from=translated src=- shape=2a357bda vocab=fe2cc869
-/
theorem integral_fixedHeight_canonicalLevelBadPart_eq_tsum_scale
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    {k : ℕ} (hAk : 0 ≤ A k) (r : ℕ) (lam : ℝ) (hlam : lam ≠ 0) (x : ℝ) :
    (∫ t, canonicalLevelBadPart A f k (x-t) *
      (dyadicPsi (oscillatoryScaleIndex lam r hlam) t : ℂ) * phase (lam*t^2)) =
      ∑' j : ℤ, ∫ t, stoppingScaleLevelBadPart A f j k (x-t) *
        (dyadicPsi (oscillatoryScaleIndex lam r hlam) t : ℂ) * phase (lam*t^2) := by
  have hK : Measurable (fun y ↦ fixedHeightQuadraticKernel lam r hlam (x-y)) := by
    unfold fixedHeightQuadraticKernel
    apply Measurable.mul
    · exact Complex.measurable_ofReal.comp
        ((dyadicPsi_smooth _).continuous.measurable.comp (measurable_const.sub measurable_id))
    · unfold phase
      fun_prop
  have hi := integral_kernel_mul_canonicalLevelBadPart_eq_tsum hf hK k
    (integrable_fixedHeightQuadraticKernel_mul_locallyIntegrable
      (integrable_canonicalLevelBadPart hf hfi hAk).locallyIntegrable r lam hlam x)
  simpa only [fixedHeightQuadraticKernel_integral_eq_paper] using hi

/--
@isnad1 id=eq.4h6v.s7.1d3af075ccab from=translated src=- shape=16937014 vocab=ded5a45a
-/
theorem integral_paperLowCZKernel_canonicalLevelBadPart_eq_tsum_scale
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    {k : ℕ} (hAk : 0 ≤ A k) (B : ℕ) (lam : ℝ) (hlam : lam ≠ 0) (x : ℝ) :
    (∫ y, paperLowCZKernel lam hlam B x y * canonicalLevelBadPart A f k y) =
      ∑' j : ℤ, ∫ y, paperLowCZKernel lam hlam B x y * stoppingScaleLevelBadPart A f j k y := by
  have hK : Measurable (fun y ↦ paperLowCZKernel lam hlam B x y) :=
    (continuous_paperLowOscillatoryKernel hlam B).measurable.comp
      (measurable_const.sub measurable_id)
  exact integral_kernel_mul_canonicalLevelBadPart_eq_tsum hf hK k
    ((integrable_canonicalLevelBadPart hf hfi hAk).bdd_mul hK.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y ↦ paperLowOscillatoryKernel_norm_le_global hlam B (x-y)))

/-- Exact all-height action recombination at every point and every nonzero
real modulation, including every dyadic lacunary modulation.
@isnad1 id=eq.4h5v.s6.c4a0d683d8ff from=translated src=- shape=88b4a8d1 vocab=59b250ee
-/
theorem paperOscillatoryAction_canonicalLevelBadPart_eq_tsum_scale
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    {k : ℕ} (hAk : 0 ≤ A k) (lam : ℝ) (hlam : lam ≠ 0) (x : ℝ) :
    paperOscillatoryAction lam hlam (canonicalLevelBadPart A f k) x =
      ∑' j : ℤ, paperOscillatoryAction lam hlam (stoppingScaleLevelBadPart A f j k) x := by
  rw [paperOscillatoryAction_eq_integral_of_integrable lam hlam
    (integrable_canonicalLevelBadPart hf hfi hAk)]
  simp_rw [paperOscillatoryAction_eq_integral_of_integrable lam hlam
    (integrable_stoppingScaleLevelBadPart hf hfi _ hAk)]
  exact integral_kernel_mul_canonicalLevelBadPart_eq_tsum hf
    ((measurable_highPassKernel lam hlam).comp (measurable_const.sub measurable_id)) k
    (integrable_highPassKernel_mul lam hlam (integrable_canonicalLevelBadPart hf hfi hAk) x)

end CanonicalScaleAtoms
end QuadraticCarleson
