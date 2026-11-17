import Tengoku.SingularityCompleteLean.Singularity.L2Convolution

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The L¹–L² convolution multiplier theorem

We prove the multiplier identity for the Bochner convolution operator. Fubini is
justified by the product of the L¹ kernel norm and an L¹ inner-product density.
-/

noncomputable section
open MeasureTheory
open scoped FourierTransform

namespace Singularity

/-- The ordinary Fourier transform of an L¹ kernel is continuous.
@isnad1 id=continuo.1h1v.s6.b5be480c5420 from=translated src=- shape=24873076 vocab=9e444e7d
-/
theorem integrable_fourier_continuous {k : ℝ → ℂ} (hk : Integrable k) : Continuous (𝓕 k) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ hk

/-- Its uniform bound.
@isnad1 id=le.1h2v.s6.36277e3de833 from=translated src=- shape=1d1deb45 vocab=3dc1e545
-/
theorem integrable_fourier_norm_le {k : ℝ → ℂ} (_hk : Integrable k) (ξ : ℝ) :
    ‖𝓕 k ξ‖ ≤ ∫ t, ‖k t‖ := by
  rw [Real.fourier_real_eq]
  apply (norm_integral_le_integral_norm _).trans_eq
  simp only [Circle.norm_smul]

/-- The Fourier transform of the kernel as an L-infinity multiplier.-/
def fourierKernelLinf (k : ℝ → ℂ) (hk : Integrable k) : Lp ℂ ⊤ (volume : Measure ℝ) :=
  (memLp_top_of_bound (integrable_fourier_continuous hk).aestronglyMeasurable (∫ t, ‖k t‖)
    (Filter.Eventually.of_forall (integrable_fourier_norm_le hk))).toLp (𝓕 k)

/-- The bounded Fourier multiplier on L².-/
def fourierKernelMultiplier (k : ℝ → ℂ) (hk : Integrable k) : RealLineL2 →L[ℂ] RealLineL2 :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL volume ⊤ 2 2 (fourierKernelLinf k hk)

/--
@isnad1 id=eventual.1h2v.s12.bea5c394ba41 from=translated src=- shape=c86c25af vocab=90fd3c7e
-/
theorem fourierKernelMultiplier_apply_ae (k : ℝ → ℂ) (hk : Integrable k) (f : RealLineL2) :
    (fourierKernelMultiplier k hk f : ℝ → ℂ) =ᵐ[volume] fun ξ => 𝓕 k ξ * f ξ := by
  have hm : (fourierKernelLinf k hk : ℝ → ℂ) =ᵐ[volume] 𝓕 k := MemLp.coeFn_toLp _
  filter_upwards [(ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2) (fourierKernelLinf k hk) f,
    hm] with ξ hξ hmξ
  exact hξ.trans (by rw [hmξ]; rfl)

/-- Joint continuity of the scalar phase.
@isnad1 id=continuo.0h0v.s5.69eb779f6460 from=translated src=- shape=e37279c3 vocab=94899f6f
-/
theorem translationPhase_joint_continuous : Continuous (fun p : ℝ × ℝ => translationPhase p.1 p.2) :=
  continuous_subtype_val.comp (Real.continuous_fourierChar.comp
    (continuous_fst.neg.mul continuous_snd))

/-- Integrability of the family of modulated vectors.
@isnad1 id=integrab.1h2v.s13.dcb01e28ae81 from=translated src=- shape=1bed32fb vocab=b25d28f5
-/
theorem modulationL2_integrable {k : ℝ → ℂ} (hk : Integrable k) (g : RealLineL2) :
    Integrable (fun t => k t • frequencyModulation t g) := by
  have h := (Lp.fourierTransformₗᵢ ℝ ℂ).toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp
    (convolutionL2_integrable hk ((Lp.fourierTransformₗᵢ ℝ ℂ).symm g))
  simpa only [ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    Function.comp_def, map_smul, fourier_realTranslation, LinearIsometryEquiv.apply_symm_apply] using h

/-- The weak scalar formula for a modulated L² vector.
@isnad1 id=eq.0h3v.s12.b75753fc54bc from=translated src=- shape=223106b9 vocab=750c2b71
-/
theorem modulationL2_inner (a : ℝ) (h g : RealLineL2) :
    inner ℂ h (frequencyModulation a g) =
      ∫ ξ, translationPhase a ξ * inner ℂ (h ξ) (g ξ) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [frequencyModulation_apply_ae a g] with ξ hξ
  rw [hξ]
  exact inner_smul_right _ _ _

/-- Absolute integrability of the double integral used in the multiplier proof.
@isnad1 id=integrab.1h3v.s10.97bf7702c5cd from=translated src=- shape=8cbd9854 vocab=f2909d60
-/
theorem multiplier_fubini_integrable {k : ℝ → ℂ} (hk : Integrable k) (h g : RealLineL2) :
    Integrable (fun p : ℝ × ℝ => k p.1 * translationPhase p.1 p.2 * inner ℂ (h p.2) (g p.2))
      (volume.prod volume) := by
  apply (hk.norm.mul_prod (L2.integrable_inner (𝕜 := ℂ) h g).norm).mono'
  · exact (hk.aestronglyMeasurable.comp_fst.mul
      translationPhase_joint_continuous.aestronglyMeasurable).mul
        (L2.integrable_inner (𝕜 := ℂ) h g).aestronglyMeasurable.comp_snd
  · exact Filter.Eventually.of_forall (fun p => by
      simp only [norm_mul, translationPhase_norm, mul_one, le_refl])

/-- Integrating the modulation phase gives the ordinary Fourier transform.
@isnad1 id=eq.0h2v.s6.780b5a82bae3 from=translated src=- shape=f11f87a0 vocab=3b76ab76
-/
theorem integral_kernel_phase (k : ℝ → ℂ) (ξ : ℝ) :
    ∫ t, k t * translationPhase t ξ = 𝓕 k ξ := by
  rw [Real.fourier_real_eq]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => by
    simp [translationPhase, Circle.smul_def, mul_comm])

/-- The Bochner integral of modulated vectors is multiplication by the
ordinary Fourier transform of the kernel.
@isnad1 id=eq.1h2v.s14.3d9821750874 from=translated src=- shape=c3217d89 vocab=f15fb795
-/
theorem integral_modulation_eq_multiplier (k : ℝ → ℂ) (hk : Integrable k) (g : RealLineL2) :
    (∫ t, k t • frequencyModulation t g) = fourierKernelMultiplier k hk g := by
  apply ext_inner_left ℂ
  intro h
  rw [← integral_inner (modulationL2_integrable hk g)]
  simp_rw [inner_smul_right, modulationL2_inner, ← integral_const_mul]
  have hfub := integral_integral_swap
    (f := fun t ξ : ℝ => k t * translationPhase t ξ * inner ℂ (h ξ) (g ξ))
    (multiplier_fubini_integrable hk h g)
  calc
    ∫ t, ∫ ξ, k t * (translationPhase t ξ * inner ℂ (h ξ) (g ξ)) =
        ∫ ξ, ∫ t, (k t * translationPhase t ξ) * inner ℂ (h ξ) (g ξ) := by
      simpa only [mul_assoc] using hfub
    _ = ∫ ξ, 𝓕 k ξ * inner ℂ (h ξ) (g ξ) := by
      simp_rw [integral_mul_const, integral_kernel_phase]
    _ = inner ℂ h (fourierKernelMultiplier k hk g) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [fourierKernelMultiplier_apply_ae k hk g] with ξ hξ
      rw [hξ]
      exact (inner_smul_right _ _ _).symm

/-- Fourier diagonalization of convolution on all of L².
@isnad1 id=eq.1h2v.s14.887a7c018bee from=translated src=- shape=5cebdb7c vocab=b59fdaf7
-/
theorem fourier_convolutionL2 (k : ℝ → ℂ) (hk : Integrable k) (f : RealLineL2) :
    Lp.fourierTransformₗᵢ ℝ ℂ (convolutionL2 k hk f) =
      fourierKernelMultiplier k hk (Lp.fourierTransformₗᵢ ℝ ℂ f) := by
  rw [fourier_convolutionL2_integral, integral_modulation_eq_multiplier]

/-- The representative-level multiplier identity is almost everywhere.
@isnad1 id=eventual.1h2v.s14.24510852a82a from=translated src=- shape=96af9688 vocab=50029e3f
-/
theorem fourier_convolutionL2_ae (k : ℝ → ℂ) (hk : Integrable k) (f : RealLineL2) :
    (Lp.fourierTransformₗᵢ ℝ ℂ (convolutionL2 k hk f) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => 𝓕 k ξ * (Lp.fourierTransformₗᵢ ℝ ℂ f : ℝ → ℂ) ξ := by
  rw [fourier_convolutionL2]
  exact fourierKernelMultiplier_apply_ae k hk _

/-- Nonvanishing of the kernel transform implies injectivity of convolution.
@isnad1 id=injectiv.2h1v.s12.61ec63da9436 from=translated src=- shape=b338d966 vocab=c8d99d08
-/
theorem convolutionL2_injective (k : ℝ → ℂ) (hk : Integrable k)
    (hnz : ∀ᵐ ξ ∂volume, 𝓕 k ξ ≠ 0) : Function.Injective (convolutionL2 k hk) :=
  injective_of_fourier_multiplier (convolutionL2 k hk) (𝓕 k) hnz (fourier_convolutionL2_ae k hk)

end Singularity
