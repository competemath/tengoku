import Tengoku.PshdLean.PshLines.Regularization.FiniteJetBanach
import Tengoku.PshdLean.PshLines.Regularization.ConvolutionIteratedJets
import Tengoku.PshdLean.PshLines.Regularization.DistributionTranslationSchwarz
import Tengoku.Seed.Analysis.Normed.Group.Continuity
import Tengoku.Seed.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Transpose identity for distributional convolution

The cutoff-translated kernels take values in one fixed-support test-function
space.  A finite jet embeds that space into a Banach space, where the
Hahn--Banach extension of the restricted distribution commutes with a Bochner
integral.  The iterated-derivative formula for convolution identifies that
integral with the jet of the ordinary scalar convolution.
-/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace Asymptotics
open scoped Convolution ContDiff Distributions NNReal Topology

namespace PshLines.Regularization

/-- The finite-jet image of the first parameter derivative of a translated
kernel.-/
noncomputable def finiteJetCutoffTranslatedKernelFirstJetCLM
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {Ω : Opens E} (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (K : Compacts E)
    (hχK : tsupport χ ⊆ K) (m : ℕ) (z : E) :
    E →L[ℝ] FiniteJetSpace E m :=
  let L : E →ₗ[ℝ] FiniteJetSpace E m :=
    (finiteJetCLM K m).toLinearMap.comp
      (cutoffTranslatedKernelFirstJetLM χ κ hκ K hχK z)
  LinearMap.toContinuousLinearMap L

/-- The finite jet of a cutoff-translated kernel is differentiable in its
translation parameter.
@isnad1 id=hasfderi.2h7v.s9.c83b419b2bb6 from=translated src=- shape=8eb3a192 vocab=41f89866
-/
theorem finiteJet_cutoffTranslatedKernel_hasFDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {Ω : Opens E} (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (K : Compacts E)
    (hχK : tsupport χ ⊆ K) (m : ℕ) (z : E) :
    HasFDerivAt
      (fun w ↦ finiteJetCLM K m
        (cutoffTranslatedKernelSupportedIn χ κ hκ K hχK w))
      (finiteJetCutoffTranslatedKernelFirstJetCLM
        χ κ hκ K hχK m z) z := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff]
  have hrem := cutoffTranslationFirstRemainder_finiteOrderSeminorm_isLittleO_actual
    χ κ hκ K hχK z m
  rw [isLittleO_iff] at hrem
  intro c hc
  filter_upwards [hrem hc] with h hh
  calc
    ‖finiteJetCLM K m
          (cutoffTranslatedKernelSupportedIn χ κ hκ K hχK (z + h)) -
        finiteJetCLM K m
          (cutoffTranslatedKernelSupportedIn χ κ hκ K hχK z) -
        finiteJetCutoffTranslatedKernelFirstJetCLM
          χ κ hκ K hχK m z h‖ =
        ((Finset.Iic m).sup
          (ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K))
          (cutoffTranslationFirstRemainderSupportedIn
            χ κ hκ K hχK z h) := by
      change ‖finiteJetCLM K m
          (cutoffTranslatedKernelSupportedIn χ κ hκ K hχK (z + h)) -
        finiteJetCLM K m
          (cutoffTranslatedKernelSupportedIn χ κ hκ K hχK z) -
        finiteJetCLM K m
          (cutoffTranslatedKernelFirstJetLM χ κ hκ K hχK z h)‖ = _
      rw [← map_sub, ← map_sub,
        norm_finiteJetCLM_eq_finiteOrderSeminorm]
      rfl
    _ ≤ c * ‖h‖ := (Real.le_norm_self _).trans hh

/-- Continuity of a translated kernel after retaining only finitely many
spatial derivatives.
@isnad1 id=continuo.2h6v.s9.4fa408e18bc8 from=translated src=- shape=2fec4c19 vocab=dc13d832
-/
theorem continuous_finiteJet_cutoffTranslatedKernel
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {Ω : Opens E} (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (K : Compacts E)
    (hχK : tsupport χ ⊆ K) (m : ℕ) :
    Continuous (fun z ↦ finiteJetCLM K m
      (cutoffTranslatedKernelSupportedIn χ κ hκ K hχK z)) :=
  continuous_iff_continuousAt.mpr fun z ↦
    (finiteJet_cutoffTranslatedKernel_hasFDerivAt
      χ κ hκ K hχK m z).continuousAt

section Adapted

variable {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E} {x : E}

/-- The scalar convolution of an inner-domain test function with an adapted
kernel, bundled in the same fixed support as the cutoff-translated kernels.-/
noncomputable def AdaptedRadialKernelData.convolutionTestFunctionSupportedIn
    (D : AdaptedRadialKernelData μ Ω x) (j : ℕ) (φ : 𝓓(D.inner, ℝ)) :
    ContDiffMapSupportedIn E ℝ ⊤ D.cutoffCompact :=
  .of_support_subset
    ((D.kernel_hasCompactSupport j).contDiff_convolution_right
      (μ := μ) (L := ContinuousLinearMap.lsmul ℝ ℝ)
      φ.continuous.locallyIntegrable
      (D.kernel_contDiff j))
    (by
      intro y hy
      obtain ⟨z, hz, w, hw, rfl⟩ :=
        Set.mem_add.mp (support_convolution_subset
          (L := ContinuousLinearMap.lsmul ℝ ℝ) hy)
      have hzinner : z ∈ closure (D.inner : Set E) :=
        subset_closure (φ.tsupport_subset (subset_tsupport φ hz))
      have hwcoordinate :=
        D.kernel_tsupport_subset j (subset_tsupport (D.kernel j) hw)
      have hscale : D.radius / ((j : ℝ) + 1) ≤ D.radius := by
        have hj : (1 : ℝ) ≤ (j : ℝ) + 1 := by norm_num
        exact div_le_self D.radius_pos.le hj
      have hycompact : z + w ∈ D.compact :=
        D.coordinate_buffer z hzinner (z + w) (by
          simpa only [add_sub_cancel_left] using hwcoordinate.trans hscale)
      apply subset_tsupport D.cutoff
      change D.cutoff (z + w) ≠ 0
      rw [D.cutoff_one_on_compact (z + w) hycompact]
      exact one_ne_zero)

/--
@isnad1 id=eq.0h8v.s9.25cecd5bd5b3 from=translated src=- shape=d9910992 vocab=8d9bcb36
-/
@[simp]
theorem AdaptedRadialKernelData.convolutionTestFunctionSupportedIn_apply
    (D : AdaptedRadialKernelData μ Ω x) (j : ℕ) (φ : 𝓓(D.inner, ℝ))
    (y : E) :
    D.convolutionTestFunctionSupportedIn j φ y =
      ∫ z, φ z * D.kernel j (y - z) ∂μ := by
  change (φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] D.kernel j) y = _
  rfl

/-- Multiplying the finite jet of the localized kernel by an inner-domain
test function produces a Bochner-integrable Banach-space-valued map.
@isnad1 id=integrab.0h8v.s10.5c914cc43285 from=translated src=- shape=a4281335 vocab=8bd95730
-/
theorem AdaptedRadialKernelData.integrable_smul_finiteJet_localizedKernel
    (D : AdaptedRadialKernelData μ Ω x) (j : ℕ)
    (φ : 𝓓(D.inner, ℝ)) (m : ℕ) :
    Integrable (fun z ↦ φ z • finiteJetCLM D.cutoffCompact m
      (D.localizedKernelSupportedIn j z)) μ := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact φ.continuous.smul
      (continuous_finiteJet_cutoffTranslatedKernel D.cutoff (D.kernel j)
        (D.kernel_contDiff j) D.cutoffCompact (by rfl) m)
  · exact φ.hasCompactSupport.smul_right

/-- On the support of the scalar weight, every coordinate of the localized
finite jet is the corresponding coordinate of the uncut translated kernel.
@isnad1 id=eq.0h12v.s11.aab4d5a3036a from=translated src=- shape=8e50cbe2 vocab=5a0dcb1f
-/
theorem AdaptedRadialKernelData.smul_finiteJet_localizedKernel_apply
    (D : AdaptedRadialKernelData μ Ω x) (j : ℕ)
    (φ : 𝓓(D.inner, ℝ)) (m : ℕ) (z y : E)
    (i : ↑(Finset.Iic m)) (v : Fin (i : ℕ) → E) :
    (φ z • finiteJetCLM D.cutoffCompact m
        (D.localizedKernelSupportedIn j z)) i y v =
      φ z * iteratedFDeriv ℝ (i : ℕ) (D.kernel j) (y - z) v := by
  by_cases hz : φ z = 0
  · simp [hz]
  · have hzinner : z ∈ closure (D.inner : Set E) :=
      subset_closure (φ.tsupport_subset (subset_tsupport φ hz))
    have hfun : (D.localizedKernelSupportedIn j z : E → ℝ) =
        fun q ↦ D.kernel j (q - z) := by
      funext q
      exact D.localizedKernelSupportedIn_eq_kernel j hzinner
    rw [finiteJetSpace_smul_apply, finiteJetCLM_apply,
      BoundedContinuousFunction.smul_apply,
      ContDiffMapSupportedIn.structureMapCLM_top_apply]
    rw [congrArg (fun f : E → ℝ ↦ iteratedFDeriv ℝ (i : ℕ) f y) hfun,
      iteratedFDeriv_comp_sub]
    simp only [smul_apply, smul_eq_mul]

/-- The finite jet of the ordinary convolution is the Bochner integral of
the weighted finite jets of the localized translated kernel.
@isnad1 id=eq.0h8v.s10.e38a880ecf2d from=translated src=- shape=287b9a07 vocab=e31bf3e5
-/
theorem AdaptedRadialKernelData.finiteJet_convolutionTestFunctionSupportedIn_eq_integral
    (D : AdaptedRadialKernelData μ Ω x) (j : ℕ)
    (φ : 𝓓(D.inner, ℝ)) (m : ℕ) :
    finiteJetCLM D.cutoffCompact m
        (D.convolutionTestFunctionSupportedIn j φ) =
      ∫ z, φ z • finiteJetCLM D.cutoffCompact m
        (D.localizedKernelSupportedIn j z) ∂μ := by
  let I : E → FiniteJetSpace E m := fun z ↦
    φ z • finiteJetCLM D.cutoffCompact m
      (D.localizedKernelSupportedIn j z)
  have hI : Integrable I μ :=
    D.integrable_smul_finiteJet_localizedKernel j φ m
  ext i y v
  change iteratedFDeriv ℝ (i : ℕ)
      (φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] D.kernel j) y v =
    finiteJetEvalCLM m i y v (∫ z, I z ∂μ)
  rw [iteratedFDeriv_convolution_right_apply
    (ContinuousLinearMap.lsmul ℝ ℝ)
    φ.continuous.locallyIntegrable (D.kernel_hasCompactSupport j)
    (D.kernel_contDiff j) (i : ℕ) y v,
    ← (finiteJetEvalCLM m i y v).integral_comp_comm hI]
  apply integral_congr_ae
  filter_upwards [] with z
  simpa only [I, ContinuousLinearMap.lsmul_apply, smul_eq_mul, finiteJetEvalCLM_apply] using
    (D.smul_finiteJet_localizedKernel_apply j φ m z y i v).symm

/-- Exact transpose identity for convolution of a distribution with an
adapted kernel on the inner domain.
@isnad1 id=eq.0h8v.s9.52966cdcc2e6 from=translated src=- shape=92d617ae vocab=c3cbfad7
-/
theorem AdaptedRadialKernelData.distribution_convolution_transpose
    (D : AdaptedRadialKernelData μ Ω x) (T : 𝓓'(Ω, ℝ))
    (j : ℕ) (φ : 𝓓(D.inner, ℝ)) :
    ∫ z, φ z * D.distributionRegularizedValue T j z ∂μ =
      T (TestFunction.ofSupportedIn D.cutoffCompact_subset
        (D.convolutionTestFunctionSupportedIn j φ)) := by
  obtain ⟨m, G, hG⟩ := exists_finiteJet_distribution_extension
    T D.cutoffCompact D.cutoffCompact_subset
  let I : E → FiniteJetSpace E m := fun z ↦
    φ z • finiteJetCLM D.cutoffCompact m
      (D.localizedKernelSupportedIn j z)
  have hI : Integrable I μ :=
    D.integrable_smul_finiteJet_localizedKernel j φ m
  calc
    ∫ z, φ z * D.distributionRegularizedValue T j z ∂μ =
        ∫ z, G (I z) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with z
      simp only [I, AdaptedRadialKernelData.distributionRegularizedValue,
        map_smul, smul_eq_mul, hG]
    _ = G (∫ z, I z ∂μ) := G.integral_comp_comm hI
    _ = G (finiteJetCLM D.cutoffCompact m
        (D.convolutionTestFunctionSupportedIn j φ)) := by
      rw [D.finiteJet_convolutionTestFunctionSupportedIn_eq_integral j φ m]
    _ = T (TestFunction.ofSupportedIn D.cutoffCompact_subset
        (D.convolutionTestFunctionSupportedIn j φ)) := hG _

end Adapted

end PshLines.Regularization
