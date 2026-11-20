import Tengoku.PshdLean.PshLines.Regularization.DistributionTranslationSchwarz
import Tengoku.PshdLean.PshLines.SmoothPlurisubharmonic
import Tengoku.Seed.Analysis.Calculus.ContDiff.FiniteDimension

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Smooth cutoff convolutions of arbitrary distributions

Pairing an arbitrary distribution with a fixed-cutoff translate of a smooth
kernel is smooth in the translation parameter.  The proof repeatedly applies
the fixed-support first-derivative theorem: after fixing a direction, the
derivative is the same construction for the directional derivative of the
kernel.  No density representing the distribution is assumed.
-/

noncomputable section

open Set TopologicalSpace
open scoped ContDiff Distributions

namespace PshLines.Regularization

/-- The scalar distribution pairing with a cutoff-translated kernel.-/
noncomputable def distributionCutoffTranslatedPairing
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens E} (T : 𝓓'(Ω, ℝ)) (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (K : Compacts E)
    (hχK : tsupport χ ⊆ K) (hKΩ : (K : Set E) ⊆ Ω) (z : E) : ℝ :=
  distributionOnSupportedInCLM T K hKΩ
    (cutoffTranslatedKernelSupportedIn χ κ hκ K hχK z)

/-- The kernel obtained by differentiating a translate in direction `v`.
The minus sign is the derivative of `y - z` with respect to `z`.-/
noncomputable def translationDirectionalKernel
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (κ : E → ℝ) (v x : E) : ℝ :=
  fderiv ℝ κ x (-v)

/--
@isnad1 id=contdiff.1h3v.s6.5bfb5be09ede from=translated src=- shape=f120bc52 vocab=e15a1461
-/
theorem translationDirectionalKernel_contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (κ : E → ℝ) (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (v : E) :
    ContDiff ℝ (⊤ : ℕ∞) (translationDirectionalKernel κ v) := by
  exact (hκ.fderiv_right (by simp)).clm_apply contDiff_const

/-- The actual first derivative of the cutoff distribution pairing.-/
noncomputable def distributionCutoffTranslatedPairingFDeriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {Ω : Opens E} (T : 𝓓'(Ω, ℝ)) (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (K : Compacts E)
    (hχK : tsupport χ ⊆ K) (hKΩ : (K : Set E) ⊆ Ω) (z : E) :
    E →L[ℝ] ℝ :=
  ⟨(distributionOnSupportedInCLM T K hKΩ).toLinearMap.comp
      (cutoffTranslatedKernelFirstJetLM χ κ hκ K hχK z),
    ((distributionOnSupportedInCLM T K hKΩ).toLinearMap.comp
      (cutoffTranslatedKernelFirstJetLM χ κ hκ K hχK z)).continuous_of_finiteDimensional⟩

/--
@isnad1 id=eq.3h8v.s8.271d400ecbbe from=translated src=- shape=121826fd vocab=3758a4e5
-/
@[simp]
theorem distributionCutoffTranslatedPairingFDeriv_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {Ω : Opens E} (T : 𝓓'(Ω, ℝ)) (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (K : Compacts E)
    (hχK : tsupport χ ⊆ K) (hKΩ : (K : Set E) ⊆ Ω) (z v : E) :
    distributionCutoffTranslatedPairingFDeriv
        T χ κ hκ K hχK hKΩ z v =
      distributionCutoffTranslatedPairing T χ
        (translationDirectionalKernel κ v)
        (translationDirectionalKernel_contDiff κ hκ v) K hχK hKΩ z := by
  change distributionOnSupportedInCLM T K hKΩ
      (cutoffTranslatedKernelFirstJetLM χ κ hκ K hχK z v) =
    distributionOnSupportedInCLM T K hKΩ
      (cutoffTranslatedKernelSupportedIn χ
        (translationDirectionalKernel κ v)
        (translationDirectionalKernel_contDiff κ hκ v) K hχK z)
  congr 1
  ext y
  simp only [cutoffTranslatedKernelFirstJetLM_apply,
    cutoffTranslatedKernelJetSupportedIn_apply,
    cutoffTranslatedKernelSupportedIn_apply, translationDirectionalKernel,
    iteratedFDeriv_one_apply]

/--
@isnad1 id=hasfderi.3h7v.s8.d48f18c5d98a from=translated src=- shape=b7dec620 vocab=5ab9c017
-/
theorem distributionCutoffTranslatedPairing_hasFDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {Ω : Opens E} (T : 𝓓'(Ω, ℝ)) (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (K : Compacts E)
    (hχK : tsupport χ ⊆ K) (hKΩ : (K : Set E) ⊆ Ω) (z : E) :
    HasFDerivAt
      (distributionCutoffTranslatedPairing T χ κ hκ K hχK hKΩ)
      (distributionCutoffTranslatedPairingFDeriv
        T χ κ hκ K hχK hKΩ z) z := by
  exact distributionPairing_hasFDerivAt T χ κ hκ K hχK hKΩ z

private theorem distributionCutoffTranslatedPairing_contDiff_nat
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {Ω : Opens E} (T : 𝓓'(Ω, ℝ)) (χ : 𝓓(Ω, ℝ)) (K : Compacts E)
    (hχK : tsupport χ ⊆ K) (hKΩ : (K : Set E) ⊆ Ω) :
    ∀ (n : ℕ) (κ : E → ℝ) (hκ : ContDiff ℝ (⊤ : ℕ∞) κ),
      ContDiff ℝ n
        (distributionCutoffTranslatedPairing T χ κ hκ K hχK hKΩ) := by
  intro n
  induction n with
  | zero =>
      intro κ hκ
      change ContDiff ℝ 0
        (distributionCutoffTranslatedPairing T χ κ hκ K hχK hKΩ)
      rw [contDiff_zero]
      exact (show Differentiable ℝ
          (distributionCutoffTranslatedPairing T χ κ hκ K hχK hKΩ) from
        fun z ↦ (distributionCutoffTranslatedPairing_hasFDerivAt
          T χ κ hκ K hχK hKΩ z).differentiableAt).continuous
  | succ n ih =>
      intro κ hκ
      change ContDiff ℝ ((n : ℕ∞ω) + 1)
        (distributionCutoffTranslatedPairing T χ κ hκ K hχK hKΩ)
      rw [contDiff_succ_iff_hasFDerivAt]
      refine ⟨distributionCutoffTranslatedPairingFDeriv
        T χ κ hκ K hχK hKΩ, ?_, fun z ↦
          distributionCutoffTranslatedPairing_hasFDerivAt
            T χ κ hκ K hχK hKΩ z⟩
      apply contDiff_clm_apply_iff.mpr
      intro v
      have hv := ih (translationDirectionalKernel κ v)
        (translationDirectionalKernel_contDiff κ hκ v)
      have heq :
          (fun z ↦ distributionCutoffTranslatedPairingFDeriv
              T χ κ hκ K hχK hKΩ z v) =
            distributionCutoffTranslatedPairing T χ
              (translationDirectionalKernel κ v)
              (translationDirectionalKernel_contDiff κ hκ v)
              K hχK hKΩ := by
        funext z
        exact distributionCutoffTranslatedPairingFDeriv_apply
          T χ κ hκ K hχK hKΩ z v
      rw [heq]
      exact hv

/-- Pairing an arbitrary distribution with a smooth cutoff-translated kernel
is globally smooth in the translation parameter.
@isnad1 id=contdiff.3h6v.s8.204723b01123 from=translated src=- shape=300d97d9 vocab=cdda8a19
-/
theorem distributionCutoffTranslatedPairing_contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {Ω : Opens E} (T : 𝓓'(Ω, ℝ)) (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (K : Compacts E)
    (hχK : tsupport χ ⊆ K) (hKΩ : (K : Set E) ⊆ Ω) :
    ContDiff ℝ (⊤ : ℕ∞)
      (distributionCutoffTranslatedPairing T χ κ hκ K hχK hKΩ) := by
  rw [contDiff_infty]
  intro n
  exact distributionCutoffTranslatedPairing_contDiff_nat
    T χ K hχK hKΩ n κ hκ

/-- The scalar pairing is independent of the proof term witnessing kernel
smoothness and respects equality of the underlying kernels.
@isnad1 id=eq.5h7v.s8.e8d1e2d4e923 from=translated src=- shape=932cf78b vocab=7213d982
-/
theorem distributionCutoffTranslatedPairing_congr_kernel
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens E} (T : 𝓓'(Ω, ℝ)) (χ : 𝓓(Ω, ℝ))
    {κ τ : E → ℝ} (hκ : ContDiff ℝ (⊤ : ℕ∞) κ)
    (hτ : ContDiff ℝ (⊤ : ℕ∞) τ) (K : Compacts E)
    (hχK : tsupport χ ⊆ K) (hKΩ : (K : Set E) ⊆ Ω)
    (h : κ = τ) :
    distributionCutoffTranslatedPairing T χ κ hκ K hχK hKΩ =
      distributionCutoffTranslatedPairing T χ τ hτ K hχK hKΩ := by
  subst τ
  rfl

/-- The Fréchet derivative is the distribution paired with the translated
directional derivative of the kernel.
@isnad1 id=eq.3h8v.s9.b51c381277f7 from=translated src=- shape=880afbbf vocab=116da2ff
-/
theorem fderiv_distributionCutoffTranslatedPairing_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {Ω : Opens E} (T : 𝓓'(Ω, ℝ)) (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (K : Compacts E)
    (hχK : tsupport χ ⊆ K) (hKΩ : (K : Set E) ⊆ Ω) (z v : E) :
    fderiv ℝ
        (distributionCutoffTranslatedPairing T χ κ hκ K hχK hKΩ) z v =
      distributionCutoffTranslatedPairing T χ
        (translationDirectionalKernel κ v)
        (translationDirectionalKernel_contDiff κ hκ v) K hχK hKΩ z := by
  rw [(distributionCutoffTranslatedPairing_hasFDerivAt
    T χ κ hκ K hχK hKΩ z).fderiv]
  exact distributionCutoffTranslatedPairingFDeriv_apply
    T χ κ hκ K hχK hKΩ z v

/-- The scalar kernel obtained by evaluating the real Hessian twice in one
fixed direction.-/
noncomputable def realHessianDirectionalKernel
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (κ : E → ℝ) (v x : E) : ℝ :=
  realHessian κ x v v

/--
@isnad1 id=contdiff.1h3v.s6.15e4edea8629 from=translated src=- shape=f120bc52 vocab=9ce376b3
-/
theorem realHessianDirectionalKernel_contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (κ : E → ℝ) (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (v : E) :
    ContDiff ℝ (⊤ : ℕ∞) (realHessianDirectionalKernel κ v) := by
  have hiter : ContDiff ℝ (⊤ : ℕ∞) (iteratedFDeriv ℝ 2 κ) :=
    hκ.iteratedFDeriv_right (by
      change ((↑((⊤ : ℕ∞) + 2) : ℕ∞ω) ≤ ↑(⊤ : ℕ∞))
      exact WithTop.coe_le_coe.mpr (by simp))
  exact (continuousMultilinearApplyCLM ![v, v]).contDiff.comp hiter

/-- The two translation signs cancel when the same direction is applied
twice, leaving the ordinary real Hessian of the kernel.
@isnad1 id=eq.1h4v.s6.a279b815b584 from=translated src=- shape=f7fb7793 vocab=d0699adb
-/
theorem translationDirectionalKernel_twice_self
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (κ : E → ℝ) (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (v x : E) :
    translationDirectionalKernel (translationDirectionalKernel κ v) v x =
      realHessianDirectionalKernel κ v x := by
  change fderiv ℝ (fun y ↦ fderiv ℝ κ y (-v)) x (-v) =
    realHessian κ x v v
  have hneg : (fun y ↦ fderiv ℝ κ y (-v)) =
      -(fun y ↦ fderiv ℝ κ y v) := by
    funext y
    simp
  rw [hneg, fderiv_neg]
  rw [map_neg]
  rw [realHessian_eq_fderiv]
  have hDcont : ContDiff ℝ 1 (fderiv ℝ κ) :=
    hκ.fderiv_right (m := 1) (by
      change ((↑((1 : ℕ∞) + 1) : ℕ∞ω) ≤ ↑(⊤ : ℕ∞))
      exact WithTop.coe_le_coe.mpr (by simp))
  have hD : DifferentiableAt ℝ (fderiv ℝ κ) x :=
    (hDcont.differentiable one_ne_zero).differentiableAt
  rw [fderiv_clm_apply hD (differentiableAt_const v)]
  simp

/-- The real Hessian of the distribution pairing is obtained by pairing the
distribution with the corresponding translated kernel Hessian.
@isnad1 id=eq.3h8v.s8.3bcb85552919 from=translated src=- shape=3fe1cf32 vocab=6f5a64d4
-/
theorem realHessian_distributionCutoffTranslatedPairing_self
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {Ω : Opens E} (T : 𝓓'(Ω, ℝ)) (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (K : Compacts E)
    (hχK : tsupport χ ⊆ K) (hKΩ : (K : Set E) ⊆ Ω) (z v : E) :
    realHessian
        (distributionCutoffTranslatedPairing T χ κ hκ K hχK hKΩ) z v v =
      distributionCutoffTranslatedPairing T χ
        (realHessianDirectionalKernel κ v)
        (realHessianDirectionalKernel_contDiff κ hκ v)
        K hχK hKΩ z := by
  let F : E → ℝ :=
    distributionCutoffTranslatedPairing T χ κ hκ K hχK hKΩ
  let DF : E → E →L[ℝ] ℝ :=
    distributionCutoffTranslatedPairingFDeriv T χ κ hκ K hχK hKΩ
  have hFderiv : fderiv ℝ F = DF := by
    funext q
    exact (distributionCutoffTranslatedPairing_hasFDerivAt
      T χ κ hκ K hχK hKΩ q).fderiv
  have hDFsmooth : ContDiff ℝ (⊤ : ℕ∞) DF := by
    rw [← hFderiv]
    exact (distributionCutoffTranslatedPairing_contDiff
      T χ κ hκ K hχK hKΩ).fderiv_right (by simp)
  have happly :
      fderiv ℝ (fun q ↦ DF q v) z v =
        distributionCutoffTranslatedPairing T χ
          (realHessianDirectionalKernel κ v)
          (realHessianDirectionalKernel_contDiff κ hκ v)
          K hχK hKΩ z := by
    have heq : (fun q ↦ DF q v) =
        distributionCutoffTranslatedPairing T χ
          (translationDirectionalKernel κ v)
          (translationDirectionalKernel_contDiff κ hκ v)
          K hχK hKΩ := by
      funext q
      exact distributionCutoffTranslatedPairingFDeriv_apply
        T χ κ hκ K hχK hKΩ q v
    rw [heq, fderiv_distributionCutoffTranslatedPairing_apply]
    have hkernel :
        translationDirectionalKernel (translationDirectionalKernel κ v) v =
          realHessianDirectionalKernel κ v := by
      funext q
      exact translationDirectionalKernel_twice_self κ hκ v q
    exact congrFun (distributionCutoffTranslatedPairing_congr_kernel
      T χ
      (translationDirectionalKernel_contDiff (translationDirectionalKernel κ v)
        (translationDirectionalKernel_contDiff κ hκ v) v)
      (realHessianDirectionalKernel_contDiff κ hκ v)
      K hχK hKΩ hkernel) z
  have hclmapply :
      fderiv ℝ (fun q ↦ DF q v) z v = fderiv ℝ DF z v v := by
    rw [fderiv_clm_apply (hDFsmooth.differentiable (by simp)).differentiableAt
      (differentiableAt_const v)]
    simp
  rw [realHessian_eq_fderiv, hFderiv, ← hclmapply]
  exact happly

/-- The Levi form of the smooth distribution pairing is the average of the
two distribution pairings with the corresponding kernel Hessians.
@isnad1 id=eq.3h8v.s8.7e04485271a7 from=translated src=- shape=4c86aa15 vocab=35d357c5
-/
theorem leviForm_distributionCutoffTranslatedPairing
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedSpace ℂ E] [FiniteDimensional ℝ E]
    {Ω : Opens E} (T : 𝓓'(Ω, ℝ)) (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (K : Compacts E)
    (hχK : tsupport χ ⊆ K) (hKΩ : (K : Set E) ⊆ Ω) (z v : E) :
    leviForm
        (distributionCutoffTranslatedPairing T χ κ hκ K hχK hKΩ) z v =
      (distributionCutoffTranslatedPairing T χ
          (realHessianDirectionalKernel κ v)
          (realHessianDirectionalKernel_contDiff κ hκ v)
          K hχK hKΩ z +
        distributionCutoffTranslatedPairing T χ
          (realHessianDirectionalKernel κ (Complex.I • v))
          (realHessianDirectionalKernel_contDiff κ hκ (Complex.I • v))
          K hχK hKΩ z) / 4 := by
  rw [leviForm,
    realHessian_distributionCutoffTranslatedPairing_self,
    realHessian_distributionCutoffTranslatedPairing_self]

/-- If the cutoff is one on the translated kernel support, transposing the
kernel Hessian to the test function gives the corresponding second
distributional derivative.
@isnad1 id=eq.4h8v.s11.cb6c1e5bc9be from=translated src=- shape=9dbf4f89 vocab=2c6321d2
-/
theorem distributionCutoffTranslatedPairing_realHessian_eq_lineDeriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {Ω : Opens E} (T : 𝓓'(Ω, ℝ)) (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (K : Compacts E)
    (hχK : tsupport χ ⊆ K) (hKΩ : (K : Set E) ⊆ Ω)
    (z w : E)
    (hcut : ∀ y ∈ tsupport (fun q : E ↦ κ (q - z)), χ y = 1) :
    distributionCutoffTranslatedPairing T χ
        (realHessianDirectionalKernel κ w)
        (realHessianDirectionalKernel_contDiff κ hκ w)
        K hχK hKΩ z =
      T (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ w
        (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ w
          (TestFunction.ofSupportedIn hKΩ
            (cutoffTranslatedKernelSupportedIn χ κ hκ K hχK z)))) := by
  have hfun : (fun q : E ↦ χ q * κ (q - z)) =
      fun q : E ↦ κ (q - z) := by
    funext q
    by_cases hq : q ∈ tsupport (fun y : E ↦ κ (y - z))
    · rw [hcut q hq, one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hq, mul_zero]
  change T (TestFunction.ofSupportedIn hKΩ
      (cutoffTranslatedKernelSupportedIn χ
        (realHessianDirectionalKernel κ w)
        (realHessianDirectionalKernel_contDiff κ hκ w) K hχK z)) = _
  congr 1
  ext y
  rw [testFunction_lineDerivCLM_lineDerivCLM_apply]
  change χ y * realHessian κ (y - z) w w =
    realHessian (fun q : E ↦ χ q * κ (q - z)) y w w
  rw [hfun, realHessian_comp_sub]
  by_cases hh : realHessian κ (y - z) w w = 0
  · rw [hh, mul_zero]
  · have hy : y ∈ tsupport (fun q : E ↦ κ (q - z)) := by
      apply tsupport_realHessian_subset (fun q : E ↦ κ (q - z)) w w
      apply subset_tsupport
      change realHessian (fun q : E ↦ κ (q - z)) y w w ≠ 0
      rw [realHessian_comp_sub]
      exact hh
    rw [hcut y hy, one_mul]

/-- On a parameter where the cutoff is invisible, the classical Levi form
of the smooth pairing is exactly the distributional Levi derivative evaluated
on that translated test function.
@isnad1 id=eq.4h8v.s11.4bc6ad88c5ad from=translated src=- shape=8f28702b vocab=5f096fbf
-/
theorem leviForm_distributionCutoffTranslatedPairing_eq_distributionalLevi
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedSpace ℂ E] [FiniteDimensional ℝ E]
    {Ω : Opens E} (T : 𝓓'(Ω, ℝ)) (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (K : Compacts E)
    (hχK : tsupport χ ⊆ K) (hKΩ : (K : Set E) ⊆ Ω)
    (z v : E)
    (hcut : ∀ y ∈ tsupport (fun q : E ↦ κ (q - z)), χ y = 1) :
    leviForm
        (distributionCutoffTranslatedPairing T χ κ hκ K hχK hKΩ) z v =
      distributionalLeviCLM v T
        (TestFunction.ofSupportedIn hKΩ
          (cutoffTranslatedKernelSupportedIn χ κ hκ K hχK z)) := by
  rw [leviForm_distributionCutoffTranslatedPairing,
    distributionCutoffTranslatedPairing_realHessian_eq_lineDeriv
      T χ κ hκ K hχK hKΩ z v hcut,
    distributionCutoffTranslatedPairing_realHessian_eq_lineDeriv
      T χ κ hκ K hχK hKΩ z (Complex.I • v) hcut,
    distributionalLeviCLM_apply]
  ring

section AdaptedKernel

variable {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : MeasureTheory.Measure E} [μ.IsAddHaarMeasure]
  {Ω : Opens E} {x : E}

/-- The localized adapted-kernel pairing is globally smooth.
@isnad1 id=contdiff.0h7v.s8.1a68ac5760fd from=translated src=- shape=3c90116d vocab=d108b158
-/
theorem AdaptedRadialKernelData.distributionRegularizedValue_contDiff
    (D : AdaptedRadialKernelData μ Ω x) (T : 𝓓'(Ω, ℝ)) (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (D.distributionRegularizedValue T j) := by
  have heq : D.distributionRegularizedValue T j =
      distributionCutoffTranslatedPairing T D.cutoff (D.kernel j)
        (D.kernel_contDiff j) D.cutoffCompact (by rfl)
        D.cutoffCompact_subset := by
    funext z
    rfl
  rw [heq]
  exact distributionCutoffTranslatedPairing_contDiff T D.cutoff (D.kernel j)
    (D.kernel_contDiff j) D.cutoffCompact (by rfl)
    D.cutoffCompact_subset

/-- Every translated adapted kernel centered in the closed inner domain has
topological support in the compact cutoff buffer.
@isnad1 id=le.1h7v.s8.f7cb556bb7eb from=translated src=- shape=54502245 vocab=3bf5178c
-/
theorem AdaptedRadialKernelData.translatedKernel_tsupport_subset_compact_for_smoothing
    (D : AdaptedRadialKernelData μ Ω x) (j : ℕ) {z : E}
    (hz : z ∈ closure (D.inner : Set E)) :
    tsupport (fun y : E ↦ D.kernel j (y - z)) ⊆ D.compact := by
  apply closure_minimal
  · intro y hy
    have hyKernel : y - z ∈ tsupport (D.kernel j) :=
      subset_tsupport (D.kernel j) hy
    have hcoord := D.kernel_tsupport_subset j hyKernel
    have hscale : D.radius / ((j : ℝ) + 1) ≤ D.radius := by
      have hj : (1 : ℝ) ≤ (j : ℝ) + 1 := by norm_num
      exact div_le_self D.radius_pos.le hj
    exact D.coordinate_buffer z hz y (hcoord.trans hscale)
  · exact D.compact.isCompact.isClosed

/-- On the closed inner domain, the classical Levi form of an adapted-kernel
regularized value is its distributional Levi pairing.
@isnad1 id=eq.1h9v.s11.6c8c30682077 from=translated src=- shape=2fcf53aa vocab=d46c5f14
-/
theorem AdaptedRadialKernelData.leviForm_distributionRegularizedValue_eq
    (D : AdaptedRadialKernelData μ Ω x) (T : 𝓓'(Ω, ℝ)) (j : ℕ)
    {z : E} (hz : z ∈ closure (D.inner : Set E)) (v : E) :
    leviForm (D.distributionRegularizedValue T j) z v =
      distributionalLeviCLM v T
        (TestFunction.ofSupportedIn D.cutoffCompact_subset
          (D.localizedKernelSupportedIn j z)) := by
  have hcut : ∀ y ∈ tsupport (fun q : E ↦ D.kernel j (q - z)),
      D.cutoff y = 1 := by
    intro y hy
    exact D.cutoff_one_on_compact y
      (D.translatedKernel_tsupport_subset_compact_for_smoothing j hz hy)
  have heq : D.distributionRegularizedValue T j =
      distributionCutoffTranslatedPairing T D.cutoff (D.kernel j)
        (D.kernel_contDiff j) D.cutoffCompact (by rfl)
        D.cutoffCompact_subset := by
    funext q
    rfl
  rw [heq]
  simpa only [AdaptedRadialKernelData.localizedKernelSupportedIn] using
    leviForm_distributionCutoffTranslatedPairing_eq_distributionalLevi T
      D.cutoff (D.kernel j) (D.kernel_contDiff j) D.cutoffCompact
      (by rfl) D.cutoffCompact_subset z v hcut

/-- A distribution with nonnegative distributional Levi form has nonnegative
classical Levi form after adapted-kernel regularization on the inner domain.
@isnad1 id=le.2h9v.s8.a9efac9a8a50 from=translated src=- shape=3a840ca0 vocab=b3eb0147
-/
theorem AdaptedRadialKernelData.leviForm_distributionRegularizedValue_nonneg
    (D : AdaptedRadialKernelData μ Ω x) (T : 𝓓'(Ω, ℝ))
    (hT : HasNonnegativeDistributionalLevi T) (j : ℕ)
    {z : E} (hz : z ∈ closure (D.inner : Set E)) (v : E) :
    0 ≤ leviForm (D.distributionRegularizedValue T j) z v := by
  rw [D.leviForm_distributionRegularizedValue_eq T j hz v]
  apply hT v
  intro y
  change 0 ≤ D.cutoff y * D.kernel j (y - z)
  exact mul_nonneg (D.cutoff_mem_Icc y).1 (D.kernel_nonneg j (y - z))

/-- The localized adapted-kernel regularization of a positive-Levi
distribution satisfies the disc-PSH criterion on the inner domain.
@isnad1 id=discpsho.1h7v.s8.8f1927e8a564 from=translated src=- shape=b3102cd1 vocab=b68e95bb
-/
theorem AdaptedRadialKernelData.discPshOn_distributionRegularizedValue
    (D : AdaptedRadialKernelData μ Ω x) (T : 𝓓'(Ω, ℝ))
    (hT : HasNonnegativeDistributionalLevi T) (j : ℕ) :
    DiscPshOn (fun z : E ↦ (D.distributionRegularizedValue T j z : EReal))
      (D.inner : Set E) := by
  apply discPshOn_of_levi_nonneg
    ((D.distributionRegularizedValue_contDiff T j).of_le (by
      exact WithTop.coe_le_coe.mpr (by simp)))
  intro z hz v
  exact D.leviForm_distributionRegularizedValue_nonneg T hT j
    (subset_closure hz) v

end AdaptedKernel

end PshLines.Regularization
