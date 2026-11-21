import Tengoku.PshdLean.PshLines.Regularization.DistributionRegularization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Fixed-support jets of translated distribution kernels

The parameter derivative of `κ (y - z)` in directions `v i` is the spatial
iterated Fréchet derivative of `κ` in directions `-v i`.  Multiplication by a
fixed cutoff keeps every such jet in one compactly supported smooth-function
space.  This is the first finite-order input for differentiating a distribution
pairing with respect to its translation parameter.
-/

noncomputable section

open Set TopologicalSpace
open scoped ContDiff Distributions

namespace PshLines.Regularization

/-- Evaluation at fixed directions as a continuous linear functional on the
space of continuous multilinear maps.-/
noncomputable def continuousMultilinearApplyCLM
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {r : ℕ} (v : Fin r → E) : (E [×r]→L[ℝ] ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ f v
      map_add' := fun f g ↦ by simp
      map_smul' := fun c f ↦ by simp }
    (∏ i, ‖v i‖) (fun f ↦ by
      dsimp
      simpa only [Real.norm_eq_abs, mul_comm] using f.le_opNorm v)

/-- The value of the `r`-th translation-parameter jet of
`y ↦ χ y * κ (y - z)` in the directions `v`.-/
noncomputable def cutoffTranslatedKernelJet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens E} (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (r : ℕ) (z y : E) (v : Fin r → E) : ℝ :=
  χ y * iteratedFDeriv ℝ r κ (y - z) (fun i ↦ -v i)

/--
@isnad1 id=eq.0h7v.s7.2b7a8654bce1 from=translated src=- shape=58e82b93 vocab=f4e22fc5
-/
@[simp]
theorem cutoffTranslatedKernelJet_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens E} (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (z y : E) (v : Fin 0 → E) :
    cutoffTranslatedKernelJet χ κ 0 z y v = χ y * κ (y - z) := by
  simp [cutoffTranslatedKernelJet]

/-- Smoothness of a fixed directional translation jet in the spatial
variable.
@isnad1 id=contdiff.1h7v.s6.e2a0385c5272 from=translated src=- shape=ce768f75 vocab=45254edc
-/
theorem cutoffTranslatedKernelJet_contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens E} (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (r : ℕ) (z : E) (v : Fin r → E) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ cutoffTranslatedKernelJet χ κ r z y v) := by
  rw [contDiff_infty]
  intro m
  have hχm : ContDiff ℝ m (χ : E → ℝ) :=
    χ.contDiff.of_le (by
      exact_mod_cast (show (m : ℕ∞) ≤ ⊤ from le_top))
  apply hχm.mul
  have hderiv : ContDiff ℝ m (iteratedFDeriv ℝ r κ) :=
    hκ.iteratedFDeriv_right (by
      exact_mod_cast (show (m + r : ℕ∞) ≤ ⊤ from le_top))
  have htranslated : ContDiff ℝ m
      (fun y ↦ iteratedFDeriv ℝ r κ (y - z)) :=
    hderiv.comp (contDiff_id.sub contDiff_const)
  exact (continuousMultilinearApplyCLM (fun i ↦ -v i)).contDiff.comp htranslated

/-- A fixed directional translation jet, bundled in the common compact
support carried by the cutoff.-/
noncomputable def cutoffTranslatedKernelJetSupportedIn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens E} (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (K : Compacts E)
    (hχK : tsupport χ ⊆ K) (r : ℕ) (z : E) (v : Fin r → E) :
    ContDiffMapSupportedIn E ℝ ⊤ K :=
  .of_support_subset
    (cutoffTranslatedKernelJet_contDiff χ κ hκ r z v)
    (by
      change Function.support (fun y ↦ χ y *
        iteratedFDeriv ℝ r κ (y - z) (fun i ↦ -v i)) ⊆ K
      exact (Function.support_mul_subset_left _ _).trans
        ((subset_tsupport χ).trans hχK))

/--
@isnad1 id=eq.2h9v.s9.26529c878deb from=translated src=- shape=f1a06a09 vocab=89c25d62
-/
@[simp]
theorem cutoffTranslatedKernelJetSupportedIn_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens E} (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (K : Compacts E)
    (hχK : tsupport χ ⊆ K) (r : ℕ) (z y : E) (v : Fin r → E) :
    cutoffTranslatedKernelJetSupportedIn χ κ hκ K hχK r z v y =
      χ y * iteratedFDeriv ℝ r κ (y - z) (fun i ↦ -v i) := by
  rfl

/-- The zeroth translation jet is the original fixed-support translated
kernel.
@isnad1 id=eq.2h7v.s8.0ddc2759fa51 from=translated src=- shape=cea26e35 vocab=134195fa
-/
theorem cutoffTranslatedKernelJetSupportedIn_zero_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens E} (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (K : Compacts E)
    (hχK : tsupport χ ⊆ K) (z : E) (v : Fin 0 → E) :
    cutoffTranslatedKernelJetSupportedIn χ κ hκ K hχK 0 z v =
      cutoffTranslatedKernelSupportedIn χ κ hκ K hχK z := by
  ext y
  simp [cutoffTranslatedKernelJetSupportedIn_apply,
    cutoffTranslatedKernelSupportedIn_apply]

/-- Restriction of a distribution to one fixed-support smooth-function
space, kept as a continuous linear map for later finite-order estimates.-/
noncomputable def distributionOnSupportedInCLM
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens E} (T : 𝓓'(Ω, ℝ)) (K : Compacts E)
    (hKΩ : (K : Set E) ⊆ Ω) :
    ContDiffMapSupportedIn E ℝ ⊤ K →L[ℝ] ℝ :=
  T.comp (TestFunction.ofSupportedInCLM ℝ hKΩ)

/--
@isnad1 id=eq.1h5v.s9.cecc3909a27b from=translated src=- shape=07bb5a85 vocab=b5891343
-/
@[simp]
theorem distributionOnSupportedInCLM_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens E} (T : 𝓓'(Ω, ℝ)) (K : Compacts E)
    (hKΩ : (K : Set E) ⊆ Ω)
    (φ : ContDiffMapSupportedIn E ℝ ⊤ K) :
    distributionOnSupportedInCLM T K hKΩ φ =
      T (TestFunction.ofSupportedIn hKΩ φ) :=
  rfl

/-- The candidate `r`-th parameter derivative of a distribution paired with
a cutoff-translated kernel, evaluated in fixed directions.-/
noncomputable def distributionCutoffTranslatedKernelJet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens E} (T : 𝓓'(Ω, ℝ)) (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (K : Compacts E)
    (hχK : tsupport χ ⊆ K) (hKΩ : (K : Set E) ⊆ Ω)
    (r : ℕ) (z : E) (v : Fin r → E) : ℝ :=
  distributionOnSupportedInCLM T K hKΩ
    (cutoffTranslatedKernelJetSupportedIn χ κ hκ K hχK r z v)

/-- At order zero the distributional jet is the original fixed-support
cutoff-translated pairing.
@isnad1 id=eq.3h8v.s9.9a1219a8b7d0 from=translated src=- shape=11d465a3 vocab=7651aa38
-/
theorem distributionCutoffTranslatedKernelJet_zero_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens E} (T : 𝓓'(Ω, ℝ)) (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (K : Compacts E)
    (hχK : tsupport χ ⊆ K) (hKΩ : (K : Set E) ⊆ Ω)
    (z : E) (v : Fin 0 → E) :
    distributionCutoffTranslatedKernelJet T χ κ hκ K hχK hKΩ 0 z v =
      T (TestFunction.ofSupportedIn hKΩ
        (cutoffTranslatedKernelSupportedIn χ κ hκ K hχK z)) := by
  rw [distributionCutoffTranslatedKernelJet,
    distributionOnSupportedInCLM_apply,
    cutoffTranslatedKernelJetSupportedIn_zero_eq]

/-- Additivity of the fixed-support kernel jet in each direction slot.
@isnad1 id=eq.2h11v.s8.f7f57cc8d010 from=translated src=- shape=8e080139 vocab=64799d46
-/
theorem cutoffTranslatedKernelJetSupportedIn_update_add
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens E} (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (K : Compacts E)
    (hχK : tsupport χ ⊆ K) (r : ℕ) (z : E)
    (v : Fin r → E) (i : Fin r) (x y : E) :
    cutoffTranslatedKernelJetSupportedIn χ κ hκ K hχK r z
        (Function.update v i (x + y)) =
      cutoffTranslatedKernelJetSupportedIn χ κ hκ K hχK r z
          (Function.update v i x) +
        cutoffTranslatedKernelJetSupportedIn χ κ hκ K hχK r z
          (Function.update v i y) := by
  ext q
  change χ q * iteratedFDeriv ℝ r κ (q - z)
      (fun j => -Function.update v i (x + y) j) =
    χ q * iteratedFDeriv ℝ r κ (q - z)
        (fun j => -Function.update v i x j) +
      χ q * iteratedFDeriv ℝ r κ (q - z)
        (fun j => -Function.update v i y j)
  let w : Fin r → E := fun j => -v j
  have hadd : (fun j => -Function.update v i (x + y) j) =
      Function.update w i ((-x) + (-y)) := by
    funext j
    by_cases hji : j = i <;> simp [w, hji, add_comm]
  have hx : (fun j => -Function.update v i x j) =
      Function.update w i (-x) := by
    funext j
    by_cases hji : j = i <;> simp [w, hji]
  have hy : (fun j => -Function.update v i y j) =
      Function.update w i (-y) := by
    funext j
    by_cases hji : j = i <;> simp [w, hji]
  rw [hadd, hx, hy,
    (iteratedFDeriv ℝ r κ (q - z)).map_update_add]
  ring

/-- Homogeneity of the fixed-support kernel jet in each direction slot.
@isnad1 id=eq.2h11v.s8.7ca9e7d4b168 from=translated src=- shape=e75bc60e vocab=816799df
-/
theorem cutoffTranslatedKernelJetSupportedIn_update_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens E} (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (K : Compacts E)
    (hχK : tsupport χ ⊆ K) (r : ℕ) (z : E)
    (v : Fin r → E) (i : Fin r) (c : ℝ) (x : E) :
    cutoffTranslatedKernelJetSupportedIn χ κ hκ K hχK r z
        (Function.update v i (c • x)) =
      c • cutoffTranslatedKernelJetSupportedIn χ κ hκ K hχK r z
          (Function.update v i x) := by
  ext q
  change χ q * iteratedFDeriv ℝ r κ (q - z)
      (fun j => -Function.update v i (c • x) j) =
    c * (χ q * iteratedFDeriv ℝ r κ (q - z)
      (fun j => -Function.update v i x j))
  let w : Fin r → E := fun j => -v j
  have hsmul : (fun j => -Function.update v i (c • x) j) =
      Function.update w i (c • (-x)) := by
    funext j
    by_cases hji : j = i <;> simp [w, hji]
  have hx : (fun j => -Function.update v i x j) =
      Function.update w i (-x) := by
    funext j
    by_cases hji : j = i <;> simp [w, hji]
  rw [hsmul, hx,
    (iteratedFDeriv ℝ r κ (q - z)).map_update_smul]
  ring

/-- The candidate distributional jet as an algebraic multilinear map of its
direction variables.  No continuity assertion is made at this layer.-/
noncomputable def distributionCutoffTranslatedKernelJetMultilinearMap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens E} (T : 𝓓'(Ω, ℝ)) (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (K : Compacts E)
    (hχK : tsupport χ ⊆ K) (hKΩ : (K : Set E) ⊆ Ω)
    (r : ℕ) (z : E) :
    MultilinearMap ℝ (fun _ : Fin r => E) ℝ :=
  MultilinearMap.mk'
    (distributionCutoffTranslatedKernelJet T χ κ hκ K hχK hKΩ r z)
    (fun v i x y => by
      rw [distributionCutoffTranslatedKernelJet,
        cutoffTranslatedKernelJetSupportedIn_update_add,
        map_add]
      rfl)
    (fun v i c x => by
      rw [distributionCutoffTranslatedKernelJet,
        cutoffTranslatedKernelJetSupportedIn_update_smul,
        map_smul]
      rfl)

/--
@isnad1 id=eq.3h9v.s8.0e690d580c37 from=translated src=- shape=da17db79 vocab=c1e71f26
-/
@[simp]
theorem distributionCutoffTranslatedKernelJetMultilinearMap_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens E} (T : 𝓓'(Ω, ℝ)) (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (K : Compacts E)
    (hχK : tsupport χ ⊆ K) (hKΩ : (K : Set E) ⊆ Ω)
    (r : ℕ) (z : E) (v : Fin r → E) :
    distributionCutoffTranslatedKernelJetMultilinearMap
        T χ κ hκ K hχK hKΩ r z v =
      distributionCutoffTranslatedKernelJet
        T χ κ hκ K hχK hKΩ r z v := by
  rfl

/-- At order zero the algebraic multilinear package has the original
fixed-support distribution pairing as its unique value.
@isnad1 id=eq.3h8v.s9.89d8ac7c1500 from=translated src=- shape=e41edf8d vocab=38f7f053
-/
@[simp]
theorem distributionCutoffTranslatedKernelJetMultilinearMap_zero_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens E} (T : 𝓓'(Ω, ℝ)) (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (K : Compacts E)
    (hχK : tsupport χ ⊆ K) (hKΩ : (K : Set E) ⊆ Ω)
    (z : E) (v : Fin 0 → E) :
    distributionCutoffTranslatedKernelJetMultilinearMap
        T χ κ hκ K hχK hKΩ 0 z v =
      T (TestFunction.ofSupportedIn hKΩ
        (cutoffTranslatedKernelSupportedIn χ κ hκ K hχK z)) := by
  rw [distributionCutoffTranslatedKernelJetMultilinearMap_apply,
    distributionCutoffTranslatedKernelJet_zero_eq]

/-- Recursive finite-dimensional continuity upgrade for an algebraic
multilinear map, together with preservation of every pointwise value.-/
private noncomputable def multilinearMapToContinuousOfFiniteDimensionalAux
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] :
    ∀ r : ℕ, (f : MultilinearMap ℝ (fun _ : Fin r => E) ℝ) →
      {F : ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ //
        ∀ v, F v = f v}
  | 0, f => by
      refine ⟨ContinuousMultilinearMap.uncurry0 ℝ E (f 0), ?_⟩
      intro v
      rw [ContinuousMultilinearMap.uncurry0_apply]
      congr 1
      funext i
      exact Fin.elim0 i
  | r + 1, f => by
      let L : E →ₗ[ℝ]
          ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ :=
        { toFun := fun x =>
            (multilinearMapToContinuousOfFiniteDimensionalAux r
              (f.curryLeft x)).1
          map_add' := fun x y => by
            ext v
            change (multilinearMapToContinuousOfFiniteDimensionalAux r
                (f.curryLeft (x + y))).1 v =
              (multilinearMapToContinuousOfFiniteDimensionalAux r
                  (f.curryLeft x)).1 v +
                (multilinearMapToContinuousOfFiniteDimensionalAux r
                  (f.curryLeft y)).1 v
            rw [(multilinearMapToContinuousOfFiniteDimensionalAux r
                (f.curryLeft (x + y))).2 v,
              (multilinearMapToContinuousOfFiniteDimensionalAux r
                (f.curryLeft x)).2 v,
              (multilinearMapToContinuousOfFiniteDimensionalAux r
                (f.curryLeft y)).2 v]
            exact DFunLike.congr_fun ((f.curryLeft).map_add x y) v
          map_smul' := fun c x => by
            ext v
            change (multilinearMapToContinuousOfFiniteDimensionalAux r
                (f.curryLeft (c • x))).1 v =
              c • (multilinearMapToContinuousOfFiniteDimensionalAux r
                (f.curryLeft x)).1 v
            rw [(multilinearMapToContinuousOfFiniteDimensionalAux r
                (f.curryLeft (c • x))).2 v,
              (multilinearMapToContinuousOfFiniteDimensionalAux r
                (f.curryLeft x)).2 v]
            exact DFunLike.congr_fun ((f.curryLeft).map_smul c x) v }
      refine ⟨(LinearMap.toContinuousLinearMap L).uncurryLeft, ?_⟩
      intro v
      rw [ContinuousLinearMap.uncurryLeft_apply]
      change (multilinearMapToContinuousOfFiniteDimensionalAux r
          (f.curryLeft (v 0))).1 (Fin.tail v) = f v
      rw [(multilinearMapToContinuousOfFiniteDimensionalAux r
          (f.curryLeft (v 0))).2 (Fin.tail v),
        MultilinearMap.curryLeft_apply, Fin.cons_self_tail]

/-- Every real multilinear map on finitely many copies of a
finite-dimensional normed space has its canonical pointwise-preserving
continuous upgrade.-/
noncomputable def multilinearMapToContinuousOfFiniteDimensional
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {r : ℕ}
    (f : MultilinearMap ℝ (fun _ : Fin r => E) ℝ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ :=
  (multilinearMapToContinuousOfFiniteDimensionalAux r f).1

/--
@isnad1 id=eq.0h4v.s8.c386a35d7fb4 from=translated src=- shape=a0046a93 vocab=d6671cb1
-/
@[simp]
theorem multilinearMapToContinuousOfFiniteDimensional_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {r : ℕ}
    (f : MultilinearMap ℝ (fun _ : Fin r => E) ℝ) (v : Fin r → E) :
    multilinearMapToContinuousOfFiniteDimensional f v = f v :=
  (multilinearMapToContinuousOfFiniteDimensionalAux r f).2 v

/-- In finite-dimensional parameter spaces, the algebraic candidate
distributional jet is a continuous multilinear map in its direction
variables.-/
noncomputable def distributionCutoffTranslatedKernelJetContinuousMultilinearMap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {Ω : Opens E} (T : 𝓓'(Ω, ℝ)) (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (K : Compacts E)
    (hχK : tsupport χ ⊆ K) (hKΩ : (K : Set E) ⊆ Ω)
    (r : ℕ) (z : E) :
    ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ :=
  multilinearMapToContinuousOfFiniteDimensional
    (distributionCutoffTranslatedKernelJetMultilinearMap
      T χ κ hκ K hχK hKΩ r z)

/--
@isnad1 id=eq.3h9v.s8.d86a5c7674c4 from=translated src=- shape=763a8cd0 vocab=541692dd
-/
@[simp]
theorem distributionCutoffTranslatedKernelJetContinuousMultilinearMap_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {Ω : Opens E} (T : 𝓓'(Ω, ℝ)) (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (K : Compacts E)
    (hχK : tsupport χ ⊆ K) (hKΩ : (K : Set E) ⊆ Ω)
    (r : ℕ) (z : E) (v : Fin r → E) :
    distributionCutoffTranslatedKernelJetContinuousMultilinearMap
        T χ κ hκ K hχK hKΩ r z v =
      distributionCutoffTranslatedKernelJet
        T χ κ hκ K hχK hKΩ r z v := by
  rw [distributionCutoffTranslatedKernelJetContinuousMultilinearMap,
    multilinearMapToContinuousOfFiniteDimensional_apply,
    distributionCutoffTranslatedKernelJetMultilinearMap_apply]

/-- At order zero the continuous multilinear package has the original
fixed-support distribution pairing as its unique value.
@isnad1 id=eq.3h8v.s9.c79a7ec0f542 from=translated src=- shape=02de5a3c vocab=a496fe6e
-/
@[simp]
theorem distributionCutoffTranslatedKernelJetContinuousMultilinearMap_zero_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {Ω : Opens E} (T : 𝓓'(Ω, ℝ)) (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (K : Compacts E)
    (hχK : tsupport χ ⊆ K) (hKΩ : (K : Set E) ⊆ Ω)
    (z : E) (v : Fin 0 → E) :
    distributionCutoffTranslatedKernelJetContinuousMultilinearMap
        T χ κ hκ K hχK hKΩ 0 z v =
      T (TestFunction.ofSupportedIn hKΩ
        (cutoffTranslatedKernelSupportedIn χ κ hκ K hχK z)) := by
  rw [distributionCutoffTranslatedKernelJetContinuousMultilinearMap_apply,
    distributionCutoffTranslatedKernelJet_zero_eq]

end PshLines.Regularization
