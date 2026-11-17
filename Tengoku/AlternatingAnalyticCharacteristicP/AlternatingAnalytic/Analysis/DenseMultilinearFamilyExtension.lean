import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Analysis.DenseMultilinearExtension

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Extending multilinear maps on a family of dense subspaces

A continuous multilinear map on a finite family of spaces `D₁ i` extends uniquely,
with the same norm, along dense linear isometries `D₁ i → E₁ i` when the target is
complete. This is Lemma D.5(2). The proof passes through the product `∀ i, D₁ i`
with the supremum norm and the homogeneous case in `DenseMultilinearExtension`.
-/

noncomputable section

namespace AlternatingAnalytic

variable {K : Type*} [NontriviallyNormedField K]
  {I : Type*} [Fintype I]
  {D E F : Type*}
  [NormedAddCommGroup D] [NormedSpace K D]
  [NormedAddCommGroup E] [NormedSpace K E]
  [NormedAddCommGroup F] [NormedSpace K F] [CompleteSpace F]

/-- Extension of multilinear maps along `j`, indexed by any finite type.-/
def denseMultilinearExtensionFinite (j : D →ₗᵢ[K] E) (hd : DenseRange j) :
    ContinuousMultilinearMap K (fun _ : I => D) F →L[K]
      ContinuousMultilinearMap K (fun _ : I => E) F :=
  let rD := ContinuousMultilinearMap.domDomCongrₗᵢ K D F (Fintype.equivFin I)
  let rE := ContinuousMultilinearMap.domDomCongrₗᵢ K E F (Fintype.equivFin I).symm
  rE.toLinearIsometry.toContinuousLinearMap.comp
    ((denseMultilinearExtension j hd (Fintype.card I)).comp
      rD.toLinearIsometry.toContinuousLinearMap)

@[simp]
theorem denseMultilinearExtensionFinite_apply (j : D →ₗᵢ[K] E) (hd : DenseRange j)
    (P : ContinuousMultilinearMap K (fun _ : I => D) F) (x : I → D) :
    denseMultilinearExtensionFinite j hd P (fun i => j (x i)) = P x := by
  change denseMultilinearExtension j hd (Fintype.card I)
    (P.domDomCongr (Fintype.equivFin I))
    (fun i => j (x ((Fintype.equivFin I).symm i))) = P x
  rw [denseMultilinearExtension_apply]
  simp

theorem norm_denseMultilinearExtensionFinite_le (j : D →ₗᵢ[K] E) (hd : DenseRange j)
    (P : ContinuousMultilinearMap K (fun _ : I => D) F) :
    ‖denseMultilinearExtensionFinite j hd P‖ ≤ ‖P‖ := by
  change ‖(denseMultilinearExtension j hd (Fintype.card I)
    (P.domDomCongr (Fintype.equivFin I))).domDomCongr (Fintype.equivFin I).symm‖ ≤ ‖P‖
  rw [ContinuousMultilinearMap.norm_domDomCongr]
  exact (norm_denseMultilinearExtension_le j hd _ _).trans_eq
    (ContinuousMultilinearMap.norm_domDomCongr K D F _ P)

section Family

variable {D₁ E₁ : I → Type*}
  [∀ i, NormedAddCommGroup (D₁ i)] [∀ i, NormedSpace K (D₁ i)]
  [∀ i, NormedAddCommGroup (E₁ i)] [∀ i, NormedSpace K (E₁ i)]

/-- The coordinatewise product of a finite family of linear isometries.-/
def denseFamilyProductIsometry (j : ∀ i, D₁ i →ₗᵢ[K] E₁ i) :
    (∀ i, D₁ i) →ₗᵢ[K] (∀ i, E₁ i) where
  toLinearMap := LinearMap.pi fun i => (j i).toLinearMap.comp (LinearMap.proj i)
  norm_map' x := by
    change ‖fun i => j i (x i)‖ = ‖x‖
    simp only [Pi.norm_def, LinearIsometry.nnnorm_map]

@[simp]
theorem denseFamilyProductIsometry_apply (j : ∀ i, D₁ i →ₗᵢ[K] E₁ i)
    (x : ∀ i, D₁ i) (i : I) : denseFamilyProductIsometry j x i = j i (x i) := rfl

theorem denseRange_denseFamilyProductIsometry (j : ∀ i, D₁ i →ₗᵢ[K] E₁ i)
    (hd : ∀ i, DenseRange (j i)) : DenseRange (denseFamilyProductIsometry j) :=
  DenseRange.piMap hd

/-- Encode a heterogeneous multilinear map by projection from the product in every slot.-/
def multilinearFamilyToProduct :
    ContinuousMultilinearMap K D₁ F →L[K]
      ContinuousMultilinearMap K (fun _ : I => ∀ i, D₁ i) F :=
  ContinuousMultilinearMap.compContinuousLinearMapL fun i => ContinuousLinearMap.proj i

omit [Fintype I] [CompleteSpace F] in
@[simp]
theorem multilinearFamilyToProduct_apply (P : ContinuousMultilinearMap K D₁ F)
    (x : I → ∀ i, D₁ i) : multilinearFamilyToProduct P x = P (fun i => x i i) := rfl

omit [CompleteSpace F] in
theorem norm_multilinearFamilyToProduct_le (P : ContinuousMultilinearMap K D₁ F) :
    ‖multilinearFamilyToProduct P‖ ≤ ‖P‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _)
  intro x
  change ‖P (fun i => x i i)‖ ≤ ‖P‖ * ∏ i, ‖x i‖
  apply (P.le_opNorm _).trans
  gcongr with i
  exact norm_le_pi_norm (x i) i

/-- Restrict a homogeneous map on the product to its coordinate injections.-/
def multilinearProductToFamily :
    ContinuousMultilinearMap K (fun _ : I => ∀ i, E₁ i) F →L[K]
      ContinuousMultilinearMap K E₁ F := by
  classical
  exact ContinuousMultilinearMap.compContinuousLinearMapL
    fun i => (LinearIsometry.single K E₁ i).toContinuousLinearMap

omit [CompleteSpace F] in
@[simp]
theorem multilinearProductToFamily_apply [DecidableEq I] (P :
    ContinuousMultilinearMap K (fun _ : I => ∀ i, E₁ i) F) (x : ∀ i, E₁ i) :
    multilinearProductToFamily P x = P (fun i => Pi.single i (x i)) := by
  simp only [multilinearProductToFamily, ContinuousMultilinearMap.compContinuousLinearMapL_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  funext i t
  by_cases ht : t = i
  · subst t
    simp [LinearIsometry.single, LinearMap.toLinearIsometry, LinearMap.single_apply]
  · simp [LinearIsometry.single, LinearMap.toLinearIsometry, LinearMap.single_apply, ht]

omit [CompleteSpace F] in
theorem norm_multilinearProductToFamily_le (P :
    ContinuousMultilinearMap K (fun _ : I => ∀ i, E₁ i) F) :
    ‖multilinearProductToFamily P‖ ≤ ‖P‖ := by
  classical
  exact P.norm_compContinuous_linearIsometry_le fun i => LinearIsometry.single K E₁ i

/-- Extension of multilinear maps along a family of dense linear isometries.-/
def denseMultilinearFamilyExtension (j : ∀ i, D₁ i →ₗᵢ[K] E₁ i)
    (hd : ∀ i, DenseRange (j i)) :
    ContinuousMultilinearMap K D₁ F →L[K] ContinuousMultilinearMap K E₁ F :=
  multilinearProductToFamily.comp
    ((denseMultilinearExtensionFinite (denseFamilyProductIsometry j)
      (denseRange_denseFamilyProductIsometry j hd)).comp multilinearFamilyToProduct)

@[simp]
theorem denseMultilinearFamilyExtension_apply (j : ∀ i, D₁ i →ₗᵢ[K] E₁ i)
    (hd : ∀ i, DenseRange (j i)) (P : ContinuousMultilinearMap K D₁ F)
    (x : ∀ i, D₁ i) :
    denseMultilinearFamilyExtension j hd P (fun i => j i (x i)) = P x := by
  classical
  change denseMultilinearExtensionFinite (denseFamilyProductIsometry j)
    (denseRange_denseFamilyProductIsometry j hd) (multilinearFamilyToProduct P)
    (fun i => Pi.single i (j i (x i))) = P x
  have hsingle : (fun i => Pi.single i (j i (x i))) =
      (fun i => denseFamilyProductIsometry j (Pi.single i (x i))) := by
    funext i t
    by_cases ht : t = i
    · subst t
      simp
    · simp [Pi.single_eq_of_ne ht]
  rw [hsingle, denseMultilinearExtensionFinite_apply, multilinearFamilyToProduct_apply]
  simp

theorem norm_denseMultilinearFamilyExtension_le (j : ∀ i, D₁ i →ₗᵢ[K] E₁ i)
    (hd : ∀ i, DenseRange (j i)) (P : ContinuousMultilinearMap K D₁ F) :
    ‖denseMultilinearFamilyExtension j hd P‖ ≤ ‖P‖ :=
  (norm_multilinearProductToFamily_le _).trans
    ((norm_denseMultilinearExtensionFinite_le _ _ _).trans
      (norm_multilinearFamilyToProduct_le P))

omit [Fintype I] [CompleteSpace F] in
/-- Continuous multilinear maps that agree on the product of dense images are equal.-/
theorem continuousMultilinearMap_eq_of_dense_family
    (j : ∀ i, D₁ i →ₗᵢ[K] E₁ i) (hd : ∀ i, DenseRange (j i))
    (P Q : ContinuousMultilinearMap K E₁ F)
    (h : ∀ x : ∀ i, D₁ i, P (fun i => j i (x i)) = Q (fun i => j i (x i))) :
    P = Q := by
  apply ContinuousMultilinearMap.ext
  exact congrFun ((DenseRange.piMap hd).equalizer P.cont Q.cont (funext h))

/-- The extension is the only continuous multilinear map agreeing with `P` on the
dense subspaces.-/
theorem denseMultilinearFamilyExtension_unique
    (j : ∀ i, D₁ i →ₗᵢ[K] E₁ i) (hd : ∀ i, DenseRange (j i))
    (P : ContinuousMultilinearMap K D₁ F) (Q : ContinuousMultilinearMap K E₁ F)
    (hQ : ∀ x, Q (fun i => j i (x i)) = P x) :
    Q = denseMultilinearFamilyExtension j hd P := by
  apply continuousMultilinearMap_eq_of_dense_family j hd
  intro x
  rw [hQ, denseMultilinearFamilyExtension_apply]

/-- Dense extension preserves the operator norm.-/
@[simp]
theorem norm_denseMultilinearFamilyExtension
    (j : ∀ i, D₁ i →ₗᵢ[K] E₁ i) (hd : ∀ i, DenseRange (j i))
    (P : ContinuousMultilinearMap K D₁ F) :
    ‖denseMultilinearFamilyExtension j hd P‖ = ‖P‖ := by
  apply le_antisymm (norm_denseMultilinearFamilyExtension_le j hd P)
  let Q := denseMultilinearFamilyExtension j hd P
  have hP : Q.compContinuousLinearMap (fun i => (j i).toContinuousLinearMap) = P := by
    ext x
    exact denseMultilinearFamilyExtension_apply j hd P x
  calc
    ‖P‖ = ‖Q.compContinuousLinearMap (fun i => (j i).toContinuousLinearMap)‖ :=
      congrArg norm hP.symm
    _ ≤ ‖Q‖ := Q.norm_compContinuous_linearIsometry_le j

/-- The extension operator is a linear isometry of the two multilinear-map spaces.-/
def denseMultilinearFamilyExtensionIsometry
    (j : ∀ i, D₁ i →ₗᵢ[K] E₁ i) (hd : ∀ i, DenseRange (j i)) :
    ContinuousMultilinearMap K D₁ F →ₗᵢ[K] ContinuousMultilinearMap K E₁ F where
  toLinearMap := (denseMultilinearFamilyExtension j hd).toLinearMap
  norm_map' := norm_denseMultilinearFamilyExtension j hd

/-- A multilinear map bounded by `C` on the dense subspaces extends uniquely, with
norm at most `C`.-/
theorem exists_denseMultilinearFamilyExtension_of_bound
    (j : ∀ i, D₁ i →ₗᵢ[K] E₁ i) (hd : ∀ i, DenseRange (j i))
    (P : MultilinearMap K D₁ F) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x, ‖P x‖ ≤ C * ∏ i, ‖x i‖) :
    ∃ Q : ContinuousMultilinearMap K E₁ F,
      (∀ x, Q (fun i => j i (x i)) = P x) ∧ ‖Q‖ ≤ C ∧
      ∀ R : ContinuousMultilinearMap K E₁ F,
        (∀ x, R (fun i => j i (x i)) = P x) → R = Q := by
  let P₀ := P.mkContinuous C hbound
  refine ⟨denseMultilinearFamilyExtension j hd P₀, ?_, ?_, ?_⟩
  · exact denseMultilinearFamilyExtension_apply j hd P₀
  · exact (norm_denseMultilinearFamilyExtension_le j hd P₀).trans
      (P.mkContinuous_norm_le hC hbound)
  · intro R hR
    exact denseMultilinearFamilyExtension_unique j hd P₀ R hR

end Family

end AlternatingAnalytic
