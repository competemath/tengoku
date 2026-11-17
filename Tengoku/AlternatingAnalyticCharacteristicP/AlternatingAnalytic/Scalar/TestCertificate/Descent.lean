import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Scalar.TestCertificate.Transfer

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Descent of fibre maps along a functional to a subfield

Let `K / F` be a field extension and `φ : K → F` an `F`-linear functional. A `K`-multilinear
`τ : Hom_K(K^{k+1}, K^k)^k → Alt^k_K(K^{k+1}; K)` descends to an `F`-multilinear
`τ_φ : Hom_F(F^{k+1}, F^k)^k → Alt^k_F(F^{k+1}; F)`, `τ_φ(g)(ξ) = φ(τ(g_K)(ξ_K))`, where `g_K`
and `ξ_K` are the base changes. If `φ 1 = 1` and `τ` satisfies condition (1) of Lemma F.4 over
`K`, then `τ_φ` satisfies condition (1) over `F`.
-/

namespace AlternatingAnalytic.TestCertificate

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

section Alt

variable {n ι : Type*}

instance isScalarTower_alternatingMap :
    IsScalarTower F K ((n → K) [⋀^ι]→ₗ[K] K) :=
  ⟨fun c a α => by ext v; simp⟩

/-- An alternating `K`-form on `K^n`, seen as an `F`-alternating map.-/
def restrictAlt (α : (n → K) [⋀^ι]→ₗ[K] K) : (n → K) [⋀^ι]→ₗ[F] K :=
  { α.toMultilinearMap.restrictScalars F with
    map_eq_zero_of_eq' := fun v _ _ h hij => α.map_eq_zero_of_eq v h hij }

/-- Descent of alternating forms along an `F`-linear functional `φ : K → F`.-/
def descendAlt (φ : K →ₗ[F] F) : ((n → K) [⋀^ι]→ₗ[K] K) →ₗ[F] ((n → F) [⋀^ι]→ₗ[F] F) where
  toFun α := φ.compAlternatingMap ((restrictAlt α).compLinearMap incl)
  map_add' α β := by
    ext ξ
    show φ ((α + β) _) = φ (α _) + φ (β _)
    rw [AlternatingMap.add_apply, map_add]
  map_smul' c α := by
    ext ξ
    show φ ((c • α) _) = c • φ (α _)
    rw [AlternatingMap.smul_apply, map_smul]

theorem descendAlt_apply (φ : K →ₗ[F] F) (α : (n → K) [⋀^ι]→ₗ[K] K) (ξ : ι → n → F) :
    descendAlt φ α ξ = φ (α (fun i => incl (ξ i))) := rfl

end Alt

variable {k : ℕ}

/-- The descended `k`-linear map `τ_φ(g)(ξ) = φ(τ(g_K)(ξ_K))` over `F`.-/
noncomputable def descendFibreMap (φ : K →ₗ[F] F)
    (τ : MultilinearMap K (fun _ : Fin k => (Fin (k + 1) → K) →ₗ[K] (Fin k → K))
      ((Fin (k + 1) → K) [⋀^Fin k]→ₗ[K] K)) :
    MultilinearMap F (fun _ : Fin k => (Fin (k + 1) → F) →ₗ[F] (Fin k → F))
      ((Fin (k + 1) → F) [⋀^Fin k]→ₗ[F] F) :=
  (descendAlt φ).compMultilinearMap ((τ.restrictScalars F).compLinearMap (fun _ => bcMapₗ))

theorem descendFibreMap_apply (φ : K →ₗ[F] F)
    (τ : MultilinearMap K (fun _ : Fin k => (Fin (k + 1) → K) →ₗ[K] (Fin k → K))
      ((Fin (k + 1) → K) [⋀^Fin k]→ₗ[K] K))
    (g : Fin k → ((Fin (k + 1) → F) →ₗ[F] (Fin k → F))) (ξ : Fin k → (Fin (k + 1) → F)) :
    descendFibreMap φ τ g ξ = φ (τ (fun r => bcMap (g r)) (fun r => incl (ξ r))) := rfl

theorem bcMap_firstCoords : bcMap (K := K) (firstCoords F k) = firstCoords K k := by
  refine LinearMap.ext fun x => funext fun i => ?_
  rw [bcMap_apply]
  simp [bcForm, firstCoords, Pi.single_apply]

theorem detV'_incl (v : Fin k → Fin k → F) :
    detV' K k (fun r => incl (v r)) = algebraMap F K (detV' F k v) := by
  rw [detV', detV', Pi.basisFun_det_apply, Pi.basisFun_det_apply, RingHom.map_det]
  rfl

/-- If `φ 1 = 1`, condition (1) descends from `τ` to `τ_φ`.-/
theorem fibreCondition1_descendFibreMap {φ : K →ₗ[F] F} (hφ : φ 1 = 1)
    {τ : MultilinearMap K (fun _ : Fin k => (Fin (k + 1) → K) →ₗ[K] (Fin k → K))
      ((Fin (k + 1) → K) [⋀^Fin k]→ₗ[K] K)}
    (h : FibreCondition1 K k τ) : FibreCondition1 F k (descendFibreMap φ τ) := by
  unfold FibreCondition1 at h ⊢
  ext ξ
  rw [descendFibreMap_apply]
  simp only [bcMap_firstCoords, h, AlternatingMap.compLinearMap_apply]
  have hξ : (fun r => firstCoords K k (incl (ξ r))) =
      fun r => (incl (firstCoords F k (ξ r)) : Fin k → K) := rfl
  rw [hξ, detV'_incl, Algebra.algebraMap_eq_smul_one, map_smul, hφ, smul_eq_mul, mul_one]

end AlternatingAnalytic.TestCertificate
