import Tengoku.Seed.Data.Complex.Basic
import Tengoku.Seed.LinearAlgebra.Matrix.NonsingularInverse
import Tengoku.Seed.LinearAlgebra.FreeModule.StrongRankCondition
import Tengoku.Seed.LinearAlgebra.Matrix.Rank
import Tengoku.Seed.Analysis.Matrix.Spectrum
import Tengoku.Seed.Analysis.Matrix.PosDef
import Tengoku.Seed.Analysis.InnerProductSpace.PiL2

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/haimav/formalize-tubal-demyst-paper@08d013e19c2b, `TubalTensor/Prerequisites/SVD.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-!
  TubalTensor/Prerequisites/SVD.lean
  Matrix SVD: definitions, structures, and existence proofs.

  SVD existence is proved via the spectral theorem for Hermitian matrices
  (diagonalizing Aᴴ*A to get V and eigenvalues, then constructing U via
  ONB extension of the normalized columns A*vⱼ/σⱼ).
-/

namespace TubalTensor

open Matrix Complex BigOperators

/-! ## Predicates -/

/-- A square matrix is unitary: Aᴴ * A = 1.-/
def IsUnitary {n : ℕ} {𝕜 : Type*} [RCLike 𝕜] (A : Matrix (Fin n) (Fin n) 𝕜) : Prop :=
  Aᴴ * A = 1

/--
@isnad1 id=eq.1h3v.s7.b3aa58e2480d from=translated src=- shape=0725dba7 vocab=e2bb2ad2
-/
theorem IsUnitary.conjTranspose_mul_self {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {A : Matrix (Fin n) (Fin n) 𝕜}
    (h : IsUnitary A) : Aᴴ * A = 1 := h

/--
@isnad1 id=eq.1h3v.s7.aef75c1d2b70 from=translated src=- shape=dad54abf vocab=e2bb2ad2
-/
theorem IsUnitary.mul_conjTranspose_self {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {A : Matrix (Fin n) (Fin n) 𝕜}
    (h : IsUnitary A) : A * Aᴴ = 1 :=
  (mul_eq_one_comm_of_card_eq (Fin n) (Fin n) 𝕜 rfl).mp h

/--
@isnad1 id=isunitar.1h3v.s6.1728f04e4dd1 from=translated src=- shape=5b74fc42 vocab=c2aa4858
-/
theorem IsUnitary.conjTranspose {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {A : Matrix (Fin n) (Fin n) 𝕜}
    (h : IsUnitary A) : IsUnitary Aᴴ := by
  show Aᴴᴴ * Aᴴ = 1
  rw [conjTranspose_conjTranspose]
  exact h.mul_conjTranspose_self

/-- A rectangular real matrix is "SVD-diagonal": only (i,i) entries can be nonzero,
    those entries are nonneg, and they are non-increasing.-/
def IsSVDDiag {m p : ℕ} (S : Matrix (Fin m) (Fin p) ℝ) : Prop :=
  (∀ (i : Fin m) (j : Fin p), (i : ℕ) ≠ (j : ℕ) → S i j = 0) ∧
  (∀ (i : Fin m) (j : Fin p), (i : ℕ) = (j : ℕ) → 0 ≤ S i j) ∧
  (∀ (i₁ i₂ : Fin m) (j₁ j₂ : Fin p), (i₁ : ℕ) = (j₁ : ℕ) → (i₂ : ℕ) = (j₂ : ℕ) →
    i₁ ≤ i₂ → S i₂ j₂ ≤ S i₁ j₁)

/-- The complex embedding of S as used in the decomposition A = U * Sℂ * Vᴴ.-/
noncomputable abbrev toComplexMatrix {m p : ℕ} (S : Matrix (Fin m) (Fin p) ℝ) :
    Matrix (Fin m) (Fin p) ℂ :=
  S.map (Complex.ofReal)

/-- `S.map (algebraMap ℝ ℂ) = toComplexMatrix S`.
@isnad1 id=eq.0h3v.s6.0e8f0fb43156 from=translated src=- shape=16a3d192 vocab=86da53f1
-/
theorem map_algebraMap_eq_toComplexMatrix {m p : ℕ} (S : Matrix (Fin m) (Fin p) ℝ) :
    S.map (algebraMap ℝ ℂ) = toComplexMatrix S := rfl

/-- A rectangular complex matrix is "SVD-diagonal": only (i,i) entries can be nonzero,
    those entries are real and nonneg, and they are non-increasing.-/
def IsSVDDiagC {m p : ℕ} (S : Matrix (Fin m) (Fin p) ℂ) : Prop :=
  (∀ (i : Fin m) (j : Fin p), (i : ℕ) ≠ (j : ℕ) → S i j = 0) ∧
  (∀ (i : Fin m) (j : Fin p), (i : ℕ) = (j : ℕ) → (S i j).im = 0 ∧ 0 ≤ (S i j).re) ∧
  (∀ (i₁ i₂ : Fin m) (j₁ j₂ : Fin p), (i₁ : ℕ) = (j₁ : ℕ) → (i₂ : ℕ) = (j₂ : ℕ) →
    i₁ ≤ i₂ → (S i₂ j₂).re ≤ (S i₁ j₁).re)

/-- Bridge: real IsSVDDiag implies complex IsSVDDiagC via embedding.
@isnad1 id=issvddia.1h3v.s4.6c029e31fcf4 from=translated src=- shape=dbaef3ad vocab=8ddea30f
-/
theorem IsSVDDiag.toComplex {m p : ℕ} {S : Matrix (Fin m) (Fin p) ℝ}
    (h : IsSVDDiag S) : IsSVDDiagC (toComplexMatrix S) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    simp [toComplexMatrix, Matrix.map_apply, h.1 i j hij]
  · intro i j hij
    simp [toComplexMatrix, Matrix.map_apply, Complex.ofReal_im, Complex.ofReal_re]
    exact h.2.1 i j hij
  · intro i₁ i₂ j₁ j₂ h₁ h₂ hle
    simp [toComplexMatrix, Matrix.map_apply, Complex.ofReal_re]
    exact h.2.2 i₁ i₂ j₁ j₂ h₁ h₂ hle

/-- A complex matrix has all-real entries.-/
def IsRealMatrix {m p : ℕ} (A : Matrix (Fin m) (Fin p) ℂ) : Prop :=
  ∀ (i : Fin m) (j : Fin p), (A i j).im = 0

/-! ## MatrixSVD structure -/

/-- The SVD of a matrix over 𝕜 (ℝ or ℂ), bundling U, S, V and all properties.-/
structure MatrixSVD {𝕜 : Type*} [RCLike 𝕜] {m p : ℕ} (A : Matrix (Fin m) (Fin p) 𝕜) where
  /-- The left unitary factor (m × m).-/
  U : Matrix (Fin m) (Fin m) 𝕜
  /-- The real SVD-diagonal factor (m × p).-/
  S : Matrix (Fin m) (Fin p) ℝ
  /-- The right unitary factor (p × p).-/
  V : Matrix (Fin p) (Fin p) 𝕜
  /-- U is unitary.-/
  hU_unitary : IsUnitary U
  /-- V is unitary.-/
  hV_unitary : IsUnitary V
  /-- S is SVD-diagonal (real, nonneg, non-increasing).-/
  hS_svdDiag : IsSVDDiag S
  /-- The decomposition identity A = U * S.map (algebraMap ℝ 𝕜) * Vᴴ.-/
  hA_eq : A = U * S.map (algebraMap ℝ 𝕜) * Vᴴ

/-! ## Matrix SVD existence (proved via spectral theorem) -/

section SVDExistence

variable {𝕜 : Type*} [RCLike 𝕜] {m p : ℕ}

/-! ### Eigenvalue/eigenvector setup -/

/-- The sorted eigenvalues of Aᴴ*A, indexed by Fin p (non-increasing, nonneg).-/
private noncomputable def svdEigval (A : Matrix (Fin m) (Fin p) 𝕜) (j : Fin p) : ℝ :=
  (isHermitian_conjTranspose_mul_self A).eigenvalues₀
    ⟨j.val, (Fintype.card_fin p).symm ▸ j.isLt⟩

/-- The ONB of eigenvectors of Aᴴ*A, reindexed to Fin p.-/
private noncomputable def svdONB (A : Matrix (Fin m) (Fin p) 𝕜) :
    OrthonormalBasis (Fin p) 𝕜 (EuclideanSpace 𝕜 (Fin p)) :=
  ((isSymmetric_toEuclideanLin_iff.symm.1 (isHermitian_conjTranspose_mul_self A)).eigenvectorBasis
    finrank_euclideanSpace).reindex (finCongr (Fintype.card_fin p))

private lemma svdEigval_antitone (A : Matrix (Fin m) (Fin p) 𝕜) :
    Antitone (svdEigval A) := by
  intro a b hab
  exact (isHermitian_conjTranspose_mul_self A).eigenvalues₀_antitone hab

private lemma svdEigval_nonneg (A : Matrix (Fin m) (Fin p) 𝕜) (j : Fin p) :
    0 ≤ svdEigval A j := by
  unfold svdEigval
  have hA := isHermitian_conjTranspose_mul_self A
  -- eigenvalues₀ k = eigenvalues (e k) where e : Fin (card (Fin p)) ≃ Fin p
  have heq : ∀ k, hA.eigenvalues₀ k =
      hA.eigenvalues ((Fintype.equivOfCardEq (Fintype.card_fin _) : Fin (Fintype.card (Fin p)) ≃ Fin p) k) := by
    intro k
    simp [Matrix.IsHermitian.eigenvalues, Equiv.symm_apply_apply]
  rw [heq]
  exact eigenvalues_conjTranspose_mul_self_nonneg A _

private lemma mulVec_svdONB (A : Matrix (Fin m) (Fin p) 𝕜) (j : Fin p) :
    (Aᴴ * A) *ᵥ (svdONB A j).ofLp = (svdEigval A j : 𝕜) • (svdONB A j).ofLp := by
  set sym := isSymmetric_toEuclideanLin_iff.symm.1 (isHermitian_conjTranspose_mul_self A)
  set k := (finCongr (Fintype.card_fin p)).symm j
  -- svdONB A j = sym.eigenvectorBasis finrank_euclideanSpace k (by reindex)
  have hv : (svdONB A j : EuclideanSpace 𝕜 (Fin p)) = sym.eigenvectorBasis finrank_euclideanSpace k := by
    simp only [svdONB, OrthonormalBasis.reindex_apply]; congr 1
  -- svdEigval A j = sym.eigenvalues finrank_euclideanSpace k
  have heval : svdEigval A j = sym.eigenvalues finrank_euclideanSpace k := by
    simp only [svdEigval, Matrix.IsHermitian.eigenvalues₀]; congr 1
  -- The eigenvector equation at the LinearMap level
  have heig := sym.apply_eigenvectorBasis finrank_euclideanSpace k
  -- heig : toLpLin 2 2 (Aᴴ * A) (eigvec k) = (eigenvalue k : 𝕜) • eigvec k
  -- Take ofLp of both sides
  have := congr_arg WithLp.ofLp heig
  simp only [toLpLin_apply, WithLp.ofLp_toLp, WithLp.ofLp_smul] at this
  rw [← hv, ← heval] at this
  exact this

/-! ### V and S construction -/

private noncomputable def svdV (A : Matrix (Fin m) (Fin p) 𝕜) : Matrix (Fin p) (Fin p) 𝕜 :=
  (EuclideanSpace.basisFun (Fin p) 𝕜).toBasis.toMatrix (svdONB A).toBasis

private lemma svdV_unitary (A : Matrix (Fin m) (Fin p) 𝕜) : IsUnitary (svdV A) := by
  have := (EuclideanSpace.basisFun (Fin p) 𝕜).toMatrix_orthonormalBasis_mem_unitary (svdONB A)
  rwa [Matrix.mem_unitaryGroup_iff'] at this

private noncomputable def svdS (A : Matrix (Fin m) (Fin p) 𝕜) : Matrix (Fin m) (Fin p) ℝ :=
  fun i j => if (i : ℕ) = (j : ℕ) then Real.sqrt (svdEigval A j) else 0

private lemma svdS_isSVDDiag (A : Matrix (Fin m) (Fin p) 𝕜) : IsSVDDiag (svdS A) := by
  refine ⟨fun i j hij => ?_, fun i j hij => ?_, fun i₁ i₂ j₁ j₂ h₁ h₂ hle => ?_⟩
  · simp [svdS, hij]
  · simp only [svdS, hij, ite_true]; exact Real.sqrt_nonneg _
  · simp only [svdS, h₁, h₂, ite_true]
    exact Real.sqrt_le_sqrt (svdEigval_antitone A (show j₁ ≤ j₂ by omega))

/-! ### U construction -/

private noncomputable def svdPartialU (A : Matrix (Fin m) (Fin p) 𝕜) :
    Fin m → EuclideanSpace 𝕜 (Fin m) := fun i =>
  if h : ∃ j : Fin p, (j : ℕ) = (i : ℕ) ∧ svdEigval A j ≠ 0 then
    ((Real.sqrt (svdEigval A (Classical.choose h)))⁻¹ : 𝕜) •
      (WithLp.toLp 2 (A *ᵥ (svdONB A (Classical.choose h)).ofLp) : EuclideanSpace 𝕜 (Fin m))
  else 0

private def svdActiveSet (A : Matrix (Fin m) (Fin p) 𝕜) : Set (Fin m) :=
  {i | ∃ j : Fin p, (j : ℕ) = (i : ℕ) ∧ svdEigval A j ≠ 0}

private lemma svdPartialU_orthonormal (A : Matrix (Fin m) (Fin p) 𝕜) :
    Orthonormal 𝕜 ((svdActiveSet A).domRestrict (svdPartialU A)) := by
  rw [orthonormal_iff_ite]
  intro ⟨i₁, hi₁⟩ ⟨i₂, hi₂⟩
  set j₁ := Classical.choose hi₁
  set j₂ := Classical.choose hi₂
  have hj₁_val : (j₁ : ℕ) = (i₁ : ℕ) := (Classical.choose_spec hi₁).1
  have hj₁_ne : svdEigval A j₁ ≠ 0 := (Classical.choose_spec hi₁).2
  have hj₂_val : (j₂ : ℕ) = (i₂ : ℕ) := (Classical.choose_spec hi₂).1
  have hj₂_ne : svdEigval A j₂ ≠ 0 := (Classical.choose_spec hi₂).2
  have hu₁ : svdPartialU A i₁ = ((Real.sqrt (svdEigval A j₁))⁻¹ : 𝕜) •
      (WithLp.toLp 2 (A *ᵥ (svdONB A j₁).ofLp) : EuclideanSpace 𝕜 (Fin m)) :=
    dite_eq_left hi₁
  have hu₂ : svdPartialU A i₂ = ((Real.sqrt (svdEigval A j₂))⁻¹ : 𝕜) •
      (WithLp.toLp 2 (A *ᵥ (svdONB A j₂).ofLp) : EuclideanSpace 𝕜 (Fin m)) :=
    dite_eq_left hi₂
  simp only [Set.domRestrict, hu₁, hu₂]
  rw [inner_smul_left, inner_smul_right]
  -- Compute inner product using inner_toLp_toLp: <toLp x, toLp y> = y . star x
  have inner_Av : @inner 𝕜 (EuclideanSpace 𝕜 (Fin m)) _
      (WithLp.toLp 2 (A *ᵥ (svdONB A j₁).ofLp))
      (WithLp.toLp 2 (A *ᵥ (svdONB A j₂).ofLp)) =
      (svdEigval A j₂ : 𝕜) * @inner 𝕜 (EuclideanSpace 𝕜 (Fin p)) _
        (svdONB A j₁) (svdONB A j₂) := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct]
    -- Goal: (A *ᵥ v₂) ⬝ᵥ star (A *ᵥ v₁) = eigval₂ * (v₂ ⬝ᵥ star v₁)
    rw [star_mulVec, dotProduct_comm (A *ᵥ _), dotProduct_mulVec, vecMul_vecMul,
        ← dotProduct_mulVec, mulVec_svdONB, dotProduct_smul, smul_eq_mul, dotProduct_comm]
  rw [inner_Av]
  have honb := (svdONB A).orthonormal
  simp only [Subtype.mk.injEq]
  by_cases h : i₁ = i₂
  · have hj_eq : j₁ = j₂ := Fin.ext (by omega)
    rw [ite_eq_left h, hj_eq]
    rw [orthonormal_iff_ite.mp honb j₂ j₂, ite_eq_left rfl, mul_one]
    have hσ_ne : (Real.sqrt (svdEigval A j₂) : 𝕜) ≠ 0 :=
      RCLike.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr
        (lt_of_le_of_ne (svdEigval_nonneg A j₂) (Ne.symm hj₂_ne))))
    have hsqeig : (svdEigval A j₂ : 𝕜) =
        (Real.sqrt (svdEigval A j₂) : 𝕜) * (Real.sqrt (svdEigval A j₂) : 𝕜) := by
      rw [← RCLike.ofReal_mul, Real.mul_self_sqrt (svdEigval_nonneg A j₂)]
    rw [hsqeig]
    simp only [map_inv₀, RCLike.conj_ofReal]
    field_simp
  · have hj_ne : j₁ ≠ j₂ := fun h' => h (Fin.ext (by omega))
    rw [orthonormal_iff_ite.mp honb j₁ j₂, ite_eq_right hj_ne, mul_zero, mul_zero, mul_zero, ite_eq_right h]

private noncomputable def svdUONB (A : Matrix (Fin m) (Fin p) 𝕜) :
    OrthonormalBasis (Fin m) 𝕜 (EuclideanSpace 𝕜 (Fin m)) :=
  ((svdPartialU_orthonormal A).exists_orthonormalBasis_extension_of_card_eq
    finrank_euclideanSpace).choose

private noncomputable def svdUMatrix (A : Matrix (Fin m) (Fin p) 𝕜) :
    Matrix (Fin m) (Fin m) 𝕜 :=
  (EuclideanSpace.basisFun (Fin m) 𝕜).toBasis.toMatrix (svdUONB A).toBasis

private lemma basis_toMatrix_onb_unitary {k : ℕ} (b : OrthonormalBasis (Fin k) 𝕜 (EuclideanSpace 𝕜 (Fin k))) :
    IsUnitary ((EuclideanSpace.basisFun (Fin k) 𝕜).toBasis.toMatrix b.toBasis) := by
  unfold IsUnitary
  have hmem := (EuclideanSpace.basisFun (Fin k) 𝕜).toMatrix_orthonormalBasis_mem_unitary b
  rwa [Matrix.mem_unitaryGroup_iff'] at hmem

private lemma svdUMatrix_unitary (A : Matrix (Fin m) (Fin p) 𝕜) :
    IsUnitary (svdUMatrix A) := by
  unfold svdUMatrix
  exact basis_toMatrix_onb_unitary _

/-! ### Main decomposition -/

/-- The ONB extension property: for indices in the active set, the U ONB agrees
    with the partial U construction.-/
private lemma svdUONB_eq_partialU (A : Matrix (Fin m) (Fin p) 𝕜)
    (i : Fin m) (hi : i ∈ svdActiveSet A) :
    svdUONB A i = svdPartialU A i :=
  ((svdPartialU_orthonormal A).exists_orthonormalBasis_extension_of_card_eq
    finrank_euclideanSpace).choose_spec i hi

-- Helper: if eigval = 0 then A *ᵥ (eigvec) = 0
private lemma mulVec_svdONB_eq_zero (A : Matrix (Fin m) (Fin p) 𝕜) (j : Fin p)
    (hj : svdEigval A j = 0) :
    A *ᵥ (svdONB A j).ofLp = 0 := by
  have heig := mulVec_svdONB A j
  rw [hj, RCLike.ofReal_zero, zero_smul] at heig
  -- Show ⟪toLp(Av), toLp(Av)⟫ = 0 using the eigenvector equation
  set v := (svdONB A j).ofLp
  set Av_lp : EuclideanSpace 𝕜 (Fin m) := WithLp.toLp 2 (A *ᵥ v)
  have hinner : @inner 𝕜 (EuclideanSpace 𝕜 (Fin m)) _ Av_lp Av_lp = 0 := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct, Av_lp]
    -- Goal: A *ᵥ v ⬝ᵥ star (A *ᵥ v) = 0
    have hstar : star (A *ᵥ v) ⬝ᵥ (A *ᵥ v) = 0 := by
      rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, heig, dotProduct_zero]
    rw [← starRingEnd_self_apply (A *ᵥ v ⬝ᵥ star (A *ᵥ v))]
    simp only [dotProduct_comm (A *ᵥ v) (star (A *ᵥ v)), hstar, map_zero]
  have hAv_zero : Av_lp = 0 := (inner_self_eq_zero (𝕜 := 𝕜)).mp hinner
  have : A *ᵥ v = WithLp.ofLp Av_lp := (WithLp.ofLp_toLp 2 (A *ᵥ v)).symm
  rw [this, hAv_zero]; rfl

-- The SVD decomposition identity A = U * S.map (algebraMap ℝ 𝕜) * V^H.
private lemma svd_eq (A : Matrix (Fin m) (Fin p) 𝕜) :
    A = svdUMatrix A * (svdS A).map (algebraMap ℝ 𝕜) * (svdV A)ᴴ := by
  -- Strategy: suffices A * V = U * S, then right-multiply by Vᴴ
  suffices h : A * svdV A = svdUMatrix A * (svdS A).map (algebraMap ℝ 𝕜) by
    have hVu := svdV_unitary A
    calc A = A * (svdV A * (svdV A)ᴴ) := by rw [hVu.mul_conjTranspose_self, Matrix.mul_one]
      _ = A * svdV A * (svdV A)ᴴ := by rw [Matrix.mul_assoc]
      _ = svdUMatrix A * (svdS A).map (algebraMap ℝ 𝕜) * (svdV A)ᴴ := by rw [h]
  -- Show A * V = U * S entry-by-entry
  ext i j
  -- LHS = (A *ᵥ (onb j).ofLp) i
  have hLHS : (A * svdV A) i j = (A *ᵥ (svdONB A j).ofLp) i := by
    simp only [Matrix.mul_apply, mulVec, dotProduct, svdV,
      Module.Basis.toMatrix_apply, EuclideanSpace.basisFun_repr]
    rfl
  rw [hLHS]
  -- RHS: expand and simplify diagonal S
  simp only [Matrix.mul_apply, Matrix.map_apply, svdS]
  -- Case split on eigval
  by_cases hev : svdEigval A j = 0
  · -- eigval = 0: Av = 0 and √eigval = 0
    have hAv := mulVec_svdONB_eq_zero A j hev
    simp only [hAv, Pi.zero_apply, hev, Real.sqrt_zero, map_zero, ite_self, mul_zero,
      Finset.sum_const_zero]
  · -- eigval ≠ 0
    by_cases hjm : (j : ℕ) < m
    · -- j.val < m: exactly one term survives
      set k₀ : Fin m := ⟨j.val, hjm⟩
      rw [Finset.sum_eq_single_of_mem k₀ (Finset.mem_univ _)]
      · -- Main term: k₀.val = j.val, so the if is true
        simp only [k₀, show (⟨j.val, hjm⟩ : Fin m).val = (j : ℕ) from rfl, ite_true]
        -- Need: svdUMatrix A i k₀ * √eigval = (Av) i
        have hactive : k₀ ∈ svdActiveSet A := ⟨j, rfl, hev⟩
        have hueq := svdUONB_eq_partialU A k₀ hactive
        -- Classical.choose hactive = j
        have hcc : Classical.choose hactive = j :=
          Fin.ext (Classical.choose_spec hactive).1
        -- svdPartialU A k₀ = (√eigval)⁻¹ • toLp(Av)
        have hpu : svdPartialU A k₀ = ((Real.sqrt (svdEigval A j))⁻¹ : 𝕜) •
            (WithLp.toLp 2 (A *ᵥ (svdONB A j).ofLp) : EuclideanSpace 𝕜 (Fin m)) := by
          show svdPartialU A k₀ = _
          unfold svdPartialU
          split
          · next h =>
            have hj_eq : Classical.choose h = j :=
              Fin.ext (Classical.choose_spec h).1
            simp only [hj_eq]
          · next h => exact absurd hactive h
        -- U entry = (svdUONB A k₀) i = (svdPartialU A k₀) i = (1/σ) * (Av) i
        have hUik : svdUMatrix A i k₀ =
            ((Real.sqrt (svdEigval A j))⁻¹ : 𝕜) * (A *ᵥ (svdONB A j).ofLp) i := by
          -- svdUMatrix A i k₀ = (basisFun.toBasis.toMatrix uonb.toBasis) i k₀
          -- = basisFun.repr (uonb k₀) i = (uonb k₀) i
          -- = (partialU k₀) i  (by hueq)
          -- = ((√eigval)⁻¹ • toLp(Av)) i  (by hpu)
          -- = (√eigval)⁻¹ * (Av) i
          have : svdUMatrix A i k₀ = (svdUONB A k₀ : EuclideanSpace 𝕜 (Fin m)) i := by
            simp [svdUMatrix, Module.Basis.toMatrix_apply, EuclideanSpace.basisFun_repr]
          rw [this, hueq, hpu]
          simp [Pi.smul_apply, smul_eq_mul, WithLp.ofLp_toLp]
        rw [hUik]
        -- (√eigval)⁻¹ * (Av i) * √eigval = (Av i)
        have hσ_ne : (Real.sqrt (svdEigval A j) : 𝕜) ≠ 0 :=
          RCLike.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr
            (lt_of_le_of_ne (svdEigval_nonneg A j) (Ne.symm hev))))
        field_simp
      · -- Other terms vanish: k.val ≠ j.val
        intro k _ hk
        have : ¬((k : ℕ) = (j : ℕ)) := fun h => hk (Fin.ext h)
        simp [this]
    · -- j.val ≥ m and eigval ≠ 0: impossible
      -- By antitone, all eigvals for indices 0..j are nonzero.
      -- This gives m+1 orthonormal vectors in 𝕜^m, contradiction.
      exfalso
      have hev_all : ∀ k : Fin p, (k : ℕ) ≤ (j : ℕ) → svdEigval A k ≠ 0 := by
        intro k hk habs
        have h1 : svdEigval A j ≤ svdEigval A k := svdEigval_antitone A hk
        have h2 : 0 ≤ svdEigval A j := svdEigval_nonneg A j
        exact hev (le_antisymm (habs ▸ h1) h2)
      -- Build m+1 orthonormal vectors
      set f : Fin (m + 1) → EuclideanSpace 𝕜 (Fin m) := fun k =>
        let kp : Fin p := ⟨k.val, by omega⟩
        ((Real.sqrt (svdEigval A kp))⁻¹ : 𝕜) •
          (WithLp.toLp 2 (A *ᵥ (svdONB A kp).ofLp) : EuclideanSpace 𝕜 (Fin m))
      have hf_on : Orthonormal 𝕜 f := by
        rw [orthonormal_iff_ite]
        intro ⟨a, ha⟩ ⟨b, hb⟩
        simp only [f]
        set ka : Fin p := ⟨a, by omega⟩
        set kb : Fin p := ⟨b, by omega⟩
        rw [inner_smul_left, inner_smul_right]
        have inner_Av : @inner 𝕜 (EuclideanSpace 𝕜 (Fin m)) _
            (WithLp.toLp 2 (A *ᵥ (svdONB A ka).ofLp))
            (WithLp.toLp 2 (A *ᵥ (svdONB A kb).ofLp)) =
            (svdEigval A kb : 𝕜) * @inner 𝕜 (EuclideanSpace 𝕜 (Fin p)) _
              (svdONB A ka) (svdONB A kb) := by
          simp only [EuclideanSpace.inner_eq_star_dotProduct]
          rw [star_mulVec, dotProduct_comm (A *ᵥ _), dotProduct_mulVec, vecMul_vecMul,
              ← dotProduct_mulVec, mulVec_svdONB, dotProduct_smul, smul_eq_mul, dotProduct_comm]
        rw [inner_Av]
        have honb := (svdONB A).orthonormal
        by_cases hab : a = b
        · subst hab
          have hka_ne := hev_all ka (show (ka : ℕ) ≤ (j : ℕ) by simp [ka]; omega)
          rw [show ka = kb from rfl, orthonormal_iff_ite.mp honb kb kb, ite_eq_left rfl, mul_one,
              ite_eq_left rfl]
          have hσ_ne : (Real.sqrt (svdEigval A kb) : 𝕜) ≠ 0 :=
            RCLike.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr
              (lt_of_le_of_ne (svdEigval_nonneg A kb) (Ne.symm hka_ne))))
          rw [show (svdEigval A kb : 𝕜) =
              (Real.sqrt (svdEigval A kb) : 𝕜) * (Real.sqrt (svdEigval A kb) : 𝕜) from by
            rw [← RCLike.ofReal_mul, Real.mul_self_sqrt (svdEigval_nonneg A kb)]]
          simp only [map_inv₀, RCLike.conj_ofReal]
          field_simp
        · have hkab : ka ≠ kb := fun h => hab (by simp [ka, kb] at h; exact h)
          rw [orthonormal_iff_ite.mp honb ka kb, ite_eq_right hkab, mul_zero, mul_zero, mul_zero,
              ite_eq_right (fun h => hab (Fin.mk.inj h))]
      -- m + 1 orthonormal vectors in 𝕜^m contradicts finrank = m
      have := hf_on.linearIndependent.fintype_card_le_finrank
      simp [finrank_euclideanSpace] at this

/-- **Matrix SVD existence**.
    Every matrix over an `RCLike` field has a singular value decomposition.-/
noncomputable def matrix_svd (m p : ℕ) (A : Matrix (Fin m) (Fin p) 𝕜) : MatrixSVD A :=
  { U := svdUMatrix A
    S := svdS A
    V := svdV A
    hU_unitary := svdUMatrix_unitary A
    hV_unitary := svdV_unitary A
    hS_svdDiag := svdS_isSVDDiag A
    hA_eq := svd_eq A }

/-! ### Real-to-complex SVD lifting -/

/-- Extract the real part of a complex matrix with all-real entries.-/
noncomputable def realPartMatrix {m p : ℕ} (A : Matrix (Fin m) (Fin p) ℂ)
    (_hA : IsRealMatrix A) : Matrix (Fin m) (Fin p) ℝ :=
  fun i j => (A i j).re

/--
@isnad1 id=eq.1h3v.s5.4bb2d3713888 from=translated src=- shape=27b36f3e vocab=74d208ca
-/
lemma realPartMatrix_map_eq {m p : ℕ} (A : Matrix (Fin m) (Fin p) ℂ)
    (hA : IsRealMatrix A) : (realPartMatrix A hA).map Complex.ofReal = A := by
  ext i j
  simp only [realPartMatrix, Matrix.map_apply]
  have him := hA i j
  apply Complex.ext <;> simp [him]

private lemma real_map_ofReal_unitary {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : Mᴴ * M = 1) : IsUnitary (M.map Complex.ofReal) := by
  show (M.map Complex.ofReal)ᴴ * M.map Complex.ofReal = 1
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply,
    Matrix.one_apply, Complex.star_def, Complex.conj_ofReal]
  rw [show (∑ k, ↑(M k i) * ↑(M k j)) = (↑(∑ k, M k i * M k j) : ℂ) from by push_cast; ring]
  have := congr_fun₂ hM i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial, Matrix.one_apply] at this
  rw [this]; split_ifs <;> simp

private lemma isRealMatrix_map_ofReal {m p : ℕ} (B : Matrix (Fin m) (Fin p) ℝ) :
    IsRealMatrix (B.map Complex.ofReal) := by
  intro i j
  simp [Matrix.map_apply, Complex.ofReal_im]

/-- Lift a real SVD to a complex SVD by embedding U, V via ofReal.-/
noncomputable def MatrixSVD.toComplex {m p : ℕ} {A : Matrix (Fin m) (Fin p) ℝ}
    (svd : MatrixSVD A) : MatrixSVD (A.map (algebraMap ℝ ℂ)) :=
  have hVc_conj : (svd.V.map Complex.ofReal)ᴴ = (svd.Vᴴ).map Complex.ofReal :=
    (conjTranspose_map Complex.ofReal (fun x => by simp [Complex.conj_ofReal])).symm
  have hmap_id : svd.S.map (algebraMap ℝ ℝ) = svd.S := by
    ext i j; simp [Matrix.map_apply]
  have hA_decomp : A.map (algebraMap ℝ ℂ) =
      svd.U.map Complex.ofReal * (svd.S).map (algebraMap ℝ ℂ) *
      (svd.V.map Complex.ofReal)ᴴ := by
    rw [hVc_conj]
    conv_lhs => rw [svd.hA_eq, hmap_id]
    change (svd.U * svd.S * svd.Vᴴ).map (Complex.ofRealHom : ℝ →+* ℂ) =
      svd.U.map (Complex.ofRealHom : ℝ →+* ℂ) *
        svd.S.map (Complex.ofRealHom : ℝ →+* ℂ) *
          (svd.Vᴴ).map (Complex.ofRealHom : ℝ →+* ℂ)
    rw [Matrix.map_mul, Matrix.map_mul]
  { U := svd.U.map Complex.ofReal
    S := svd.S
    V := svd.V.map Complex.ofReal
    hU_unitary := real_map_ofReal_unitary _ svd.hU_unitary.conjTranspose_mul_self
    hV_unitary := real_map_ofReal_unitary _ svd.hV_unitary.conjTranspose_mul_self
    hS_svdDiag := svd.hS_svdDiag
    hA_eq := hA_decomp }

/-- The U factor of a real SVD lifted to complex has all-real entries.
@isnad1 id=isrealma.0h4v.s7.c1ba968a38a8 from=translated src=- shape=ab4064b5 vocab=1a3b6ad7
-/
theorem MatrixSVD.toComplex_isRealMatrix_U {m p : ℕ} {A : Matrix (Fin m) (Fin p) ℝ}
    (svd : MatrixSVD A) : IsRealMatrix svd.toComplex.U :=
  isRealMatrix_map_ofReal _

/-- The V factor of a real SVD lifted to complex has all-real entries.
@isnad1 id=isrealma.0h4v.s7.fc61ba260e68 from=translated src=- shape=e3bdb440 vocab=eea5f112
-/
theorem MatrixSVD.toComplex_isRealMatrix_V {m p : ℕ} {A : Matrix (Fin m) (Fin p) ℝ}
    (svd : MatrixSVD A) : IsRealMatrix svd.toComplex.V :=
  isRealMatrix_map_ofReal _

end SVDExistence

/-! ## Rank-k truncation of an SVD-diagonal matrix -/

/-- Truncate an SVD-diagonal matrix at rank k: keep the first k diagonal
    singular values, zero out everything else.-/
noncomputable def svdTrunc {m p : ℕ} (S : Matrix (Fin m) (Fin p) ℝ)
    (_hS : IsSVDDiag S) (k : ℕ) : Matrix (Fin m) (Fin p) ℝ :=
  fun i j => if (i : ℕ) < k ∧ (i : ℕ) = (j : ℕ) then S i j else 0

/-- svdTrunc preserves IsSVDDiag.
@isnad1 id=issvddia.1h4v.s4.f03040adc04c from=translated src=- shape=8358ba36 vocab=417f10b5
-/
theorem isSVDDiag_svdTrunc {m p : ℕ} {S : Matrix (Fin m) (Fin p) ℝ}
    (hS : IsSVDDiag S) (k : ℕ) : IsSVDDiag (svdTrunc S hS k) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Off-diagonal zero
    intro i j hij
    simp only [svdTrunc, ite_eq_right (not_and_of_not_right _ hij)]
  · -- Diagonal nonneg
    intro i j hij
    simp only [svdTrunc]
    split_ifs with h
    · exact hS.2.1 i j hij
    · rfl
  · -- Non-increasing
    intro i₁ i₂ j₁ j₂ h₁ h₂ hle
    simp only [svdTrunc]
    -- The condition is (i < k ∧ i.val = j.val)
    by_cases hi₂ : (i₂ : ℕ) < k ∧ (i₂ : ℕ) = (j₂ : ℕ)
    · by_cases hi₁ : (i₁ : ℕ) < k ∧ (i₁ : ℕ) = (j₁ : ℕ)
      · rw [ite_eq_left hi₂, ite_eq_left hi₁]; exact hS.2.2 i₁ i₂ j₁ j₂ h₁ h₂ hle
      · -- i₂ satisfies but i₁ doesn't: impossible (i₁ ≤ i₂ < k, and h₁ gives i₁=j₁)
        exfalso; apply hi₁; exact ⟨by omega, h₁⟩
    · by_cases hi₁ : (i₁ : ℕ) < k ∧ (i₁ : ℕ) = (j₁ : ℕ)
      · rw [ite_eq_right hi₂, ite_eq_left hi₁]; exact hS.2.1 i₁ j₁ h₁
      · rw [ite_eq_right hi₂, ite_eq_right hi₁]

/-! ## MatrixSVD methods -/

/-- The rank-k truncated SVD approximation.-/
noncomputable def MatrixSVD.truncApprox {m p : ℕ} {A : Matrix (Fin m) (Fin p) ℂ}
    (svd : MatrixSVD A) (k : ℕ) : Matrix (Fin m) (Fin p) ℂ :=
  svd.U * toComplexMatrix (svdTrunc svd.S svd.hS_svdDiag k) * svd.Vᴴ

/-- The rank of the truncated SVD is at most k.
@isnad1 id=le.0h5v.s5.5c8a123f221e from=translated src=- shape=bda02c4e vocab=384c48a2
-/
theorem MatrixSVD.rank_truncApprox_le {m p : ℕ} {A : Matrix (Fin m) (Fin p) ℂ}
    (svd : MatrixSVD A) (k : ℕ) :
    (svd.truncApprox k).rank ≤ k := by
  unfold truncApprox
  -- rank(U * Sk * Vᴴ) = rank(Sk) since U, Vᴴ are invertible
  have hUdet : IsUnit svd.U.det :=
    isUnit_det_of_left_inverse svd.hU_unitary.conjTranspose_mul_self
  have hVHdet : IsUnit svd.Vᴴ.det := by
    rw [det_conjTranspose]
    exact (isUnit_det_of_left_inverse svd.hV_unitary.conjTranspose_mul_self).star
  rw [Matrix.mul_assoc,
    rank_mul_eq_right_of_isUnit_det _ _ hUdet,
    rank_mul_eq_left_of_isUnit_det _ _ hVHdet]
  -- rank(toComplexMatrix(svdTrunc S k)) ≤ k
  -- Write Sk = P * Sℂ where P projects onto the first k rows.
  set w : Fin m → ℂ := fun i => if (i : ℕ) < k then 1 else 0
  have hPSk : toComplexMatrix (svdTrunc svd.S svd.hS_svdDiag k) =
      diagonal w * toComplexMatrix svd.S := by
    ext i j
    simp only [toComplexMatrix, svdTrunc, Matrix.map_apply, Matrix.mul_apply, w,
      diagonal_apply]
    by_cases h : (i : ℕ) < k
    · -- i < k: need to show if (i<k ∧ i=j) then S i j else 0 = sum with projection
      by_cases hij : (i : ℕ) = (j : ℕ)
      · -- diagonal entry: kept
        rw [ite_eq_left ⟨h, hij⟩]; symm
        rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _)]
        · simp [ite_eq_left h]
        · intro b _ hb; simp [show ¬(i = b) from fun h => hb h.symm]
      · -- off-diagonal entry: S i j = 0 by SVD-diag
        rw [ite_eq_right (not_and_of_not_right _ hij)]; symm
        rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _)]
        · simp [ite_eq_left h, svd.hS_svdDiag.1 i j hij]
        · intro b _ hb; simp [show ¬(i = b) from fun h => hb h.symm]
    · -- i ≥ k: everything zero
      rw [ite_eq_right (not_and_of_not_left _ h), Complex.ofReal_zero]; symm
      apply Finset.sum_eq_zero; intro b _
      simp only [ite_mul, one_mul, zero_mul]
      split_ifs with hb <;> simp_all
  rw [hPSk]
  calc (diagonal w * toComplexMatrix svd.S).rank
      ≤ (diagonal w).rank := rank_mul_le_left _ _
    _ ≤ k := by
        have := rank_diagonal w
        rw [this]
        -- #{i : Fin m | w i ≠ 0} ≤ k
        -- w i ≠ 0 iff (i : ℕ) < k
        have hw : ∀ i : Fin m, w i ≠ 0 ↔ (i : ℕ) < k := by
          intro i; simp only [w]; split_ifs with h <;> simp [h]
        -- Inject {i // w i ≠ 0} into Fin k
        apply le_trans (Fintype.card_le_of_injective
          (fun ⟨i, hi⟩ => (⟨(i : ℕ), (hw i).mp hi⟩ : Fin k))
          (fun ⟨a, _⟩ ⟨b, _⟩ h => by
            have := Fin.mk.inj h
            exact Subtype.ext (Fin.ext this)))
        simp

end TubalTensor
