import Tengoku.Nlalib.NLAlib.Matrix.Basic.Dilation
import Tengoku.Nlalib.NLAlib.Matrix.Basic.Orthonormal
import Tengoku.Nlalib.NLAlib.Matrix.Norms.Reindex
import Tengoku.Seed.Analysis.CStarAlgebra.Spectrum
import Tengoku.Nlalib.NLAlib.Matrix.Functions.ExpLogPosDef
import Tengoku.Seed.Data.Matrix.ColumnRowPartitioned
import Tengoku.Seed.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Hermitian calculus

Small facts about the functional calculus of Hermitian matrices over `[RCLike 𝕜]`, used
throughout the matrix concentration files, collected here so that each has one copy:

* spectral calculus of a Hermitian matrix: `matrixExp_smul_eq_cfc`, `traceExp_smul_eq_sum`,
  `le_of_mem_spectrum_of_lambdaMax_le`, `abs_le_norm_of_mem_spectrum`;
* Loewner bounds for the matrix exponential (moved from `Concentration/Matrix/BernsteinMgfCgf`):
  `one_add_smul_add_smul_sq_eq_cfc`, `matrixExp_smul_le_one_add_smul_add_smul_sq_of_spectrum_le`,
  `one_add_le_matrixExp_of_isHermitian`;
* reindexing: `reindexStarAlgEquiv`, `norm_reindex`, `lambdaMax_reindex`;
* the Hermitian dilation and block-diagonal matrices: `dilationLinearMap`, `dilation_sq`,
  `fromBlocks₁₁CLM`, `fromBlocks₂₂CLM`;
* block-diagonal positivity and norm: `posSemidef_fromBlocks_diag`, `norm_fromBlocks_diag`, and the
  isometric-compression bound `norm_conjTranspose_mul_mul_le`;
* the rank-one eigenvector projectors `eigenvectorProjector hA i` and the spectral decomposition
  `cfc_eq_sum_smul_eigenvectorProjector`.

The integral versions (`integral_reindex`, `integral_fromBlocks_diag`) are in
`NLAlib.Probability.Concentration.Basic.MatrixCalculus`. Tropp 2015, §2.1.

Atlas: support for `matrix-laplace`, `matrix-gaussian-series`, `matrix-chernoff`,
`matrix-bernstein`, `hermitian-dilation`, `intrinsic-dimension`.
-/

open scoped Matrix.Norms.L2Operator MatrixOrder

noncomputable section
namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜]

section Spectral

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- `Matrix d d 𝕜` (spectral norm) as a real normed algebra, with the entrywise real scalar
action `Matrix.instAlgebra` (so that Mathlib's Hermitian functional calculus instance applies
verbatim). Not an instance: it is introduced with `letI` inside proofs that call Mathlib's
real-exponential calculus (`CFC.real_exp_eq_normedSpace_exp`), where it is needed only for
abstract `𝕜`.-/
abbrev normedAlgebraRealMatrix : NormedAlgebra ℝ (Matrix d d 𝕜) where
  toAlgebra := Matrix.instAlgebra
  norm_smul_le r A := by
    rw [RCLike.real_smul_eq_coe_smul (K := 𝕜) r A]
    simpa using norm_smul_le (r : 𝕜) A

/-- For Hermitian `A`, `matrixExp (s • A)` is the functional calculus of `x ↦ exp (s x)` at `A`.
Tropp 2015, §2.1.11.
@isnad1 id=eq.1h4v.s8.019abd9c3347 from=translated src=- shape=7db56946 vocab=fd6e35cd
-/
theorem matrixExp_smul_eq_cfc (A : Matrix d d 𝕜) (hA : A.IsHermitian) (s : ℝ) :
    matrixExp (s • A) = cfc (fun x => Real.exp (s * x)) A := by
  letI := normedAlgebraRealMatrix (𝕜 := 𝕜) (d := d)
  rw [matrixExp, ← CFC.real_exp_eq_normedSpace_exp
    (hA.smul (isSelfAdjoint_iff.mpr (star_trivial s))),
    ← cfc_comp_const_mul s Real.exp A (by fun_prop) hA.isSelfAdjoint]

/-- For Hermitian `A`, `traceExp (θ • A) = ∑ i, exp (θ λᵢ)` over the eigenvalues of `A`. Tropp
2015, §3.1.
@isnad1 id=eq.1h4v.s7.d67c7be12238 from=translated src=- shape=d8a83de0 vocab=72b10eea
-/
theorem traceExp_smul_eq_sum (A : Matrix d d 𝕜) (hA : A.IsHermitian) (θ : ℝ) :
    traceExp (θ • A) = ∑ i, Real.exp (θ * hA.eigenvalues i) := by
  letI := normedAlgebraRealMatrix (𝕜 := 𝕜) (d := d)
  rw [traceExp, matrixExp,
    ← CFC.real_exp_eq_normedSpace_exp (hA.smul (isSelfAdjoint_iff.mpr (star_trivial θ)))]
  rw [← cfc_comp_const_mul θ Real.exp A (by fun_prop) hA.isSelfAdjoint, hA.cfc_eq]
  simp only [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  simp

/-- For Hermitian `A` with `lambdaMax A ≤ L`, every real spectral value of `A` is at most `L`.
Tropp 2015, §2.1.
@isnad1 id=le.3h5v.s7.183007c92211 from=translated src=- shape=68e3f821 vocab=975a2c0c
-/
theorem le_of_mem_spectrum_of_lambdaMax_le (A : Matrix d d 𝕜) (hA : A.IsHermitian) {L : ℝ}
    (hb : lambdaMax A ≤ L) : ∀ x ∈ spectrum ℝ A, x ≤ L := by
  intro x hx
  have hfin : (spectrum ℝ A).Finite := by
    rw [hA.spectrum_real_eq_range_eigenvalues]; exact Set.finite_range _
  exact (le_csSup hfin.bddAbove hx).trans hb

/-- A real spectral value of a square matrix is bounded in absolute value by its ℓ₂
operator norm. Tropp 2015, §2.1.
@isnad1 id=le.1h4v.s6.07181a897775 from=translated src=- shape=e4297b31 vocab=dddf3353
-/
theorem abs_le_norm_of_mem_spectrum [Nonempty d] (B : Matrix d d 𝕜) {x : ℝ}
    (hx : x ∈ spectrum ℝ B) : |x| ≤ ‖B‖ := by
  have h : algebraMap ℝ 𝕜 x ∈ spectrum 𝕜 B := (spectrum.algebraMap_mem_iff 𝕜).mpr hx
  have := spectrum.norm_le_norm_of_mem h
  simpa using this

/-- `1 + θ A + c A² = cfc (x ↦ 1 + θ x + c x²) A` for Hermitian `A`. Tropp 2015, §2.1.11;
helper for `matrix-bernstein` and `matrix-freedman`.
@isnad1 id=eq.1h5v.s9.26241297a061 from=translated src=- shape=43c8e984 vocab=2a07c13f
-/
theorem one_add_smul_add_smul_sq_eq_cfc (A : Matrix d d 𝕜) (hA : A.IsHermitian) (θ c : ℝ) :
    1 + θ • A + c • A ^ 2 = cfc (fun x => 1 + θ * x + c * x ^ 2) A := by
  have e1 := cfc_add A (fun x => 1 + θ * x) (fun x => c * x ^ 2)
  have e2 := cfc_const_add 1 (fun x => θ * x) A
  rw [e1, e2, cfc_const_mul_id θ A, cfc_const_mul c (fun x : ℝ => x ^ 2) A,
    cfc_pow_id A 2 hA.isSelfAdjoint, map_one]

/-- If `exp (θ x) ≤ 1 + θ x + c x²` on the spectrum of a Hermitian `A`, then
`exp (θ A) ≼ 1 + θ A + c A²`. Tropp 2015, Lemma 6.6.2; helper for `matrix-bernstein` and
`matrix-freedman`.
@isnad1 id=le.2h5v.s9.23b2e21e5725 from=translated src=- shape=86fba578 vocab=ebe5858c
-/
theorem matrixExp_smul_le_one_add_smul_add_smul_sq_of_spectrum_le
    (A : Matrix d d 𝕜) (hA : A.IsHermitian) {θ c : ℝ}
    (hb : ∀ x ∈ spectrum ℝ A, Real.exp (θ * x) ≤ 1 + θ * x + c * x ^ 2) :
    matrixExp (θ • A) ≤ 1 + θ • A + c • A ^ 2 := by
  rw [matrixExp_smul_eq_cfc A hA θ, one_add_smul_add_smul_sq_eq_cfc A hA θ c]
  exact cfc_mono hb

/-- `I + B ≼ exp B` for every Hermitian `B` (the tangent inequality `1 + x ≤ exp x` through the
functional calculus). Tropp 2015, §2.1.11; helper for `matrix-bernstein` and `matrix-freedman`.
@isnad1 id=le.1h3v.s7.4ac7b18870f1 from=translated src=- shape=895f60ae vocab=0ee88cbf
-/
theorem one_add_le_matrixExp_of_isHermitian (B : Matrix d d 𝕜) (hB : B.IsHermitian) :
    1 + B ≤ matrixExp B := by
  letI := normedAlgebraRealMatrix (𝕜 := 𝕜) (d := d)
  have e1 : 1 + B = cfc (fun x : ℝ => 1 + x) B := by
    rw [cfc_const_add (1 : ℝ) (fun x : ℝ => x) B, cfc_id' ℝ B hB.isSelfAdjoint, map_one]
  rw [matrixExp, ← CFC.real_exp_eq_normedSpace_exp hB, e1]
  exact cfc_mono (fun x _ => by linarith [Real.add_one_le_exp x])

end Spectral

section Reindex

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- `Matrix.reindex e e` as a `⋆`-algebra equivalence of square matrices over `𝕜`.-/
def reindexStarAlgEquiv (e : ι ≃ κ) : Matrix ι ι 𝕜 ≃⋆ₐ[𝕜] Matrix κ κ 𝕜 :=
  { Matrix.reindexAlgEquiv 𝕜 𝕜 e with
    map_star' := by intro A; rfl
    map_smul' := by intro r A; rfl }

/-- Reindexing preserves the ℓ₂ operator norm.
@isnad1 id=eq.0h5v.s6.3951a83a2f30 from=translated src=- shape=66caaf96 vocab=7992f1a6
-/
theorem norm_reindex (e : ι ≃ κ) (A : Matrix ι ι 𝕜) : ‖Matrix.reindex e e A‖ = ‖A‖ := by
  rw [← specNorm_eq_norm, ← specNorm_eq_norm, specNorm_reindex]

/-- Reindexing preserves the real spectrum: `spectrum ℝ (reindex e e A) = spectrum ℝ A`.
@isnad1 id=eq.0h5v.s7.4e8aa4963cad from=translated src=- shape=75713ffc vocab=03f91619
-/
theorem spectrum_reindex (e : ι ≃ κ) (A : Matrix ι ι 𝕜) :
    spectrum ℝ (Matrix.reindex e e A) = spectrum ℝ A := by
  have h := AlgEquiv.spectrum_eq (Matrix.reindexAlgEquiv ℝ 𝕜 e) A
  rwa [Matrix.coe_reindexAlgEquiv] at h

/-- Reindexing preserves the real spectrum, hence `lambdaMax`.
@isnad1 id=eq.0h5v.s6.3c3f56f440e4 from=translated src=- shape=2992681d vocab=48ae8754
-/
theorem lambdaMax_reindex (e : ι ≃ κ) (A : Matrix ι ι 𝕜) :
    lambdaMax (Matrix.reindex e e A) = lambdaMax A := by
  unfold lambdaMax
  rw [spectrum_reindex]

end Reindex

section Blocks

open Matrix

/-- The Hermitian dilation as a real-linear map. Tropp 2015, Def. 2.1.5. Atlas:
`hermitian-dilation`.-/
def dilationLinearMap (m n : Type*) : Matrix m n 𝕜 →ₗ[ℝ] Matrix (m ⊕ n) (m ⊕ n) 𝕜 where
  toFun := dilation
  map_add' X Y := by
    simp [dilation, Matrix.fromBlocks_add, Matrix.conjTranspose_add]
  map_smul' c X := by
    simp [dilation, Matrix.fromBlocks_smul, Matrix.conjTranspose_smul]

/-- `dilationLinearMap` applies `dilation`.
@isnad1 id=eq.0h4v.s8.bd5c1f1c4946 from=translated src=- shape=6c7be1b5 vocab=0002c1b1
-/
@[simp]
theorem dilationLinearMap_apply {m n : Type*} (X : Matrix m n 𝕜) :
    dilationLinearMap m n X = dilation X := rfl

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The square of the Hermitian dilation is block diagonal: `(dilation X)² =
fromBlocks (X Xᴴ) 0 0 (Xᴴ X)`. Tropp 2015, eq. (2.1.28). Atlas: `hermitian-dilation`.
@isnad1 id=eq.0h4v.s8.8fab59740946 from=translated src=- shape=07da72ba vocab=4d0acc37
-/
theorem dilation_sq (X : Matrix m n 𝕜) :
    dilation X ^ 2 = fromBlocks (X * Xᴴ) 0 0 (Xᴴ * X) := by
  simp [dilation, sq, fromBlocks_multiply]

variable (n) in
/-- The upper-left block inclusion `P ↦ fromBlocks P 0 0 0` as a continuous linear map.-/
def fromBlocks₁₁CLM : Matrix m m 𝕜 →L[𝕜] Matrix (m ⊕ n) (m ⊕ n) 𝕜 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun P => fromBlocks P 0 0 0
      map_add' := fun P P' => by rw [fromBlocks_add]; simp
      map_smul' := fun c P => by rw [fromBlocks_smul]; simp }

variable (m) in
/-- The lower-right block inclusion `Q ↦ fromBlocks 0 0 0 Q` as a continuous linear map.-/
def fromBlocks₂₂CLM : Matrix n n 𝕜 →L[𝕜] Matrix (m ⊕ n) (m ⊕ n) 𝕜 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun Q => fromBlocks 0 0 0 Q
      map_add' := fun Q Q' => by rw [fromBlocks_add]; simp
      map_smul' := fun c Q => by rw [fromBlocks_smul]; simp }

omit [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- `fromBlocks₁₁CLM` puts its argument in the upper-left block.
@isnad1 id=eq.0h4v.s9.08b095637ad4 from=translated src=- shape=9b6bfa9e vocab=61ec5cb9
-/
@[simp]
theorem fromBlocks₁₁CLM_apply (P : Matrix m m 𝕜) :
    fromBlocks₁₁CLM n P = fromBlocks P 0 0 0 := rfl

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
/-- `fromBlocks₂₂CLM` puts its argument in the lower-right block.
@isnad1 id=eq.0h4v.s9.96b100a45264 from=translated src=- shape=a8a81c8b vocab=16601c90
-/
@[simp]
theorem fromBlocks₂₂CLM_apply (Q : Matrix n n 𝕜) :
    fromBlocks₂₂CLM m Q = fromBlocks 0 0 0 Q := rfl

end Blocks

section BlockDiagonal

/-! ### Block-diagonal matrices: positivity and operator norm -/

open Matrix

variable {m n : Type*} [Fintype m] [Fintype n]

/-- A block-diagonal matrix `fromBlocks P 0 0 Q` with positive semidefinite diagonal blocks is
positive semidefinite (over any star-ordered commutative ring, in particular `ℝ` and `ℂ`).
Tropp 2015, §2.1.16 and §7.3; helper for `intrinsic-dimension`.
@isnad1 id=possemid.2h5v.s7.b727f24288df from=translated src=- shape=04e0e1d6 vocab=359852c7
-/
theorem posSemidef_fromBlocks_diag {R : Type*} [CommRing R] [PartialOrder R] [StarRing R]
    [StarOrderedRing R] {P : Matrix m m R} {Q : Matrix n n R}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) : (fromBlocks P 0 0 Q).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg
    (IsHermitian.fromBlocks hP.1 (by simp) hQ.1) fun x => ?_
  have e : star x ⬝ᵥ (fromBlocks P 0 0 Q *ᵥ x) =
      star (x ∘ Sum.inl) ⬝ᵥ (P *ᵥ (x ∘ Sum.inl)) +
        star (x ∘ Sum.inr) ⬝ᵥ (Q *ᵥ (x ∘ Sum.inr)) := by
    rw [fromBlocks_mulVec]
    simp [dotProduct, Fintype.sum_sum_type]
  rw [e]
  exact add_nonneg (hP.dotProduct_mulVec_nonneg _) (hQ.dotProduct_mulVec_nonneg _)

variable [DecidableEq m] [DecidableEq n]

/-- Compression by a matrix with orthonormal columns does not increase the L2 operator norm:
`‖Eᴴ M E‖ ≤ ‖M‖`. Tropp 2015, §2.1.16; helper for `hermitian-dilation` and
`intrinsic-dimension`.
@isnad1 id=le.1h5v.s7.dd6aca3cfd70 from=translated src=- shape=d977f77b vocab=1b25981c
-/
theorem norm_conjTranspose_mul_mul_le {k : Type*} [Fintype k] [DecidableEq k]
    {E : Matrix k m 𝕜} (hE : HasOrthonormalCols E) (M : Matrix k k 𝕜) :
    ‖Eᴴ * M * E‖ ≤ ‖M‖ := by
  have hE1 : ‖E‖ ≤ 1 := by
    have h1 : ‖(1 : Matrix m m 𝕜)‖ ≤ 1 := by
      rw [← diagonal_one, l2_opNorm_diagonal]
      exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun _ => by simp
    have h2 : ‖E‖ * ‖E‖ ≤ 1 := by
      rw [← l2_opNorm_conjTranspose_mul_self, hE.conjTranspose_mul_self]; exact h1
    nlinarith [norm_nonneg E]
  calc ‖Eᴴ * M * E‖ ≤ ‖Eᴴ * M‖ * ‖E‖ := l2_opNorm_mul _ _
    _ ≤ ‖Eᴴ‖ * ‖M‖ * ‖E‖ := by gcongr; exact l2_opNorm_mul _ _
    _ ≤ 1 * ‖M‖ * 1 := by
      rw [l2_opNorm_conjTranspose]; gcongr
    _ = ‖M‖ := by ring

/-- The L2 operator norm of a block-diagonal matrix is the larger of the block norms:
`‖fromBlocks P 0 0 Q‖ = max ‖P‖ ‖Q‖`. Tropp 2015, eq. (2.2.10) and (7.3.4); helper for
`hermitian-dilation` and `intrinsic-dimension`.
@isnad1 id=eq.0h5v.s7.c2a0354c2af9 from=translated src=- shape=65b96277 vocab=c10a2100
-/
theorem norm_fromBlocks_diag (P : Matrix m m 𝕜) (Q : Matrix n n 𝕜) :
    ‖fromBlocks P 0 0 Q‖ = max ‖P‖ ‖Q‖ := by
  apply le_antisymm
  · rw [cstar_norm_def]
    set c := max ‖P‖ ‖Q‖
    refine ContinuousLinearMap.opNorm_le_bound _ (le_max_of_le_left (norm_nonneg _)) fun x => ?_
    let x₁ : EuclideanSpace 𝕜 m := WithLp.toLp 2 (fun i => x (Sum.inl i))
    let x₂ : EuclideanSpace 𝕜 n := WithLp.toLp 2 (fun i => x (Sum.inr i))
    have h1 := l2_opNorm_mulVec P x₁
    have h2 := l2_opNorm_mulVec Q x₂
    have hx : ‖x‖ ^ 2 = ‖x₁‖ ^ 2 + ‖x₂‖ ^ 2 := by
      simp [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type, x₁, x₂]
    have hT : ‖toEuclideanCLM (n := m ⊕ n) (𝕜 := 𝕜) (fromBlocks P 0 0 Q) x‖ ^ 2 =
        ‖(EuclideanSpace.equiv m 𝕜).symm (P *ᵥ x₁)‖ ^ 2 +
          ‖(EuclideanSpace.equiv n 𝕜).symm (Q *ᵥ x₂)‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
      simp [fromBlocks_mulVec, Fintype.sum_sum_type, x₁, x₂, Function.comp_def]
    have hP : ‖P‖ ≤ c := le_max_left _ _
    have hQ : ‖Q‖ ≤ c := le_max_right _ _
    refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp ?_
    rw [hT, mul_pow, hx, mul_add]
    gcongr
    · calc _ ≤ (‖P‖ * ‖x₁‖) ^ 2 := by gcongr
        _ ≤ _ := by rw [mul_pow]; gcongr
    · calc _ ≤ (‖Q‖ * ‖x₂‖) ^ 2 := by gcongr
        _ ≤ _ := by rw [mul_pow]; gcongr
  · apply max_le
    · have h := norm_conjTranspose_mul_mul_le (E := fromRows (1 : Matrix m m 𝕜) (0 : Matrix n m 𝕜))
        (by ext i j; simp [mul_apply, Fintype.sum_sum_type, one_apply, eq_comm])
        (fromBlocks P 0 0 Q)
      have heq : P = (fromRows (1 : Matrix m m 𝕜) (0 : Matrix n m 𝕜))ᴴ * fromBlocks P 0 0 Q *
          (fromRows (1 : Matrix m m 𝕜) (0 : Matrix n m 𝕜)) := by
        ext i j; simp [mul_apply, Fintype.sum_sum_type, one_apply]
      exact (congrArg norm heq).trans_le h
    · have h := norm_conjTranspose_mul_mul_le (E := fromRows (0 : Matrix m n 𝕜) (1 : Matrix n n 𝕜))
        (by ext i j; simp [mul_apply, Fintype.sum_sum_type, one_apply, eq_comm])
        (fromBlocks P 0 0 Q)
      have heq : Q = (fromRows (0 : Matrix m n 𝕜) (1 : Matrix n n 𝕜))ᴴ * fromBlocks P 0 0 Q *
          (fromRows (0 : Matrix m n 𝕜) (1 : Matrix n n 𝕜)) := by
        ext i j; simp [mul_apply, Fintype.sum_sum_type, one_apply]
      exact (congrArg norm heq).trans_le h

end BlockDiagonal

section EigenProjections

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The **rank-one eigenvector projector** `U eᵢ eᵢᴴ Uᴴ = uᵢ uᵢᴴ` of a Hermitian matrix `A`
onto its `i`-th eigenvector `uᵢ`, where `U = hA.eigenvectorUnitary` is Mathlib's chosen
eigenvector basis (so the projector depends on that choice; it is a proof device, and the
basis-free object is the eigenspace projector `eigenspaceProjector hA ℓ` of
`Matrix/Perturbation/EigenspaceProjector.lean`). Tropp 2015, §2.1.6.-/
noncomputable def eigenvectorProjector {A : Matrix d d 𝕜} (hA : A.IsHermitian) (i : d) :
    Matrix d d 𝕜 :=
  (hA.eigenvectorUnitary : Matrix d d 𝕜) * Matrix.single i i 1 *
    star (hA.eigenvectorUnitary : Matrix d d 𝕜)

/-- **Spectral decomposition of the functional calculus**:
`cfc f A = ∑ᵢ f (λᵢ) • eigenvectorProjector hA i`. Tropp 2015, §2.1.6.
@isnad1 id=eq.1h4v.s8.db6471f2fa69 from=translated src=- shape=4f6659a0 vocab=4352ff88
-/
theorem cfc_eq_sum_smul_eigenvectorProjector {A : Matrix d d 𝕜} (hA : A.IsHermitian)
    (f : ℝ → ℝ) :
    cfc f A = ∑ i, f (hA.eigenvalues i) • eigenvectorProjector hA i := by
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
    ← Matrix.sum_single_eq_diagonal, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have : Matrix.single i i ((RCLike.ofReal ∘ f ∘ hA.eigenvalues) i : 𝕜)
      = f (hA.eigenvalues i) • (Matrix.single i i (1 : 𝕜)) := by
    rw [Matrix.smul_single]; simp [RCLike.real_smul_eq_coe_mul]
  rw [this, eigenvectorProjector, Matrix.mul_smul, Matrix.smul_mul]

/-- `c • A² = cfc (x ↦ c x²) A` for Hermitian `A`. Tropp 2015, §4.6 (helper).
@isnad1 id=eq.1h4v.s8.ec31e6e63f8e from=translated src=- shape=3e2d2b86 vocab=2c90695e
-/
theorem smul_sq_eq_cfc (A : Matrix d d 𝕜) (hA : A.IsHermitian) (c : ℝ) :
    c • A ^ 2 = cfc (fun x => c * x ^ 2) A := by
  rw [cfc_const_mul c (fun x : ℝ => x ^ 2) A, cfc_pow_id A 2 hA.isSelfAdjoint]

/-- `matrixExp (c • A²) = cfc (x ↦ exp (c x²)) A` for Hermitian `A`. Tropp 2015, §4.6 (helper).
@isnad1 id=eq.1h4v.s8.906b6a1d4265 from=translated src=- shape=37a27b8a vocab=689340db
-/
theorem matrixExp_smul_sq_eq_cfc (A : Matrix d d 𝕜) (hA : A.IsHermitian) (c : ℝ) :
    matrixExp (c • A ^ 2) = cfc (fun x => Real.exp (c * x ^ 2)) A := by
  rw [matrixExp_smul_eq_cfc (A ^ 2) (hA.pow 2) c,
    ← cfc_comp_pow (fun y => Real.exp (c * y)) 2 A (by fun_prop) hA.isSelfAdjoint]

end EigenProjections

end NLAlib
