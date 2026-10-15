/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/
module

public import Tengoku.LeanPool.LeanPool.QuantumParallelRepetition.Part01
public import Tengoku

/-! # Quantum parallel repetition, part 02 -/

@[expose] public section

noncomputable section

namespace QuantumParallelRepetition

/-- The local matrix norm instance used while elaborating part two. -/
noncomputable local instance matrixComplexContinuousENormPartTwo
    {m n : Type*} [Fintype m] [Fintype n] :
    ContinuousENorm (Matrix m n ℂ) :=
  @SeminormedAddGroup.toContinuousENorm (Matrix m n ℂ)
    (Matrix.normedAddCommGroup.toSeminormedAddCommGroup.toSeminormedAddGroup)

open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset

section

open scoped BigOperators

end

section

open WithLp
open scoped BigOperators Kronecker

/-- The quantum state representing e pr. -/
def ePRState (m : ℕ) :
    EuclideanSpace ℂ (Fin m × Fin m) :=
  toLp 2 fun q : Fin m × Fin m =>
    if q.1 = q.2 then
      (↑((Real.sqrt (m : ℝ))⁻¹) : ℂ)
    else
      0

/--
@isnad1 id=mem.0h2v.s6.5b544cd1644f from=translated src=- shape=5ea862ca vocab=3445821a
-/
theorem permutationMatrix_mem_unitary
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ : Equiv.Perm ι) :
    σ.permMatrix ℂ ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]
  simp only [inv_mul_cancel, permMatrix_one]

/-- The unitary operator implementing permutation. -/
def permutationUnitary
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ : Equiv.Perm ι) : Matrix.unitaryGroup ι ℂ :=
  ⟨σ.permMatrix ℂ, permutationMatrix_mem_unitary σ⟩

/--
@isnad1 id=eq.0h2v.s7.4ac034a099a1 from=translated src=- shape=3ba9fedf vocab=14a629a6
-/
@[simp] theorem permutationUnitary_val
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ : Equiv.Perm ι) :
    (permutationUnitary σ : Matrix ι ι ℂ) =
      σ.permMatrix ℂ := rfl

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

private def harmonicTensorSchmidtAmplitude
    {d n : ℕ} (σ : Fin d → ℝ) (q : Fin (d * n)) : ℝ :=
  let p : Fin d × Fin n := finProdFinEquiv.symm q
  σ p.1 * (Real.sqrt ((p.2.val : ℝ) + 1))⁻¹

private def descendingHarmonicSchmidtPermutation
    {d n : ℕ} (σ : Fin d → ℝ) : Equiv.Perm (Fin (d * n)) :=
  Tuple.sort (fun q : Fin (d * n) =>
    -harmonicTensorSchmidtAmplitude (n := n) σ q)

private def diagonalSchmidtUnitVector
    {d : ℕ} (σ : Fin d → ℝ)
    (hunit : (∑ i : Fin d, σ i ^ 2) = 1) :
    BipartiteUnitVector d := by
  refine ⟨diagonalSchmidtState σ, ?_⟩
  have hsquare := diagonalSchmidtState_norm_sq σ
  rw [hunit] at hsquare
  nlinarith [norm_nonneg (diagonalSchmidtState σ)]

private def harmonicSchmidtPermutationUnitary
    {d n : ℕ} (σ : Fin d → ℝ) :
    Matrix.unitaryGroup (Fin (d * n)) ℂ :=
  permutationUnitary
    (descendingHarmonicSchmidtPermutation
      (n := n) σ).symm

private def universalCatalystOverlapTerm
    {d n : ℕ} (σ : Fin d → ℝ)
    (k : Fin (d * n)) : ℝ :=
  ‖rawEmbezzlementState (d * n)‖⁻¹ *
    (Real.sqrt ((k.val : ℝ) + 1))⁻¹ *
    ‖rawEmbezzlementState n‖⁻¹ *
    harmonicTensorSchmidtAmplitude
      (n := n) σ
        (descendingHarmonicSchmidtPermutation
          (n := n) σ k)

private def harmonicTargetLiftUnitary
    {d n : ℕ}
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    Matrix.unitaryGroup (Fin (d * n)) ℂ := by
  let e : (Fin d × Fin n) ≃ Fin (d * n) :=
    finProdFinEquiv
  let M : Matrix (Fin d × Fin n) (Fin d × Fin n) ℂ :=
    (U.val ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))
  have hM : M ∈ Matrix.unitaryGroup (Fin d × Fin n) ℂ := by
    exact Matrix.kronecker_mem_unitary U.property
      (show (1 : Matrix (Fin n) (Fin n) ℂ) ∈
        Matrix.unitaryGroup (Fin n) ℂ from
          (Matrix.unitaryGroup (Fin n) ℂ).one_mem)
  refine ⟨(Matrix.reindex e e) M, ?_⟩
  rw [Matrix.mem_unitaryGroup_iff']
  have hstar :
      star ((Matrix.reindex e e) M) =
        (Matrix.reindex e e) (star M) := by
    ext i j
    simp only [reindex_apply, star_apply, submatrix_apply, RCLike.star_def, star_eq_conjTranspose,
      conjTranspose_apply]
  rw [hstar]
  change (Matrix.reindexRingEquiv ℂ e) (star M) *
    (Matrix.reindexRingEquiv ℂ e) M = 1
  rw [← (Matrix.reindexRingEquiv ℂ e).map_mul,
    (Matrix.mem_unitaryGroup_iff').mp hM]
  exact (Matrix.reindexRingEquiv ℂ e).map_one

@[simp] private theorem harmonicTargetLiftUnitary_apply
    {d n : ℕ}
    (U : Matrix.unitaryGroup (Fin d) ℂ)
    (a b : Fin d) (i j : Fin n) :
    harmonicTargetLiftUnitary (n := n) U
      (finProdFinEquiv (a, i))
      (finProdFinEquiv (b, j)) =
        if i = j then U a b else 0 := by
  change
    (Matrix.reindex finProdFinEquiv finProdFinEquiv
      (U.val ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)))
        (finProdFinEquiv (a, i))
        (finProdFinEquiv (b, j)) = _
  simp only [reindex_apply, submatrix_apply, Equiv.symm_apply_apply, kroneckerMap_apply,
    Matrix.one_apply, mul_ite, mul_one, mul_zero]

/-- The unitary operator implementing coherent shared random controlled. -/
def coherentSharedRandomControlledUnitary
    {Ω d : Type*}
    [Fintype Ω] [Fintype d]
    [DecidableEq Ω] [DecidableEq d]
    (U : Ω → Matrix.unitaryGroup d ℂ) :
    Matrix.unitaryGroup (Σ _ : Ω, d) ℂ := by
  refine ⟨Matrix.blockDiagonal' fun ω : Ω =>
    (U ω : Matrix d d ℂ), ?_⟩
  rw [Matrix.mem_unitaryGroup_iff',
    Matrix.star_eq_conjTranspose,
    Matrix.blockDiagonal'_conjTranspose,
    ← Matrix.blockDiagonal'_mul]
  have hblock (ω : Ω) :
      (U ω : Matrix d d ℂ).conjTranspose *
        (U ω : Matrix d d ℂ) = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff').mp (U ω).property
  simp_rw [hblock]
  ext ⟨ω, i⟩ ⟨ν, j⟩
  by_cases hων : ω = ν <;>
    by_cases hij : i = j <;>
      simp [Matrix.blockDiagonal'_apply,
        Matrix.one_apply, hων, hij]

/-- The positive operator-valued measurement implementing spectral partition. -/
def spectralPartitionPOVM
    {κ d : Type*}
    [Fintype κ] [Fintype d] [DecidableEq κ] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (bin : d → κ) : POVM κ d where
  effect k :=
    ∑ i ∈ Finset.univ.filter (fun i : d => bin i = k),
      positiveMatrixSpectralAtom F hF i
  positive k := by
    apply Matrix.posSemidef_sum
    intro i _
    exact positiveMatrixSpectralAtom_posSemidef F hF i
  complete := by
    classical
    calc
      (∑ k : κ,
        ∑ i ∈ Finset.univ.filter (fun i : d => bin i = k),
          positiveMatrixSpectralAtom F hF i) =
        ∑ i : d, positiveMatrixSpectralAtom F hF i := by
          simp only [sum_filter, sum_comm, sum_ite_eq, mem_univ, ↓reduceIte]
      _ = 1 := positiveMatrixSpectralAtom_sum F hF

/--
@isnad1 id=eq.1h5v.s6.00fa32bd7eaf from=translated src=- shape=3c18b57a vocab=ee5cb3bb
-/
theorem spectralPartitionPOVM_projective
    {κ d : Type*}
    [Fintype κ] [Fintype d] [DecidableEq κ] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (bin : d → κ) (k : κ) :
    (spectralPartitionPOVM F hF bin).effect k *
      (spectralPartitionPOVM F hF bin).effect k =
        (spectralPartitionPOVM F hF bin).effect k := by
  exact spectralAtomSum_mul_self F hF
    (Finset.univ.filter (fun i : d => bin i = k))

/-- Regroup two families of local indices into a family of paired indices. -/
def bilateralWorkPairEquiv
    {ι d e : Type*} :
    ((ι → d) × (ι → e)) ≃ (ι → d × e) where
  toFun x i := (x.1 i, x.2 i)
  invFun x := (fun i => (x i).1, fun i => (x i).2)
  left_inv x := by
    rcases x with ⟨a, b⟩
    rfl
  right_inv x := by
    funext i
    exact Prod.eta (x i)

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

/-- The `k`th point of a uniform grid with spacing `(upper - lower) / N`. -/
def finiteUniformThresholdGrid
    (lower upper : ℝ) (N : ℕ) (k : Fin N) : ℝ :=
  lower + (k.val : ℝ) * ((upper - lower) / (N : ℝ))

private def finiteUniformThresholdCrossing
    (lower upper a b : ℝ) (N : ℕ) : ℝ :=
  ((Finset.univ.filter fun k : Fin N =>
      min a b ≤ finiteUniformThresholdGrid lower upper N k ∧
        finiteUniformThresholdGrid lower upper N k ≤ max a b).card : ℝ) /
    (N : ℝ)

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

/-- The coefficient matrix of a bipartite vector, with Bob indexing its rows. -/
def targetCoefficientMatrix
    {d : ℕ} (ξ : BipartiteUnitVector d) :
    Matrix (Fin d) (Fin d) ℂ :=
  fun b a => ξ.val (a, b)

private theorem targetCoefficientMatrix_vec
    {d : ℕ} (ξ : BipartiteUnitVector d) :
    toLp 2 (Matrix.vec (targetCoefficientMatrix ξ)) = ξ.val := by
  ext ⟨a, b⟩
  rfl

private def targetReducedDensity
    {d : ℕ} (ξ : BipartiteUnitVector d) :
    Matrix (Fin d) (Fin d) ℂ :=
  (targetCoefficientMatrix ξ).conjTranspose *
    targetCoefficientMatrix ξ

private theorem targetReducedDensity_posSemidef
    {d : ℕ} (ξ : BipartiteUnitVector d) :
    (targetReducedDensity ξ).PosSemidef := by
  exact Matrix.posSemidef_conjTranspose_mul_self
    (targetCoefficientMatrix ξ)

private theorem targetReducedDensity_trace
    {d : ℕ} (ξ : BipartiteUnitVector d) :
    Matrix.trace (targetReducedDensity ξ) = 1 := by
  have vectorized := matrixVectorization_inner
    (targetCoefficientMatrix ξ)
    (targetCoefficientMatrix ξ)
  rw [targetCoefficientMatrix_vec,
    inner_self_eq_one_of_norm_eq_one ξ.property] at vectorized
  exact vectorized.symm

end

section

open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp

private def targetCanonicalSchmidtCoefficient
    {d : ℕ} (ξ : BipartiteUnitVector d)
    (i : Fin d) : ℝ :=
  Real.sqrt
    ((targetReducedDensity_posSemidef ξ).isHermitian.eigenvalues i)

private theorem targetCanonicalSchmidtCoefficient_nonneg
    {d : ℕ} (ξ : BipartiteUnitVector d) (i : Fin d) :
    0 ≤ targetCanonicalSchmidtCoefficient ξ i :=
  Real.sqrt_nonneg _

private theorem exists_proofTargetCanonicalSpectralSchmidtDecomposition
    {d : ℕ} (ξ : BipartiteUnitVector d) :
    ∃ (V : Matrix.unitaryGroup (Fin d) ℂ),
      ξ.val = schmidtVector
        (targetCanonicalSchmidtCoefficient ξ)
        (conjugateUnitary
          (targetReducedDensity_posSemidef ξ).isHermitian.eigenvectorUnitary)
        V := by
  classical
  let C : Matrix (Fin d) (Fin d) ℂ := targetCoefficientMatrix ξ
  let T : EuclideanSpace ℂ (Fin d) →ₗ[ℂ]
      EuclideanSpace ℂ (Fin d) := Matrix.toEuclideanLin C
  let hF := targetReducedDensity_posSemidef ξ
  let v : OrthonormalBasis (Fin d) ℂ
      (EuclideanSpace ℂ (Fin d)) := hF.isHermitian.eigenvectorBasis
  let σ : Fin d → ℝ := targetCanonicalSchmidtCoefficient ξ
  have hσ (i : Fin d) : 0 ≤ σ i :=
    targetCanonicalSchmidtCoefficient_nonneg ξ i
  have hσsq (i : Fin d) :
      σ i ^ 2 = hF.isHermitian.eigenvalues i := by
    exact Real.sq_sqrt (hF.eigenvalues_nonneg i)
  have heigen (i : Fin d) :
      (T.adjoint ∘ₗ T) (v i) = ((σ i ^ 2 : ℝ) : ℂ) • v i := by
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    change
      toLp 2
        (C.conjTranspose.mulVec
          (C.mulVec (ofLp (v i)))) =
        ((σ i ^ 2 : ℝ) : ℂ) • v i
    rw [Matrix.mulVec_mulVec]
    have spectral := hF.isHermitian.mulVec_eigenvectorBasis i
    change
      (C.conjTranspose * C).mulVec
        (ofLp (v i)) =
        (hF.isHermitian.eigenvalues i) • (ofLp (v i)) at spectral
    rw [spectral, ← hσsq]
    rfl
  let s : Set (Fin d) := {i | σ i ≠ 0}
  let f : Fin d → EuclideanSpace ℂ (Fin d) :=
    fun i => ((σ i : ℂ)⁻¹) • T (v i)
  have hGram (i j : Fin d) :
      inner ℂ (T (v i)) (T (v j)) =
        ((σ j ^ 2 : ℝ) : ℂ) * inner ℂ (v i) (v j) := by
    calc
      inner ℂ (T (v i)) (T (v j)) =
          inner ℂ (v i) (T.adjoint (T (v j))) :=
        (T.adjoint_inner_right (v i) (T (v j))).symm
      _ = inner ℂ (v i) (((σ j ^ 2 : ℝ) : ℂ) • v j) := by
        rw [← heigen j]
        rfl
      _ = _ := by rw [inner_smul_right]
  have hf : Orthonormal ℂ (s.domRestrict f) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hi : (σ (i : Fin d) : ℂ) ≠ 0 := by
      exact_mod_cast i.property
    have hj : (σ (j : Fin d) : ℂ) ≠ 0 := by
      exact_mod_cast j.property
    change inner ℂ
      (((σ (i : Fin d) : ℂ)⁻¹) • T (v i))
      (((σ (j : Fin d) : ℂ)⁻¹) • T (v j)) = _
    rw [inner_smul_left, inner_smul_right, hGram,
      v.inner_eq_ite]
    by_cases same : i = j
    · subst j
      simp only [ite_true, mul_one]
      have real_star :
          starRingEnd ℂ ((σ (i : Fin d) : ℂ)⁻¹) =
            ((σ (i : Fin d) : ℂ)⁻¹) := by simp only [map_inv₀, conj_ofReal]
      rw [real_star]
      push_cast
      field_simp
    · have unequal : (i : Fin d) ≠ (j : Fin d) := by
        intro equal
        exact same (Subtype.ext equal)
      simp only [map_inv₀, conj_ofReal, ofReal_pow, unequal, ↓reduceIte, mul_zero, same]
  obtain ⟨u, hu⟩ :=
    Orthonormal.exists_orthonormalBasis_extension_of_card_eq
      (by
        rw [Fintype.card_fin]
        exact finrank_euclideanSpace_fin) hf
  have singular (i : Fin d) :
      T (v i) = (σ i : ℂ) • u i := by
    by_cases zero : σ i = 0
    · have kernel : (T.adjoint ∘ₗ T) (v i) = 0 := by
        rw [heigen i, zero]
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, ofReal_zero,
          zero_smul]
      have image : T (v i) = 0 := by
        apply LinearMap.mem_ker.mp
        rw [← T.ker_adjoint_comp_self]
        exact LinearMap.mem_ker.mpr kernel
      simp only [image, zero, ofReal_zero, zero_smul]
    · have chosen : u i = f i := hu i zero
      rw [chosen]
      change T (v i) =
        (σ i : ℂ) • (((σ i : ℂ)⁻¹) • T (v i))
      rw [smul_smul, mul_inv_cancel₀]
      · simp only [one_smul]
      · exact_mod_cast zero
  refine ⟨orthonormalBasisUnitary u, ?_⟩
  have eigen_unitary :
      orthonormalBasisUnitary v =
        hF.isHermitian.eigenvectorUnitary := rfl
  ext ⟨a, b⟩
  rw [schmidtVector_apply]
  have repr :
      T ((EuclideanSpace.basisFun (Fin d) ℂ) a) =
        ∑ i : Fin d,
          inner ℂ (v i) ((EuclideanSpace.basisFun (Fin d) ℂ) a) •
            T (v i) := by
    calc
      T ((EuclideanSpace.basisFun (Fin d) ℂ) a) =
          T (∑ i : Fin d,
            inner ℂ (v i) ((EuclideanSpace.basisFun (Fin d) ℂ) a) •
              v i) := by rw [v.sum_repr']
      _ = _ := by simp only [EuclideanSpace.basisFun_apply, map_sum, map_smul]
  have coordinate := congrArg
    (fun z : EuclideanSpace ℂ (Fin d) => z b) repr
  have replace :
      conjugateUnitary
          hF.isHermitian.eigenvectorUnitary =
        conjugateUnitary
          (orthonormalBasisUnitary v) := by
    rw [eigen_unitary]
  rw [replace]
  simpa [T, C, σ, targetCoefficientMatrix, Matrix.toLpLin_apply,
    EuclideanSpace.basisFun_apply, Matrix.mulVec_single_one,
    Matrix.col_apply, EuclideanSpace.inner_single_right,
    conjugateUnitary_apply,
    orthonormalBasisUnitary_apply, singular,
    mul_assoc, mul_left_comm, mul_comm] using coordinate

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

private def targetCanonicalSpectralEnergy
    {d : ℕ} (ξ ζ : BipartiteUnitVector d) : ℝ :=
  let F := targetReducedDensity ξ
  let G := targetReducedDensity ζ
  let hF := targetReducedDensity_posSemidef ξ
  let hG := targetReducedDensity_posSemidef ζ
  ∑ i : Fin d, ∑ j : Fin d,
    (Real.sqrt (hF.isHermitian.eigenvalues i) -
      Real.sqrt (hG.isHermitian.eigenvalues j)) ^ 2 *
      spectralAtomOverlap F G hF hG i j

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

/--
The DSV canonical failure prefix construction used in the quantum parallel-repetition argument.
-/
def dSVCanonicalFailurePrefix
    {d : ℕ} (r : Fin (d + 1)) :
    EuclideanSpace ℂ (Fin d × Fin d) :=
  toLp 2 fun q : Fin d × Fin d =>
    if q.1 = q.2 ∧ q.1.val < r.val then 1 else 0

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

/--
@isnad1 id=possemid.2h2v.s6.ee9144ef5d0b from=translated src=- shape=3a077c7a vocab=d0a6a4df
-/
theorem dSVProjectorComplement_posSemidef
    {d : Type*} [Fintype d] [DecidableEq d]
    (P : Matrix d d ℂ) (positive : P.PosSemidef)
    (projective : P * P = P) :
    (1 - P).PosSemidef := by
  have gram :
      (1 - P).conjTranspose * (1 - P) = (1 - P) := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      positive.isHermitian.eq]
    simp only [Matrix.mul_sub, mul_one, Matrix.sub_mul, one_mul, projective, sub_self, sub_zero]
  rw [← gram]
  exact Matrix.posSemidef_conjTranspose_mul_self (1 - P)

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

/-- The finite equivalence encoding DSV rank controlled target catalyst index. -/
def dSVRankControlledTargetCatalystIndexEquiv
    {ι : Type*} [Fintype ι]
    (d n : ℕ) :
    ((Fin d × ι) × Fin n) ≃
      Fin (d * (Fintype.card ι * n)) :=
  (Equiv.prodAssoc (Fin d) ι (Fin n)).trans
    ((Equiv.prodCongr (Equiv.refl (Fin d))
      ((Equiv.prodCongr (Fintype.equivFin ι)
        (Equiv.refl (Fin n))).trans finProdFinEquiv)).trans
      finProdFinEquiv)

end

section

open scoped BigOperators Kronecker ComplexOrder MatrixOrder

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

/-- The positive operator-valued measurement implementing DSV global projector binary. -/
def dSVGlobalProjectorBinaryPOVM
    {κ d : Type*} [Fintype κ] [Fintype d]
    [DecidableEq κ] [DecidableEq d]
    (P : κ → Matrix d d ℂ)
    (positive : ∀ k, (P k).PosSemidef)
    (complement : ∀ k, (1 - P k).PosSemidef) :
    POVM Bool (Σ _ : κ, d) where
  effect b := Matrix.blockDiagonal' fun k =>
    if b then P k else 1 - P k
  positive b := by
    apply posSemidef_blockDiagonal'
    intro k
    cases b
    · exact complement k
    · exact positive k
  complete := by
    classical
    rw [Fintype.sum_bool]
    ext ⟨k, i⟩ ⟨l, j⟩
    by_cases same : k = l
    · subst l
      simp only [↓reduceIte, Bool.false_eq_true, Matrix.add_apply, blockDiagonal'_apply,
        ↓reduceDIte, cast_eq, Matrix.sub_apply, Matrix.one_apply, add_sub_cancel, Sigma.mk.injEq,
        heq_eq_eq, true_and]
    · simp only [↓reduceIte, Bool.false_eq_true, Matrix.add_apply, blockDiagonal'_apply, same,
        ↓reduceDIte, add_zero, ne_eq, Sigma.mk.injEq, heq_eq_eq, false_and, not_false_eq_true,
        one_apply_ne]

end

section

open scoped BigOperators

/-- The DSV rational soft pass construction used in the quantum parallel-repetition argument. -/
def dSVRationalSoftPass (t x : ℝ) : ℝ :=
  x / (x + t)

/--
@isnad1 id=and.2h2v.s5.5ea0b256a3bf from=translated src=- shape=0a333a6b vocab=82892b9d
-/
theorem dSVRationalSoftPass_mem_unit
    {t x : ℝ} (positive : 0 < t) (nonnegative : 0 ≤ x) :
    0 ≤ dSVRationalSoftPass t x ∧
      dSVRationalSoftPass t x ≤ 1 := by
  unfold dSVRationalSoftPass
  have denominator : 0 < x + t := by linarith
  constructor
  · exact div_nonneg nonnegative denominator.le
  · apply (div_le_iff₀ denominator).mpr
    linarith

end

section

open scoped BigOperators ComplexOrder MatrixOrder

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

/--
The DSV soft bob left reduced density construction used in the quantum parallel-repetition
argument.
-/
def dSVSoftBobLeftReducedDensity
    {d : ℕ} (ζ : BipartiteUnitVector d) :
    Matrix (Fin d) (Fin d) ℂ :=
  targetCoefficientMatrix ζ *
    (targetCoefficientMatrix ζ).conjTranspose

/--
@isnad1 id=possemid.0h2v.s3.d81ad1bbf790 from=translated src=- shape=cc4c7d09 vocab=d51fff8e
-/
theorem dSVSoftBobLeftReducedDensity_posSemidef
    {d : ℕ} (ζ : BipartiteUnitVector d) :
    (dSVSoftBobLeftReducedDensity ζ).PosSemidef := by
  exact Matrix.posSemidef_self_mul_conjTranspose
    (targetCoefficientMatrix ζ)

/--
@isnad1 id=eq.0h2v.s4.1e76543d4911 from=translated src=- shape=07b30d77 vocab=8873951b
-/
theorem dSVSoftBobLeftReducedDensity_trace
    {d : ℕ} (ζ : BipartiteUnitVector d) :
    Matrix.trace (dSVSoftBobLeftReducedDensity ζ) = 1 := by
  unfold dSVSoftBobLeftReducedDensity
  calc
    Matrix.trace
        (targetCoefficientMatrix ζ *
          (targetCoefficientMatrix ζ).conjTranspose) =
        Matrix.trace
          ((targetCoefficientMatrix ζ).conjTranspose *
            targetCoefficientMatrix ζ) :=
      Matrix.trace_mul_comm _ _
    _ = 1 := targetReducedDensity_trace ζ

/-- The unitary operator implementing DSV original computational reindexed. -/
def dSVOriginalComputationalReindexedUnitary
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {D : ℕ} (e : ι ≃ Fin D)
    (U : Matrix.unitaryGroup ι ℂ) :
    Matrix.unitaryGroup (Fin D) ℂ := by
  classical
  let M : Matrix ι ι ℂ := U.val
  refine ⟨(Matrix.reindex e e) M, ?_⟩
  rw [Matrix.mem_unitaryGroup_iff']
  have compatible :
      star ((Matrix.reindex e e) M) =
        (Matrix.reindex e e) (star M) := by
    ext i j
    simp only [reindex_apply, star_apply, submatrix_apply, RCLike.star_def, star_eq_conjTranspose,
      conjTranspose_apply]
  rw [compatible]
  change (Matrix.reindexRingEquiv ℂ e) (star M) *
    (Matrix.reindexRingEquiv ℂ e) M = 1
  rw [← (Matrix.reindexRingEquiv ℂ e).map_mul,
    (Matrix.mem_unitaryGroup_iff').mp U.property]
  exact (Matrix.reindexRingEquiv ℂ e).map_one

end

section

open scoped BigOperators ComplexOrder

/--
The DSV heterogeneous real prefix construction used in the quantum parallel-repetition argument.
-/
def dSVHeterogeneousRealPrefix
    (continuation : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∏ i ∈ Finset.range k, continuation i

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

/--
The type used to represent DSV uniform density threshold local index in the exact sampling
construction.
-/
abbrev DSVUniformDensityThresholdLocalIndex
    (N d : ℕ) :=
  Σ _ : Fin N, Fin d

/-- The quantum state representing DSV uniform density threshold shared. -/
def dSVUniformDensityThresholdSharedState
    (N d : ℕ) :
    EuclideanSpace ℂ
      (DSVUniformDensityThresholdLocalIndex N d ×
        DSVUniformDensityThresholdLocalIndex N d) :=
  sharedThresholdResource (d := Fin d)
    (fun _ : Fin N => (1 : ℝ))

/--
@isnad1 id=eq.2h2v.s6.08d1888cceb9 from=translated src=- shape=8212d33d vocab=d30e17af
-/
theorem dSVUniformDensityThresholdSharedState_norm
    {N d : ℕ} (grid : 0 < N) (dimension : 0 < d) :
    ‖dSVUniformDensityThresholdSharedState N d‖ = 1 := by
  exact sharedThresholdResource_norm
    (fun _ : Fin N => (1 : ℝ))
    ⟨0, grid⟩ ⟨0, dimension⟩ (by norm_num)

/--
The DSV uniform density threshold shared density construction used in the quantum parallel-
repetition argument.
-/
def dSVUniformDensityThresholdSharedDensity
    {N d : ℕ} (grid : 0 < N) (dimension : 0 < d) :
    DensityMatrix
      (DSVUniformDensityThresholdLocalIndex N d ×
        DSVUniformDensityThresholdLocalIndex N d) :=
  pureDensityMatrix
    (dSVUniformDensityThresholdSharedState N d)
    (dSVUniformDensityThresholdSharedState_norm
      grid dimension)

/--
The type used to represent DSV uniform density independent history local index in the exact
sampling construction.
-/
abbrev DSVUniformDensityIndependentHistoryLocalIndex
    (L N d : ℕ) :=
  Fin L → DSVUniformDensityThresholdLocalIndex N d

/-- The isometry regrouping paired history coordinates into Alice's and Bob's histories. -/
def dSVUniformDensityIndependentHistoryPairReindex
    (L N d : ℕ) :
    EuclideanSpace ℂ
      (Fin L →
        (DSVUniformDensityThresholdLocalIndex N d ×
          DSVUniformDensityThresholdLocalIndex N d)) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ
        (DSVUniformDensityIndependentHistoryLocalIndex
            L N d ×
          DSVUniformDensityIndependentHistoryLocalIndex
            L N d) := by
  classical
  exact LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    bilateralWorkPairEquiv.symm

/-- The quantum state representing DSV uniform density independent shared. -/
def dSVUniformDensityIndependentSharedState
    (L N d : ℕ) :
    EuclideanSpace ℂ
      (DSVUniformDensityIndependentHistoryLocalIndex L N d ×
        DSVUniformDensityIndependentHistoryLocalIndex L N d) :=
  dSVUniformDensityIndependentHistoryPairReindex L N d
    (finiteTensorVector
      (fun _ : Fin L =>
        dSVUniformDensityThresholdSharedState N d))

end

section

open scoped BigOperators ComplexOrder MatrixOrder

private def dSVUniformDensitySpectralAtomDiscrepancy
    {d : ℕ} (ξ ζ : BipartiteUnitVector d) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin d,
    |targetCanonicalSchmidtCoefficient ξ i ^ 2 -
      targetCanonicalSchmidtCoefficient ζ j ^ 2| *
      spectralAtomOverlap
        (targetReducedDensity ξ)
        (targetReducedDensity ζ)
        (targetReducedDensity_posSemidef ξ)
        (targetReducedDensity_posSemidef ζ) i j

private def dSVUniformDensitySchmidtSumMass
    {d : ℕ} (ξ ζ : BipartiteUnitVector d) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin d,
    (targetCanonicalSchmidtCoefficient ξ i +
      targetCanonicalSchmidtCoefficient ζ j) ^ 2 *
      spectralAtomOverlap
        (targetReducedDensity ξ)
        (targetReducedDensity ζ)
        (targetReducedDensity_posSemidef ξ)
        (targetReducedDensity_posSemidef ζ) i j

end

section

open scoped BigOperators

namespace ClassicalSampling

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The marked element with smallest rank after applying the given permutation. -/
def markedFirst (rank : α ≃ Fin (Fintype.card α))
    (marked : Finset α) (nonempty : marked.Nonempty)
    (permutation : Equiv.Perm α) : α :=
  permutation.symm
    (rank.symm
      ((marked.image (fun a => rank (permutation a))).min'
        (nonempty.image (fun a => rank (permutation a)))))

private def firstFiber (rank : α ≃ Fin (Fintype.card α))
    (marked : Finset α) (nonempty : marked.Nonempty)
    (a : α) : Finset (Equiv.Perm α) :=
  Finset.univ.filter fun permutation =>
    markedFirst rank marked nonempty permutation = a

/-- The probability of uniform permutation. -/
def uniformPermutationProbability (event : Equiv.Perm α → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter fun permutation : Equiv.Perm α =>
      event permutation).card : ℝ) / Fintype.card (Equiv.Perm α)

private def markedTotalVariation (left right : Finset α) : ℝ :=
  (((left \ right) ∪ (right \ left)).card : ℝ) /
    (2 * (left.card : ℝ))

section RationalMarks

variable {β : Type*} [Fintype β] [DecidableEq β]

/-- The rational marked construction used in the quantum parallel-repetition argument. -/
def rationalMarked (denominator : ℕ) (numerator : β → ℕ) :
    Finset (β × Fin denominator) := by
  classical
  exact Finset.univ.filter fun point =>
    point.2.val < numerator point.1

end RationalMarks

end ClassicalSampling

namespace Pinsker

private def pinskerScalarGap (x : ℝ) : ℝ :=
  InformationTheory.klFun x - 3 * (x - 1) ^ 2 / (2 * (x + 2))

/-- The entropy quantity for finite relative. -/
def finiteRelativeEntropy {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) : ℝ :=
  ∑ i, q i * InformationTheory.klFun (p i / q i)

/-- The finite total variation construction used in the quantum parallel-repetition argument. -/
def finiteTotalVariation {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) : ℝ :=
  (∑ i, |p i - q i|) / 2

end Pinsker

namespace ClassicalInformation

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalSampling

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/--
The distribution floor numerator construction used in the quantum parallel-repetition argument.
-/
def distributionFloorNumerator (denominator : ℕ) (p : ι → ℝ) : ι → ℕ :=
  fun i => Nat.floor (p i * (denominator : ℝ))

/--
The distribution floor residual construction used in the quantum parallel-repetition argument.
-/
def distributionFloorResidual (denominator : ℕ) (p : ι → ℝ) : ℕ :=
  denominator - ∑ i, distributionFloorNumerator denominator p i

/--
The distribution rounded numerator construction used in the quantum parallel-repetition
argument.
-/
def distributionRoundedNumerator
    (base : ι) (denominator : ℕ) (p : ι → ℝ) : ι → ℕ :=
  fun i => distributionFloorNumerator denominator p i +
    if i = base then distributionFloorResidual denominator p else 0

private def distributionFloorProbability
    (denominator : ℕ) (p : ι → ℝ) : ι → ℝ :=
  fun i => (distributionFloorNumerator denominator p i : ℝ) / denominator

/-- The probability of distribution rounded. -/
def distributionRoundedProbability
    (base : ι) (denominator : ℕ) (p : ι → ℝ) : ι → ℝ :=
  fun i =>
    (distributionRoundedNumerator base denominator p i : ℝ) / denominator

section CoarseGraining

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The total probability mass of grouped. -/
def groupedMass (map : ι → κ) (p : ι → ℝ) (j : κ) : ℝ :=
  ∑ i ∈ (Finset.univ.filter fun i => map i = j), p i

omit [DecidableEq ι] [Fintype κ] in
/-- Express a grouped mass as an indicator-weighted sum over its source.
@isnad1 id=eq.0h5v.s5.774936e6d607 from=translated src=- shape=58970463 vocab=021b122e
-/
theorem groupedMass_eq_sum_ite (map : ι → κ) (p : ι → ℝ) (j : κ) :
    groupedMass map p j = ∑ i, if map i = j then p i else 0 := by
  classical
  rw [groupedMass, Finset.sum_filter]

end CoarseGraining

section JointChainRule

variable {κ : Type*} [Fintype κ]

/-- The marginal distribution of joint first. -/
def jointFirstMarginal (joint : ι × κ → ℝ) : ι → ℝ :=
  fun i => ∑ j : κ, joint (i, j)

/-- The joint conditional construction used in the quantum parallel-repetition argument. -/
def jointConditional (joint : ι × κ → ℝ) (i : ι) : κ → ℝ :=
  fun j => joint (i, j) / jointFirstMarginal joint i

end JointChainRule

section SharedPermutationSampling

/--
The rational permutation output construction used in the quantum parallel-repetition argument.
-/
def rationalPermutationOutput
    (denominator : ℕ) (numerator : ι → ℕ)
    (nonempty : (rationalMarked denominator numerator).Nonempty)
    (permutation : Equiv.Perm (ι × Fin denominator)) : ι :=
  (markedFirst (Fintype.equivFin (ι × Fin denominator))
    (rationalMarked denominator numerator) nonempty permutation).1

end SharedPermutationSampling

end ClassicalInformation

end

section

open WithLp
open scoped BigOperators ComplexOrder MatrixOrder

private def dSVUniformLeftDensityConjugateSwapVector
    {d : ℕ} (z : EuclideanSpace ℂ (Fin d × Fin d)) :
    EuclideanSpace ℂ (Fin d × Fin d) :=
  toLp 2 (fun ij : Fin d × Fin d => star (z (ij.2, ij.1)))

private theorem dSVUniformLeftDensityConjugateSwapVector_norm
    {d : ℕ} (z : EuclideanSpace ℂ (Fin d × Fin d)) :
    ‖dSVUniformLeftDensityConjugateSwapVector z‖ = ‖z‖ := by
  have squares :
      ‖dSVUniformLeftDensityConjugateSwapVector z‖ ^ 2 =
        ‖z‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      Fintype.sum_prod_type, Fintype.sum_prod_type]
    change
      (∑ i : Fin d, ∑ j : Fin d,
        ‖star (z (j, i))‖ ^ 2) =
        ∑ i : Fin d, ∑ j : Fin d, ‖z (i, j)‖ ^ 2
    simp_rw [norm_star]
    rw [Finset.sum_comm]
  nlinarith [norm_nonneg
    (dSVUniformLeftDensityConjugateSwapVector z),
    norm_nonneg z]

private def dSVUniformLeftDensityConjugateSwap
    {d : ℕ} (ξ : BipartiteUnitVector d) :
    BipartiteUnitVector d :=
  ⟨dSVUniformLeftDensityConjugateSwapVector ξ.val,
    (dSVUniformLeftDensityConjugateSwapVector_norm ξ.val).trans
      ξ.property⟩

private theorem dSVUniformLeftDensityConjugateSwap_coefficient
    {d : ℕ} (ξ : BipartiteUnitVector d) :
    targetCoefficientMatrix
        (dSVUniformLeftDensityConjugateSwap ξ) =
      (targetCoefficientMatrix ξ).conjTranspose := by
  ext b a
  rfl

private theorem dSVUniformLeftDensityConjugateSwap_density
    {d : ℕ} (ξ : BipartiteUnitVector d) :
    targetReducedDensity
        (dSVUniformLeftDensityConjugateSwap ξ) =
      dSVSoftBobLeftReducedDensity ξ := by
  unfold targetReducedDensity
    dSVSoftBobLeftReducedDensity
  rw [dSVUniformLeftDensityConjugateSwap_coefficient,
    Matrix.conjTranspose_conjTranspose]

/--
The DSV uniform left density schmidt coefficient construction used in the quantum parallel-
repetition argument.
-/
def dSVUniformLeftDensitySchmidtCoefficient
    {d : ℕ} (ξ : BipartiteUnitVector d)
    (i : Fin d) : ℝ :=
  Real.sqrt
    ((dSVSoftBobLeftReducedDensity_posSemidef ξ).isHermitian.eigenvalues i)

/--
The DSV uniform left density spectral atom discrepancy construction used in the quantum
parallel-repetition argument.
-/
def dSVUniformLeftDensitySpectralAtomDiscrepancy
    {d : ℕ} (ξ ζ : BipartiteUnitVector d) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin d,
    |dSVUniformLeftDensitySchmidtCoefficient ξ i ^ 2 -
      dSVUniformLeftDensitySchmidtCoefficient ζ j ^ 2| *
      spectralAtomOverlap
        (dSVSoftBobLeftReducedDensity ξ)
        (dSVSoftBobLeftReducedDensity ζ)
        (dSVSoftBobLeftReducedDensity_posSemidef ξ)
        (dSVSoftBobLeftReducedDensity_posSemidef ζ) i j

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

attribute [local instance] Classical.propDecidable

/--
The DSV uniform density threshold grid construction used in the quantum parallel-repetition
argument.
-/
def dSVUniformDensityThresholdGrid
    (N : ℕ) (k : Fin N) : ℝ :=
  finiteUniformThresholdGrid
    (1 / (N : ℝ)) (1 + 1 / (N : ℝ)) N k

/--
@isnad1 id=eq.1h2v.s5.76c0bd507f30 from=translated src=- shape=bd9a4f01 vocab=d7791624
-/
theorem dSVUniformDensityThresholdGrid_apply
    {N : ℕ} (positive : 0 < N) (k : Fin N) :
    dSVUniformDensityThresholdGrid N k =
      ((k.val : ℝ) + 1) / (N : ℝ) := by
  have nonzero : (N : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt positive)
  unfold dSVUniformDensityThresholdGrid
    finiteUniformThresholdGrid
  field_simp
  ring

/-- The probability weight for DSV uniform density threshold. -/
def dSVUniformDensityThresholdWeight
    (N : ℕ) (_k : Fin N) : ℝ :=
  1 / (N : ℝ)

/--
@isnad1 id=le.0h2v.s4.07c37ec9fd9b from=translated src=- shape=9363a417 vocab=d30b2f88
-/
theorem dSVUniformDensityThresholdWeight_nonneg
    (N : ℕ) (k : Fin N) :
    0 ≤ dSVUniformDensityThresholdWeight N k := by
  unfold dSVUniformDensityThresholdWeight
  positivity

/--
The DSV uniform density grid prefix construction used in the quantum parallel-repetition
argument.
-/
def dSVUniformDensityGridPrefix
    (N : ℕ) (density : ℝ) : ℝ :=
  ∑ k : Fin N,
    dSVUniformDensityThresholdWeight N k *
      if dSVUniformDensityThresholdGrid N k ≤ density
      then 1 else 0

/--
@isnad1 id=eq.0h2v.s5.2b13ab4f02b4 from=translated src=- shape=a653a937 vocab=edb76c4a
-/
theorem dSVUniformDensityGridPrefix_eq_count
    (N : ℕ) (density : ℝ) :
    dSVUniformDensityGridPrefix N density =
      ((Finset.univ.filter fun k : Fin N =>
        dSVUniformDensityThresholdGrid N k ≤ density).card : ℝ) /
        (N : ℝ) := by
  classical
  unfold dSVUniformDensityGridPrefix
    dSVUniformDensityThresholdWeight
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  simp only [div_eq_mul_inv, mul_comm, mul_one, sum_const, nsmul_eq_mul]

/--
The DSV uniform density threshold mismatch construction used in the quantum parallel-repetition
argument.
-/
def dSVUniformDensityThresholdMismatch
    (N : ℕ) (alice bob : ℝ) : ℝ :=
  ∑ k : Fin N,
    dSVUniformDensityThresholdWeight N k *
      if ((dSVUniformDensityThresholdGrid N k ≤ alice) ↔
        (dSVUniformDensityThresholdGrid N k ≤ bob))
      then 0 else 1

/--
@isnad1 id=eq.3h2v.s6.1c17c954c725 from=translated src=- shape=ac8e1c19 vocab=b3887112
-/
theorem dSVUniformDensityThresholdGrid_count_eq_floor
    {N : ℕ} (positive : 0 < N)
    (density : ℝ) (nonnegative : 0 ≤ density) (bounded : density ≤ 1) :
    (Finset.univ.filter fun k : Fin N =>
      dSVUniformDensityThresholdGrid N k ≤ density).card =
        Nat.floor (density * (N : ℝ)) := by
  classical
  have gridpositive : (0 : ℝ) < N := by exact_mod_cast positive
  have densitypositive : 0 ≤ density * (N : ℝ) :=
    mul_nonneg nonnegative gridpositive.le
  have floor_bound : Nat.floor (density * (N : ℝ)) ≤ N := by
    have product : density * (N : ℝ) ≤ (N : ℝ) := by
      nlinarith
    have floor := Nat.floor_mono product
    simpa only [ge_iff_le, Nat.floor_natCast] using floor
  have same :
      (Finset.univ.filter fun k : Fin N =>
        dSVUniformDensityThresholdGrid N k ≤ density) =
      (Finset.univ.filter fun k : Fin N =>
        k.val < Nat.floor (density * (N : ℝ))) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [dSVUniformDensityThresholdGrid_apply positive,
      div_le_iff₀ gridpositive]
    constructor
    · intro threshold
      have cast : ((k.val + 1 : ℕ) : ℝ) ≤ density * (N : ℝ) := by
        simpa only [Nat.cast_add, Nat.cast_one] using threshold
      have below := (Nat.le_floor_iff densitypositive).2 cast
      omega
    · intro below
      have integer : k.val + 1 ≤ Nat.floor (density * (N : ℝ)) := by
        omega
      have cast := (Nat.le_floor_iff densitypositive).1 integer
      simpa only [ge_iff_le, Nat.cast_add, Nat.cast_one] using cast
  rw [same, Fin.card_filter_val_lt, min_eq_right floor_bound]

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

end

section

open scoped BigOperators Kronecker ComplexOrder MatrixOrder

end

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

attribute [local instance] Classical.propDecidable

/-- The normalize or default construction used in the quantum parallel-repetition argument. -/
def normalizeOrDefault (fallback z : E) : E :=
  if z = 0 then fallback else NormedSpace.normalize z

/--
@isnad1 id=eq.1h3v.s5.3fff0c1c53dd from=translated src=- shape=ab06a75b vocab=0ac31309
-/
theorem normalizeOrDefault_norm
    (fallback z : E) (hfallback : ‖fallback‖ = 1) :
    ‖normalizeOrDefault fallback z‖ = 1 := by
  classical
  by_cases hz : z = 0
  · simp only [normalizeOrDefault, hz, ↓reduceIte, hfallback]
  · simp only [normalizeOrDefault, hz, ↓reduceIte, NormedSpace.norm_normalize hz]

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

/--
The DSV canonical failure unit rank family construction used in the quantum parallel-repetition
argument.
-/
def dSVCanonicalFailureUnitRankFamily
    (d : ℕ) (positive : 0 < d) (rank : Fin (d + 1)) :
    BipartiteUnitVector d :=
  ⟨normalizeOrDefault
      (embezzlementState d)
      (dSVCanonicalFailurePrefix rank),
    normalizeOrDefault_norm
      (embezzlementState d)
      (dSVCanonicalFailurePrefix rank)
      (embezzlementState_norm d positive)⟩

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

/--
The DSV uniform density threshold left bob basis construction used in the quantum parallel-
repetition argument.
-/
def dSVUniformDensityThresholdLeftBobBasis
    {d : ℕ} (ζ : BipartiteUnitVector d) :
    Matrix.unitaryGroup (Fin d) ℂ :=
  (dSVSoftBobLeftReducedDensity_posSemidef ζ).isHermitian.eigenvectorUnitary

end

section

open WithLp
open scoped BigOperators ComplexOrder MatrixOrder

/--
@isnad1 id=ex.0h2v.s8.65c885d25beb from=translated src=- shape=1d139398 vocab=7ca80e29
-/
theorem exists_proofDSVUniformDensityPolarLeftCanonicalSchmidt
    {d : ℕ} (ξ : BipartiteUnitVector d) :
    ∃ A : Matrix.unitaryGroup (Fin d) ℂ,
      ξ.val = schmidtVector
        (dSVUniformLeftDensitySchmidtCoefficient ξ)
        A (dSVUniformDensityThresholdLeftBobBasis ξ) := by
  let χ := dSVUniformLeftDensityConjugateSwap ξ
  have density : targetReducedDensity χ =
      dSVSoftBobLeftReducedDensity ξ :=
    dSVUniformLeftDensityConjugateSwap_density ξ
  obtain ⟨V, decomposition⟩ :=
    exists_proofTargetCanonicalSpectralSchmidtDecomposition χ
  have canonical_basis :
      (targetReducedDensity_posSemidef χ).isHermitian.eigenvectorUnitary =
        dSVUniformDensityThresholdLeftBobBasis ξ := by
    unfold dSVUniformDensityThresholdLeftBobBasis
    simp only [density]
  have canonical_coefficient :
      targetCanonicalSchmidtCoefficient χ =
        dSVUniformLeftDensitySchmidtCoefficient ξ := by
    funext i
    unfold targetCanonicalSchmidtCoefficient
      dSVUniformLeftDensitySchmidtCoefficient
    simp only [density]
  rw [canonical_basis, canonical_coefficient] at decomposition
  refine ⟨conjugateUnitary V, ?_⟩
  ext ⟨a, b⟩
  have coordinate := congrArg
    (fun v : EuclideanSpace ℂ (Fin d × Fin d) => v (b, a))
    decomposition
  change star (ξ.val (a, b)) = _ at coordinate
  rw [schmidtVector_apply] at coordinate
  have unconjugated := congrArg star coordinate
  rw [schmidtVector_apply]
  simpa only [conjugateUnitary_apply, RCLike.star_def, mul_comm, mul_left_comm,
    RingHomCompTriple.comp_apply, RingHom.id_apply, star_sum, star_mul',
    conj_ofReal] using unconjugated

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

/-- The matrix of the tensor product of a finite family of local unitaries. -/
def finiteTensorLocalUnitaryMatrix
    {ι β : Type*} [Fintype ι] [Fintype β] [DecidableEq β]
    (U : ι → Matrix.unitaryGroup β ℂ) :
    Matrix (ι → β) (ι → β) ℂ :=
  fun q r => ∏ i : ι, (U i : Matrix β β ℂ) (q i) (r i)

/--
@isnad1 id=eq.0h3v.s8.ba12fe4c2d87 from=translated src=- shape=1b316f46 vocab=bde8a4f0
-/
theorem finiteTensorLocalUnitaryMatrix_gram
    {ι β : Type*}
    [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (U : ι → Matrix.unitaryGroup β ℂ) :
    (finiteTensorLocalUnitaryMatrix U).conjTranspose *
        finiteTensorLocalUnitaryMatrix U = 1 := by
  classical
  ext p q
  change
    (∑ r : ι → β,
      star (∏ i : ι, (U i : Matrix β β ℂ) (r i) (p i)) *
        (∏ i : ι, (U i : Matrix β β ℂ) (r i) (q i))) =
      (1 : Matrix (ι → β) (ι → β) ℂ) p q
  have factor :
      (∑ r : ι → β,
        star (∏ i : ι, (U i : Matrix β β ℂ) (r i) (p i)) *
          (∏ i : ι, (U i : Matrix β β ℂ) (r i) (q i))) =
        ∏ i : ι, ∑ x : β,
          star ((U i : Matrix β β ℂ) x (p i)) *
            (U i : Matrix β β ℂ) x (q i) := by
    calc
      _ = ∑ r : ι → β, ∏ i : ι,
          (star ((U i : Matrix β β ℂ) (r i) (p i)) *
            (U i : Matrix β β ℂ) (r i) (q i)) := by
        apply Finset.sum_congr rfl
        intro r _
        rw [star_prod, ← Finset.prod_mul_distrib]
      _ = _ :=
        (Fintype.prod_sum fun i : ι => fun x : β =>
          star ((U i : Matrix β β ℂ) x (p i)) *
            (U i : Matrix β β ℂ) x (q i)).symm
  rw [factor]
  have single (i : ι) :
      (∑ x : β,
        star ((U i : Matrix β β ℂ) x (p i)) *
          (U i : Matrix β β ℂ) x (q i)) =
        (1 : Matrix β β ℂ) (p i) (q i) := by
    have gram := (Matrix.mem_unitaryGroup_iff').mp
      (U i).property
    have entry := congrArg
      (fun M : Matrix β β ℂ => M (p i) (q i)) gram
    simpa only [RCLike.star_def, star_eq_conjTranspose, Matrix.mul_apply,
      conjTranspose_apply] using entry
  simp_rw [single]
  by_cases equal : p = q
  · subst q
    simp only [one_apply_eq, prod_const_one]
  · have different : ∃ i : ι, p i ≠ q i := by
      by_contra h
      push Not at h
      exact equal (funext h)
    obtain ⟨i, hi⟩ := different
    have zero :
        (∏ j : ι, (1 : Matrix β β ℂ) (p j) (q j)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp only [ne_eq, hi, not_false_eq_true, one_apply_ne]
    rw [zero]
    simp only [ne_eq, equal, not_false_eq_true, one_apply_ne]

/-- The unitary on function indices obtained by tensoring the local unitaries. -/
def finiteTensorLocalUnitary
    {ι β : Type*}
    [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (U : ι → Matrix.unitaryGroup β ℂ) :
    Matrix.unitaryGroup (ι → β) ℂ := by
  refine ⟨finiteTensorLocalUnitaryMatrix U, ?_⟩
  rw [Matrix.mem_unitaryGroup_iff',
    Matrix.star_eq_conjTranspose]
  exact finiteTensorLocalUnitaryMatrix_gram U

/-- The unitary operator implementing controlled finite tensor local. -/
def controlledFiniteTensorLocalUnitary
    {Ω ι β : Type*}
    [Fintype Ω] [DecidableEq Ω]
    [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (U : Ω → ι → Matrix.unitaryGroup β ℂ) :
    Matrix.unitaryGroup (Σ _ : Ω, (ι → β)) ℂ :=
  coherentSharedRandomControlledUnitary
    (fun ω => finiteTensorLocalUnitary (U ω))

end

section

open scoped BigOperators Kronecker ComplexOrder MatrixOrder

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

/--
The type used to represent DSV uniform density threshold whole history local index in the exact
sampling construction.
-/
abbrev DSVUniformDensityThresholdWholeHistoryLocalIndex
    (N d L : ℕ) :=
  Σ _ : Fin (L + 1),
    Fin (L + 1) → DSVUniformDensityThresholdLocalIndex N d

/--
The type used to represent DSV uniform density threshold whole history catalyst index in the
exact sampling construction.
-/
abbrev DSVUniformDensityThresholdWholeHistoryCatalystIndex
    (N d L : ℕ) :=
  Fin N × (Fin (L + 1) ×
    (Fin L → DSVUniformDensityThresholdLocalIndex N d))

/-- The quantum state representing DSV uniform density threshold whole history shared. -/
def dSVUniformDensityThresholdWholeHistorySharedState
    (N d L : ℕ) :
    EuclideanSpace ℂ
      (DSVUniformDensityThresholdWholeHistoryLocalIndex N d L ×
        DSVUniformDensityThresholdWholeHistoryLocalIndex N d L) :=
  sharedThresholdResource
    (d := Fin (L + 1) →
      DSVUniformDensityThresholdLocalIndex N d)
    (fun flag : Fin (L + 1) =>
      if flag.val = 0 then (1 : ℝ) else 0)

/-- The finite equivalence encoding DSV uniform density threshold whole history target split. -/
def dSVUniformDensityThresholdWholeHistoryTargetSplitEquiv
    (N d L : ℕ) :
    DSVUniformDensityThresholdWholeHistoryLocalIndex N d L ≃
      (Fin d ×
        DSVUniformDensityThresholdWholeHistoryCatalystIndex
          N d L) where
  toFun q :=
    ((q.2 0).2,
      ((q.2 0).1, (q.1, fun j => q.2 j.succ)))
  invFun q :=
    ⟨q.2.2.1,
      Fin.cons (⟨q.2.1, q.1⟩ :
        DSVUniformDensityThresholdLocalIndex N d)
        q.2.2.2⟩
  left_inv := by
    rintro ⟨flag, history⟩
    change
      (⟨flag, Fin.cons (history 0) (fun j => history j.succ)⟩ :
        DSVUniformDensityThresholdWholeHistoryLocalIndex
          N d L) = ⟨flag, history⟩
    congr 1
    exact Fin.cons_self_tail history
  right_inv := by
    rintro ⟨target, threshold, flag, history⟩
    simp only [Fin.cons_zero, Fin.cons_succ]

/--
The DSV uniform density alice history spectral copy construction used in the quantum parallel-
repetition argument.
-/
def dSVUniformDensityAliceHistorySpectralCopy
    {N d : ℕ} (ξ : BipartiteUnitVector d) :
    Matrix.unitaryGroup
      (DSVUniformDensityThresholdLocalIndex N d) ℂ :=
  coherentSharedRandomControlledUnitary
    (fun _ : Fin N =>
      (dSVUniformDensityThresholdLeftBobBasis ξ)⁻¹)

/--
The DSV uniform density bob history copy basis construction used in the quantum parallel-
repetition argument.
-/
def dSVUniformDensityBobHistoryCopyBasis
    {N d : ℕ} (ζ : BipartiteUnitVector d) :
    Matrix.unitaryGroup
      (DSVUniformDensityThresholdLocalIndex N d) ℂ :=
  coherentSharedRandomControlledUnitary
    (fun _ : Fin N =>
      conjugateUnitary
        (dSVUniformDensityThresholdLeftBobBasis ζ))

end

section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-- The scalar resolvent function `z / (z + s)` as a complex square-integrable function. -/
def scalarPurificationLp (z : ℝ) (hz : 0 ≤ z) :
    Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ))) :=
  ((scalarResolventFilter_memLp_two hz).ofReal (K := ℂ)).toLp
    (fun s : ℝ => ((z / (z + s) : ℝ) : ℂ))

private theorem scalarPurificationLp_coeFn
    (z : ℝ) (hz : 0 ≤ z) :
    (scalarPurificationLp z hz : ℝ → ℂ) =ᵐ[volume.restrict (Ioi 0)]
      (fun s : ℝ => ((z / (z + s) : ℝ) : ℂ)) :=
  ((scalarResolventFilter_memLp_two hz).ofReal
    (K := ℂ)).coeFn_toLp

/-- Resolvent functions for the eigenvalues of the family and its mean matrix. -/
def commonPurificationGenerator
    {ι d : Type*} [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) :
    Sum (ι × d) d → Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))
  | .inl (i, k) =>
      scalarPurificationLp
        ((positive i).isHermitian.eigenvalues k)
        ((positive i).eigenvalues_nonneg k)
  | .inr k =>
      scalarPurificationLp
        (hM.isHermitian.eigenvalues k)
        (hM.eigenvalues_nonneg k)

/--
The common purification subspace construction used in the quantum parallel-repetition argument.
-/
def commonPurificationSubspace
    {ι d : Type*} [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) :
    Submodule ℂ (Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))) :=
  Submodule.span ℂ
    (Set.range (commonPurificationGenerator F M positive hM))

/--
@isnad1 id=finitedi.2h4v.s12.8f7ddd4c5fff from=translated src=- shape=d3046cd2 vocab=963364fb
-/
theorem commonPurificationSubspace_finiteDimensional
    {ι d : Type*} [Finite ι] [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) :
    FiniteDimensional ℂ (commonPurificationSubspace F M positive hM) := by
  unfold commonPurificationSubspace
  exact FiniteDimensional.span_of_finite ℂ
    (Set.finite_range (commonPurificationGenerator F M positive hM))

private theorem ensemble_scalarPurificationLp_mem_common
    {ι d : Type*} [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) (i : ι) (k : d) :
    scalarPurificationLp
        ((positive i).isHermitian.eigenvalues k)
        ((positive i).eigenvalues_nonneg k) ∈
      commonPurificationSubspace F M positive hM := by
  apply Submodule.subset_span
  exact ⟨Sum.inl (i, k), rfl⟩

private theorem mean_scalarPurificationLp_mem_common
    {ι d : Type*} [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) (k : d) :
    scalarPurificationLp
        (hM.isHermitian.eigenvalues k)
        (hM.eigenvalues_nonneg k) ∈
      commonPurificationSubspace F M positive hM := by
  apply Submodule.subset_span
  exact ⟨Sum.inr k, rfl⟩

end

section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder
  Matrix.Norms.Elementwise InnerProductSpace

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/--
The spectral purification filter entry lp construction used in the quantum parallel-repetition
argument.
-/
def spectralPurificationFilterEntryLp
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) (i j : d) :
    Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ))) :=
  (((spectralPurificationFilter_memLp_two F hF).eval i).eval j).toLp
    (fun s : ℝ => spectralPurificationFilter F hF s i j)

/--
@isnad1 id=eventual.1h4v.s8.03db6da02761 from=translated src=- shape=10bcd809 vocab=da49920e
-/
theorem spectralPurificationFilterEntryLp_coeFn
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) (i j : d) :
    (spectralPurificationFilterEntryLp F hF i j : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioi 0)]
        (fun s : ℝ => spectralPurificationFilter F hF s i j) :=
  (((spectralPurificationFilter_memLp_two F hF).eval i).eval j).coeFn_toLp

private theorem spectralPurificationFilterEntryLp_eq_eigen_sum
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) (i j : d) :
    spectralPurificationFilterEntryLp F hF i j =
      ∑ k : d,
        (((hF.isHermitian.eigenvectorUnitary : Matrix d d ℂ) i k) *
          (star (hF.isHermitian.eigenvectorUnitary : Matrix d d ℂ)) k j) •
        scalarPurificationLp
          (hF.isHermitian.eigenvalues k)
          (hF.eigenvalues_nonneg k) := by
  classical
  let U := hF.isHermitian.eigenvectorUnitary
  let eigenvalue := hF.isHermitian.eigenvalues
  let coefficient : d → ℂ := fun k =>
    (U : Matrix d d ℂ) i k *
      star (U : Matrix d d ℂ) k j
  let generator : d → Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ))) :=
    fun k => scalarPurificationLp
      (eigenvalue k) (hF.eigenvalues_nonneg k)
  apply Lp.ext
  have hentry := spectralPurificationFilterEntryLp_coeFn F hF i j
  have hsum := Lp.coeFn_fun_finsetSum
    Finset.univ (fun k : d => coefficient k • generator k)
  have hgenerator :
      ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
        ∀ k : d,
          (coefficient k • generator k :
            Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))) s =
            coefficient k *
              ((eigenvalue k / (eigenvalue k + s) : ℝ) : ℂ) := by
    apply ae_all_iff.mpr
    intro k
    have hsmul := Lp.coeFn_smul (coefficient k) (generator k)
    have hscalar := scalarPurificationLp_coeFn
      (eigenvalue k) (hF.eigenvalues_nonneg k)
    filter_upwards [hsmul, hscalar] with s hs ht
    rw [hs]
    change
      coefficient k *
        (scalarPurificationLp (eigenvalue k)
          (hF.eigenvalues_nonneg k) : ℝ → ℂ) s = _
    rw [ht]
  filter_upwards [hentry, hsum, hgenerator] with s he hs hg
  rw [he, hs]
  change
    ((U : Matrix d d ℂ) *
      Matrix.diagonal (fun k =>
        ((eigenvalue k / (eigenvalue k + s) : ℝ) : ℂ)) *
      star (U : Matrix d d ℂ)) i j =
      ∑ k : d, (coefficient k • generator k :
        Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))) s
  simp_rw [hg]
  simp only [Matrix.diagonal, ofReal_div, ofReal_add, Matrix.mul_apply, of_apply, mul_comm,
    ite_mul, zero_mul, sum_ite_eq', Finset.mem_univ, ↓reduceIte, star_apply, RCLike.star_def,
    mul_assoc, coefficient]

/--
@isnad1 id=mem.2h7v.s11.65005ae7d481 from=translated src=- shape=0b794c24 vocab=78e39401
-/
theorem ensemble_spectralPurificationFilterEntryLp_mem_common
    {ι d : Type*} [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef)
    (a : ι) (i j : d) :
    spectralPurificationFilterEntryLp (F a) (positive a) i j ∈
      commonPurificationSubspace F M positive hM := by
  rw [spectralPurificationFilterEntryLp_eq_eigen_sum]
  apply (commonPurificationSubspace F M positive hM).sum_mem
  intro k _
  apply (commonPurificationSubspace F M positive hM).smul_mem
  exact ensemble_scalarPurificationLp_mem_common
    F M positive hM a k

/--
@isnad1 id=mem.2h6v.s11.a084872cae6c from=translated src=- shape=4bd16187 vocab=78e39401
-/
theorem mean_spectralPurificationFilterEntryLp_mem_common
    {ι d : Type*} [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef)
    (i j : d) :
    spectralPurificationFilterEntryLp M hM i j ∈
      commonPurificationSubspace F M positive hM := by
  rw [spectralPurificationFilterEntryLp_eq_eigen_sum]
  apply (commonPurificationSubspace F M positive hM).sum_mem
  intro k _
  apply (commonPurificationSubspace F M positive hM).smul_mem
  exact mean_scalarPurificationLp_mem_common
    F M positive hM k

/--
The ensemble purification subspace entry construction used in the quantum parallel-repetition
argument.
-/
def ensemblePurificationSubspaceEntry
    {ι d : Type*} [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef)
    (a : ι) (i j : d) :
    commonPurificationSubspace F M positive hM :=
  ⟨spectralPurificationFilterEntryLp (F a) (positive a) i j,
    ensemble_spectralPurificationFilterEntryLp_mem_common
      F M positive hM a i j⟩

/-- An entry of the mean spectral purification, bundled in the common subspace. -/
def meanPurificationSubspaceEntry
    {ι d : Type*} [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef)
    (i j : d) :
    commonPurificationSubspace F M positive hM :=
  ⟨spectralPurificationFilterEntryLp M hM i j,
    mean_spectralPurificationFilterEntryLp_mem_common
      F M positive hM i j⟩

/--
The common purification orthonormal basis construction used in the quantum parallel-repetition
argument.
-/
noncomputable def commonPurificationOrthonormalBasis
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) :
    OrthonormalBasis
      (Fin (Module.finrank ℂ
        (commonPurificationSubspace F M positive hM)))
      ℂ (commonPurificationSubspace F M positive hM) := by
  letI : FiniteDimensional ℂ
      (commonPurificationSubspace F M positive hM) :=
    commonPurificationSubspace_finiteDimensional F M positive hM
  exact stdOrthonormalBasis ℂ
    (commonPurificationSubspace F M positive hM)

/-- The matrix representation of finite purification. -/
noncomputable def finitePurificationMatrix
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) (a : ι) :
    Matrix
      (d × Fin (Module.finrank ℂ
        (commonPurificationSubspace F M positive hM))) d ℂ :=
  fun ik j =>
    (commonPurificationOrthonormalBasis F M positive hM).repr
      (ensemblePurificationSubspaceEntry F M positive hM a ik.1 j)
      ik.2

/-- The matrix representation of mean finite purification. -/
noncomputable def meanFinitePurificationMatrix
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) :
    Matrix
      (d × Fin (Module.finrank ℂ
        (commonPurificationSubspace F M positive hM))) d ℂ :=
  fun ik j =>
    (commonPurificationOrthonormalBasis F M positive hM).repr
      (meanPurificationSubspaceEntry F M positive hM ik.1 j)
      ik.2

end

section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder
  Matrix.Norms.Elementwise InnerProductSpace

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/--
@isnad1 id=eq.2h7v.s17.390b532da88c from=translated src=- shape=6447dfb3 vocab=bf0f27ab
-/
theorem finitePurificationMatrix_gram_apply
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) (a : ι) (i j : d) :
    ((finitePurificationMatrix F M positive hM a).conjTranspose *
      finitePurificationMatrix F M positive hM a) i j =
      ∑ r : d,
        inner ℂ
          (ensemblePurificationSubspaceEntry F M positive hM a r i)
          (ensemblePurificationSubspaceEntry F M positive hM a r j) := by
  classical
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    finitePurificationMatrix, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r _
  let b := commonPurificationOrthonormalBasis F M positive hM
  let u := ensemblePurificationSubspaceEntry
    F M positive hM a r i
  let v := ensemblePurificationSubspaceEntry
    F M positive hM a r j
  have hisometry := b.repr.inner_map_map u v
  change (∑ k, star (b.repr u k) * b.repr v k) =
    inner ℂ u v
  rw [← hisometry, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [RCLike.star_def, mul_comm, dotProduct, Pi.star_apply]

/--
@isnad1 id=eq.2h8v.s17.f6a34722bcf8 from=translated src=- shape=1d34443b vocab=55f9e3f0
-/
theorem ensemblePurificationSubspaceEntry_inner_eq_integral
    {ι d : Type*} [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef)
    (a : ι) (r i j : d) :
    inner ℂ
        (ensemblePurificationSubspaceEntry F M positive hM a r i)
        (ensemblePurificationSubspaceEntry F M positive hM a r j) =
      ∫ s in Ioi (0 : ℝ),
        star (spectralPurificationFilter (F a) (positive a) s r i) *
          spectralPurificationFilter (F a) (positive a) s r j := by
  rw [Submodule.coe_inner, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  have hi := spectralPurificationFilterEntryLp_coeFn
    (F a) (positive a) r i
  have hj := spectralPurificationFilterEntryLp_coeFn
    (F a) (positive a) r j
  filter_upwards [hi, hj] with s hs ht
  change
    inner ℂ
      (spectralPurificationFilterEntryLp
        (F a) (positive a) r i s)
      (spectralPurificationFilterEntryLp
        (F a) (positive a) r j s) = _
  rw [hs, ht]
  simp only [RCLike.inner_apply, RCLike.star_def, mul_comm]

/--
@isnad1 id=eq.2h5v.s15.60ca841cdf2a from=translated src=- shape=e05d4869 vocab=43d705eb
-/
theorem finitePurificationMatrix_gram_eq_integral
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) (a : ι) :
    (finitePurificationMatrix F M positive hM a).conjTranspose *
        finitePurificationMatrix F M positive hM a =
      ∫ s in Ioi (0 : ℝ),
        star (spectralPurificationFilter (F a) (positive a) s) *
          spectralPurificationFilter (F a) (positive a) s := by
  classical
  have hfilter := spectralPurificationFilter_memLp_two
    (F a) (positive a)
  have hmatrix := spectralPurificationFilter_gram_integrable
    (F a) (positive a)
  have hrows :
      ∀ i : d,
        Integrable
          (fun s : ℝ =>
            (star (spectralPurificationFilter (F a) (positive a) s) *
              spectralPurificationFilter (F a) (positive a) s) i)
          (volume.restrict (Ioi 0)) :=
    fun i => hmatrix.eval i
  ext i j
  rw [finitePurificationMatrix_gram_apply]
  rw [show
    (∫ s in Ioi (0 : ℝ),
      star (spectralPurificationFilter (F a) (positive a) s) *
        spectralPurificationFilter (F a) (positive a) s) i j =
      (∫ s in Ioi (0 : ℝ),
        (star (spectralPurificationFilter (F a) (positive a) s) *
          spectralPurificationFilter (F a) (positive a) s) i) j from
        congrArg (fun row : d → ℂ => row j)
          (MeasureTheory.eval_integral hrows i)]
  rw [show
    (∫ s in Ioi (0 : ℝ),
      (star (spectralPurificationFilter (F a) (positive a) s) *
        spectralPurificationFilter (F a) (positive a) s) i) j =
      ∫ s in Ioi (0 : ℝ),
        (star (spectralPurificationFilter (F a) (positive a) s) *
          spectralPurificationFilter (F a) (positive a) s) i j from
        MeasureTheory.eval_integral (fun k => (hrows i).eval k) j]
  simp_rw [ensemblePurificationSubspaceEntry_inner_eq_integral]
  have hproduct (r : d) :
      Integrable
        (fun s : ℝ =>
          star (spectralPurificationFilter (F a) (positive a) s r i) *
            spectralPurificationFilter (F a) (positive a) s r j)
        (volume.restrict (Ioi 0)) :=
    (((hfilter.eval r).eval i).star).integrable_mul
      ((hfilter.eval r).eval j)
  rw [← integral_finsetSum Finset.univ (fun r _ => hproduct r)]
  apply integral_congr_ae
  filter_upwards with s
  simp only [RCLike.star_def, Matrix.mul_apply, star_apply]

/--
@isnad1 id=eq.2h5v.s15.176bbc269f7b from=translated src=- shape=ba6697a5 vocab=ca0bdf7e
-/
theorem finitePurificationMatrix_gram
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (F : ι → Matrix d d ℂ) (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) (a : ι) :
    (finitePurificationMatrix F M positive hM a).conjTranspose *
      finitePurificationMatrix F M positive hM a = F a := by
  rw [finitePurificationMatrix_gram_eq_integral]
  exact integral_spectralPurificationFilter_gram (F a) (positive a)

end

section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder
  Matrix.Norms.Elementwise InnerProductSpace

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end

section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder
  Matrix.Norms.Elementwise InnerProductSpace

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end

section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

private def matrixPurificationVector
    {d : Type*}
    (K : Matrix d d ℂ) : EuclideanSpace ℂ (d × d) :=
  toLp 2 (Matrix.vec K)

private theorem matrixPurificationVector_norm_sq
    {d : Type*} [Fintype d]
    (K : Matrix d d ℂ) :
    ‖matrixPurificationVector K‖ ^ 2 =
      (Matrix.trace (Matrix.conjTranspose K * K)).re := by
  exact matrixVectorization_norm_sq K

/-- Regroup purification indices into a pair of joint player indices. -/
def strategyPurificationShuffle
    (dA dB : Type) :
    ((dA × (dA × dB)) × dB) ≃ ((dA × dB) × (dA × dB)) where
  toFun q := (q.1.2, (q.1.1, q.2))
  invFun q := ((q.2.1, q.1), q.2.2)
  left_inv := by
    rintro ⟨⟨a, k⟩, b⟩
    rfl
  right_inv := by
    rintro ⟨k, ⟨a, b⟩⟩
    rfl

/-- The state vector representing strategy purification. -/
def strategyPurificationVector
    {X Y A B : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {G : Game X Y A B} (S : Strategy G) :
    EuclideanSpace ℂ ((S.Alice × (S.Alice × S.Bob)) × S.Bob) :=
  toLp 2
    (fun q =>
      Matrix.vec (spectralSupportSqrt S.state.matrix S.state.positive)
        (strategyPurificationShuffle S.Alice S.Bob q))

private theorem strategyPurificationVector_norm_sq
    {X Y A B : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {G : Game X Y A B} (S : Strategy G) :
    ‖strategyPurificationVector S‖ ^ 2 =
      ‖matrixPurificationVector
          (spectralSupportSqrt S.state.matrix S.state.positive)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simpa only [strategyPurificationVector, vec, matrixPurificationVector] using
    Equiv.sum_comp (strategyPurificationShuffle S.Alice S.Bob)
      (fun q : (S.Alice × S.Bob) × (S.Alice × S.Bob) =>
        ‖Matrix.vec
          (spectralSupportSqrt S.state.matrix S.state.positive) q‖ ^ 2)

/--
@isnad1 id=eq.0h6v.s8.95d01d1151d7 from=translated src=- shape=bb32324f vocab=09840133
-/
theorem strategyPurificationVector_norm
    {X Y A B : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {G : Game X Y A B} (S : Strategy G) :
    ‖strategyPurificationVector S‖ = 1 := by
  let K := spectralSupportSqrt S.state.matrix S.state.positive
  have h_hermitian : (Matrix.conjTranspose K) = K :=
    (spectralSupportFunctional_isHermitian
      S.state.matrix S.state.positive Real.sqrt).eq
  have h_sq : ‖strategyPurificationVector S‖ ^ 2 = 1 := by
    calc
      ‖strategyPurificationVector S‖ ^ 2 =
          ‖matrixPurificationVector K‖ ^ 2 :=
            strategyPurificationVector_norm_sq S
      _ = (Matrix.trace (Matrix.conjTranspose K * K)).re :=
            matrixPurificationVector_norm_sq K
      _ = (Matrix.trace S.state.matrix).re := by
            rw [h_hermitian]
            change
              (Matrix.trace
                (spectralSupportSqrt S.state.matrix S.state.positive *
                  spectralSupportSqrt S.state.matrix S.state.positive)).re =
                (Matrix.trace S.state.matrix).re
            rw [spectralSupportSqrt_sq]
      _ = 1 := by rw [S.state.trace_one]; norm_num
  nlinarith [norm_nonneg (strategyPurificationVector S)]

/-- The positive operator-valued measurement implementing purification alice. -/
def purificationAlicePOVM
    {ι d k : Type*} [Fintype ι]
    [Fintype d] [Fintype k] [DecidableEq d] [DecidableEq k]
    (P : POVM ι d) : POVM ι (d × k) where
  effect a := P.effect a ⊗ₖ (1 : Matrix k k ℂ)
  positive a := (P.positive a).kronecker Matrix.PosSemidef.one
  complete := by
    classical
    calc
      (∑ a : ι, P.effect a ⊗ₖ (1 : Matrix k k ℂ)) =
          (∑ a : ι, P.effect a) ⊗ₖ (1 : Matrix k k ℂ) := by
            ext ⟨i, u⟩ ⟨j, v⟩
            simp only [Matrix.sum_apply, kroneckerMap_apply, sum_mul]
      _ = 1 := by
        rw [P.complete]
        exact Matrix.one_kronecker_one

/-- The strategy implementing purified. -/
def purifiedStrategy
    {X Y A B : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {G : Game X Y A B} (S : Strategy G) : Strategy G :=
  pureVectorStrategy G (strategyPurificationVector S)
    (strategyPurificationVector_norm S)
    (fun x => purificationAlicePOVM (S.aliceMeasurement x))
    S.bobMeasurement

/-- The matrix representation of finite local purification joint. -/
def finiteLocalPurificationJointMatrix
    {X Y A B eA eB : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {G : Game X Y A B} (S : Strategy G)
    (KA : Matrix eA S.Alice ℂ) (KB : Matrix eB S.Bob ℂ) :
    Matrix ((eA × (S.Alice × S.Bob)) × eB)
      ((S.Alice × (S.Alice × S.Bob)) × S.Bob) ℂ :=
  (KA ⊗ₖ
    (1 : Matrix (S.Alice × S.Bob) (S.Alice × S.Bob) ℂ)) ⊗ₖ KB

/-- The state vector representing finite local purification. -/
def finiteLocalPurificationVector
    {X Y A B eA eB : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {G : Game X Y A B} (S : Strategy G)
    (KA : Matrix eA S.Alice ℂ) (KB : Matrix eB S.Bob ℂ) :
    EuclideanSpace ℂ ((eA × (S.Alice × S.Bob)) × eB) :=
  toLp 2
    ((finiteLocalPurificationJointMatrix S KA KB).mulVec
      (ofLp (strategyPurificationVector S)))

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder InnerProductSpace

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

/--
The DSV uniform density physical async sigma continuation construction used in the quantum
parallel-repetition argument.
-/
def dSVUniformDensityPhysicalAsyncSigmaContinuation
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (U V : ι → Matrix.unitaryGroup κ ℂ)
    (z : EuclideanSpace ℂ
      ((Σ _ : ι, κ) × (Σ _ : ι, κ))) :
    EuclideanSpace ℂ ((Σ _ : ι, κ) × (Σ _ : ι, κ)) := by
  classical
  let A := coherentSharedRandomControlledUnitary U
  let B := coherentSharedRandomControlledUnitary V
  exact toLp 2 ((A.val ⊗ₖ B.val).mulVec (ofLp z))

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

attribute [local instance] Classical.propDecidable

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

attribute [local instance] Classical.propDecidable

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

/--
The DSV uniform density corrected matched sigma weighted residual construction used in the
quantum parallel-repetition argument.
-/
def dSVUniformDensityCorrectedMatchedSigmaWeightedResidual
    {H : Type*} {n : ℕ}
    (history : EuclideanSpace ℂ (H × H))
    (work : H → H → EuclideanSpace ℂ (Fin n × Fin n)) :
    EuclideanSpace ℂ
      ((Σ _ : H, Fin n) × (Σ _ : H, Fin n)) :=
  toLp 2 fun q : (Σ _ : H, Fin n) × (Σ _ : H, Fin n) =>
    history (q.1.1, q.2.1) * work q.1.1 q.2.1 (q.1.2, q.2.2)

end

section

open WithLp
open scoped BigOperators ComplexOrder MatrixOrder

attribute [local instance] Classical.propDecidable

/--
The DSV density rational projective threshold bin construction used in the quantum parallel-
repetition argument.
-/
def dSVDensityRationalProjectiveThresholdBin
    (w : ℝ) (N : ℕ) (k : Fin N) (a : ℝ) : Bool :=
  decide (dSVUniformDensityThresholdGrid N k ≤
    dSVRationalSoftPass w a)

/--
The positive operator-valued measurement implementing DSV density rational projective threshold.
-/
def dSVDensityRationalProjectiveThresholdPOVM
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ℝ) (N : ℕ) (k : Fin N)
    (F : Matrix ι ι ℂ) (positive : F.PosSemidef) : POVM Bool ι :=
  spectralPartitionPOVM F positive
    (fun i : ι => dSVDensityRationalProjectiveThresholdBin
      w N k (positive.isHermitian.eigenvalues i))

/--
@isnad1 id=eq.1h6v.s6.5cdaf3029cb6 from=translated src=- shape=a50e2a59 vocab=700d44cd
-/
theorem dSVDensityRationalProjectiveThresholdPOVM_projective
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ℝ) (N : ℕ) (k : Fin N)
    (F : Matrix ι ι ℂ) (positive : F.PosSemidef) (outcome : Bool) :
    (dSVDensityRationalProjectiveThresholdPOVM
      w N k F positive).effect outcome *
      (dSVDensityRationalProjectiveThresholdPOVM
        w N k F positive).effect outcome =
      (dSVDensityRationalProjectiveThresholdPOVM
        w N k F positive).effect outcome := by
  exact spectralPartitionPOVM_projective F positive
    (fun i : ι => dSVDensityRationalProjectiveThresholdBin
      w N k (positive.isHermitian.eigenvalues i)) outcome

/--
The positive operator-valued measurement implementing DSV density rational left projective
threshold.
-/
def dSVDensityRationalLeftProjectiveThresholdPOVM
    {d : ℕ} (w : ℝ) (N : ℕ) (k : Fin N)
    (ξ : BipartiteUnitVector d) : POVM Bool (Fin d) :=
  dSVDensityRationalProjectiveThresholdPOVM w N k
    (dSVSoftBobLeftReducedDensity ξ)
    (dSVSoftBobLeftReducedDensity_posSemidef ξ)

/--
The DSV density rational left projective threshold atom mismatch construction used in the
quantum parallel-repetition argument.
-/
def dSVDensityRationalLeftProjectiveThresholdAtomMismatch
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) : ℝ :=
  let F := dSVSoftBobLeftReducedDensity ξ
  let G := dSVSoftBobLeftReducedDensity ζ
  let hF := dSVSoftBobLeftReducedDensity_posSemidef ξ
  let hG := dSVSoftBobLeftReducedDensity_posSemidef ζ
  ∑ i : Fin d, ∑ j : Fin d,
    spectralAtomOverlap F G hF hG i j *
      dSVUniformDensityThresholdMismatch N
        (dSVRationalSoftPass w
          (hF.isHermitian.eigenvalues i))
        (dSVRationalSoftPass w
          (hG.isHermitian.eigenvalues j))

/--
@isnad1 id=lt.3h2v.s6.2dc3d9f47cf3 from=translated src=- shape=0761750d vocab=40e25d6c
-/
theorem dSVUniformDensityGridPrefix_density_sub_lt
    {N : ℕ} (positive : 0 < N)
    {a : ℝ} (nonnegative : 0 ≤ a) (bounded : a ≤ 1) :
    a - dSVUniformDensityGridPrefix N a < 1 / (N : ℝ) := by
  have cast : (0 : ℝ) < N := by exact_mod_cast positive
  rw [dSVUniformDensityGridPrefix_eq_count,
    dSVUniformDensityThresholdGrid_count_eq_floor
      positive a nonnegative bounded]
  apply (lt_div_iff₀ cast).mpr
  have floor := Nat.lt_floor_add_one (a * (N : ℝ))
  calc
    (a - (Nat.floor (a * (N : ℝ)) : ℝ) / (N : ℝ)) *
        (N : ℝ) =
      a * (N : ℝ) - (Nat.floor (a * (N : ℝ)) : ℝ) := by
        field_simp
    _ < 1 := by linarith

/--
@isnad1 id=le.3h2v.s6.0dca38fff298 from=translated src=- shape=5d4a1b9b vocab=40e25d6c
-/
theorem dSVUniformDensityGridPrefix_density_sub_le
    {N : ℕ} (positive : 0 < N)
    {a : ℝ} (nonnegative : 0 ≤ a) (bounded : a ≤ 1) :
    a - 1 / (N : ℝ) ≤ dSVUniformDensityGridPrefix N a := by
  linarith [dSVUniformDensityGridPrefix_density_sub_lt
    positive nonnegative bounded]

/-- The total probability mass of DSV density rational left projective diagonal. -/
def dSVDensityRationalLeftProjectiveDiagonalMass
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ : BipartiteUnitVector d) : ℝ :=
  let hF := dSVSoftBobLeftReducedDensity_posSemidef ξ
  ∑ i : Fin d,
    dSVUniformDensityGridPrefix N
      (dSVRationalSoftPass w
        (hF.isHermitian.eigenvalues i))

/--
@isnad1 id=le.0h3v.s4.ec124c7e7dbb from=translated src=- shape=67104c07 vocab=4327e6f1
-/
theorem dSVSoftBobLeftReducedDensity_eigenvalue_le_one
    {d : ℕ} (ξ : BipartiteUnitVector d) (i : Fin d) :
    (dSVSoftBobLeftReducedDensity_posSemidef ξ).isHermitian.eigenvalues i
      ≤ 1 := by
  let F := dSVSoftBobLeftReducedDensity ξ
  let hF : F.PosSemidef :=
    dSVSoftBobLeftReducedDensity_posSemidef ξ
  change hF.isHermitian.eigenvalues i ≤ 1
  calc
    hF.isHermitian.eigenvalues i ≤
        ∑ j : Fin d, hF.isHermitian.eigenvalues j :=
      Finset.single_le_sum
        (fun j _ => hF.eigenvalues_nonneg j) (Finset.mem_univ i)
    _ = 1 := positiveDensity_eigenvalues_sum F hF
      (dSVSoftBobLeftReducedDensity_trace ξ)

/--
@isnad1 id=le.3h2v.s6.272c4124fe84 from=translated src=- shape=58233553 vocab=1b24fc0b
-/
theorem dSVRationalSoftPass_ge_density_div_width_add_one
    {w a : ℝ} (width : 0 < w)
    (nonnegative : 0 ≤ a) (bounded : a ≤ 1) :
    a / (w + 1) ≤ dSVRationalSoftPass w a := by
  unfold dSVRationalSoftPass
  have denominator : 0 < a + w := by linarith
  have wider : 0 < w + 1 := by linarith
  apply (div_le_div_iff₀ wider denominator).mpr
  nlinarith

/--
@isnad1 id=le.2h4v.s6.8b80944edef3 from=translated src=- shape=c728b84f vocab=62ef45a2
-/
theorem dSVDensityRationalLeftProjectiveDiagonalMass_lower
    {d N : ℕ} {w : ℝ} (width : 0 < w) (grid : 0 < N)
    (ξ : BipartiteUnitVector d) :
    1 / (w + 1) - (d : ℝ) / N ≤
      dSVDensityRationalLeftProjectiveDiagonalMass w N ξ := by
  let F := dSVSoftBobLeftReducedDensity ξ
  let hF : F.PosSemidef :=
    dSVSoftBobLeftReducedDensity_posSemidef ξ
  have density_sum :
      (∑ i : Fin d, hF.isHermitian.eigenvalues i) = 1 :=
    positiveDensity_eigenvalues_sum F hF
      (dSVSoftBobLeftReducedDensity_trace ξ)
  have rational_sum :
      1 / (w + 1) ≤
        ∑ i : Fin d,
          dSVRationalSoftPass w
            (hF.isHermitian.eigenvalues i) := by
    calc
      1 / (w + 1) =
          ∑ i : Fin d, hF.isHermitian.eigenvalues i / (w + 1) := by
        rw [← Finset.sum_div, density_sum]
      _ ≤ ∑ i : Fin d,
          dSVRationalSoftPass w
            (hF.isHermitian.eigenvalues i) := by
        apply Finset.sum_le_sum
        intro i _
        exact dSVRationalSoftPass_ge_density_div_width_add_one
          width (hF.eigenvalues_nonneg i)
          (dSVSoftBobLeftReducedDensity_eigenvalue_le_one ξ i)
  calc
    1 / (w + 1) - (d : ℝ) / N ≤
        (∑ i : Fin d,
          dSVRationalSoftPass w
            (hF.isHermitian.eigenvalues i)) - (d : ℝ) / N :=
      sub_le_sub_right rational_sum _
    _ = ∑ i : Fin d,
        (dSVRationalSoftPass w
          (hF.isHermitian.eigenvalues i) - 1 / (N : ℝ)) := by
      simp only [one_div, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
        sub_right_inj]
      ring
    _ ≤ dSVDensityRationalLeftProjectiveDiagonalMass w N ξ := by
      unfold dSVDensityRationalLeftProjectiveDiagonalMass
      change
        (∑ i : Fin d,
          (dSVRationalSoftPass w
            (hF.isHermitian.eigenvalues i) - 1 / (N : ℝ))) ≤
          ∑ i : Fin d,
            dSVUniformDensityGridPrefix N
              (dSVRationalSoftPass w
                (hF.isHermitian.eigenvalues i))
      apply Finset.sum_le_sum
      intro i _
      exact dSVUniformDensityGridPrefix_density_sub_le grid
        (dSVRationalSoftPass_mem_unit width
          (hF.eigenvalues_nonneg i)).1
        (dSVRationalSoftPass_mem_unit width
          (hF.eigenvalues_nonneg i)).2

end

end QuantumParallelRepetition

end
