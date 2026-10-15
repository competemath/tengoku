/-
Copyright (c) 2026 Yuanhe Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuanhe Zhang, Jason D. Lee, Fanghui Liu
-/
import Tengoku

/-!
# Matrix Infrastructure

This file collects the SVD, spectral-decomposition, and orthogonal-projection infrastructure used
in the random-matrix parts of HDP, Section 4.1. Courant-Fischer min-max facts are in
`SLT.MatrixInfra.CourantFischer`.

## Main definitions

* `Matrix.singularValues`: singular values of a matrix, defined via its Euclidean linear map.
* `Matrix.rightSingularVectorBasis`: right singular vectors from the Gram-operator eigenbasis.
* `Matrix.leftSingularVector`: left singular vectors attached to nonzero singular values.

## Main results

* `Matrix.singularValues_nonneg` and `Matrix.singularValues_antitone`: the singular values are
  nonnegative and weakly decreasing.
* `Matrix.support_singularValues`: the nonzero singular values are exactly indexed by the rank of
  the associated linear map.
* `Matrix.hasEigenvalue_adjoint_comp_self_sq_singularValues`: the squares of the singular values
  are eigenvalues of `A†A`, matching HDP Remark 4.1.4.
* `Matrix.hasEigenvalue_conjTranspose_mul_self_sq_singularValues`: the same fact for the literal
  matrix `Aᴴ * A`.
* `Matrix.rightSingularVectorBasis` and
  `Matrix.adjoint_comp_self_apply_rightSingularVectorBasis`: the right-singular-vector eigenbasis
  equation for `A†A`, one of the structural ingredients of HDP Theorem 4.1.1.
* `Matrix.leftSingularVector` and
  `Matrix.apply_rightSingularVectorBasis_eq_smul_leftSingularVector`: the corresponding
  `A v_i = s_i u_i` relation for nonzero singular values.
* `Matrix.toEuclideanLin_apply_eq_sum_singularValue_leftSingularVector`: the resulting
  finite-sum SVD reconstruction formula for the action of `A` on an arbitrary vector.
* `Matrix.toEuclideanLin_apply_eq_sum_singularValue_rankOne`: the same reconstruction in
  rank-one operator notation, matching the usual `A = Σ sᵢ uᵢ vᵢ*` form after application.
* `Matrix.eq_sum_singularValue_vecMulVec`: the literal matrix SVD reconstruction
  `A = Σ sᵢ uᵢ vᵢᴴ`.
* `Matrix.eq_leftSingularMatrix_mul_diagonal_mul_conjTranspose_rightSingularMatrix`: rectangular
  matrix SVD form `A = UΣVᴴ`.
* `Matrix.conjTranspose_mul_self_eq_sum_sq_singularValue_vecMulVec`: the corresponding
  right-Gram decomposition `AᴴA = Σ sᵢ² vᵢvᵢᴴ`.
* `Matrix.mul_conjTranspose_eq_sum_sq_singularValue_vecMulVec`: the corresponding left-Gram
  decomposition `AAᴴ = Σ sᵢ² uᵢuᵢᴴ`.
* `Matrix.norm_apply_rightSingularVectorBasis`: right singular vectors attain their singular
  values in norm.
* `Matrix.orthonormal_leftSingularVector_of_singularValues_ne_zero`: the left singular vectors
  attached to nonzero singular values are orthonormal.
* `Matrix.self_adjoint_apply_leftSingularVector`: the corresponding `A A† u_i = s_i² u_i`
  eigen-equation for left singular vectors.
* `Matrix.IsHermitian.eigenvectorBasisToEuclideanLin` and
  `Matrix.IsHermitian.spectral_decomposition_toEuclideanLin`: Hermitian spectral decomposition
  through the matrix's Euclidean linear map.
* `Matrix.IsHermitian.eq_sum_eigenvalue_vecMulVec`: literal rank-one Hermitian spectral
  decomposition `A = Σ λᵢ uᵢuᵢᴴ`.
* `Submodule.starProjection_isSymmetricProjection`: orthogonal projection as a symmetric
  idempotent operator.
* `Submodule.starProjection_eq_sum_rankOne`: orthogonal projection decomposes as the sum of
  rank-one projections onto an orthonormal basis.
-/

open Module

noncomputable section

namespace Matrix

variable {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m] [Fintype n] [DecidableEq n]

/-! ## Singular values of matrices -/

/-- Singular values of an `m × n` matrix, defined as the singular values of its associated
linear map between Euclidean spaces. -/
noncomputable def singularValues (A : Matrix m n 𝕜) : ℕ →₀ ℝ :=
  A.toEuclideanLin.singularValues

/--
@isnad1 id=eq.0h4v.s12.b1dc1ce1b47a from=translated src=- shape=7cafc374 vocab=f7e20e9c
-/
@[simp]
theorem singularValues_toEuclideanLin (A : Matrix m n 𝕜) :
    A.singularValues = A.toEuclideanLin.singularValues :=
  rfl

/-- Singular values are nonnegative.
@isnad1 id=le.0h5v.s5.0ef9f1612963 from=translated src=- shape=22dc4dc5 vocab=3bae3c1d
-/
theorem singularValues_nonneg (A : Matrix m n 𝕜) (i : ℕ) : 0 ≤ A.singularValues i :=
  A.toEuclideanLin.singularValues_nonneg i

/-- Singular values are arranged in weakly decreasing order.
@isnad1 id=antitone.0h4v.s5.e8859fdc88cd from=translated src=- shape=393a7ec3 vocab=67b2bc3a
-/
theorem singularValues_antitone (A : Matrix m n 𝕜) : Antitone A.singularValues :=
  A.toEuclideanLin.singularValues_antitone

/-- Singular values are square roots of the eigenvalues of `A†A`.
@isnad1 id=eq.0h5v.s14.0598d0dc0314 from=translated src=- shape=2a4c28d7 vocab=be6db6bf
-/
theorem singularValues_fin (A : Matrix m n 𝕜) (i : Fin (Fintype.card n)) :
    A.singularValues i =
      √(A.toEuclideanLin.isSymmetric_adjoint_comp_self.eigenvalues finrank_euclideanSpace i) :=
  A.toEuclideanLin.singularValues_fin finrank_euclideanSpace i

/-- The singular values after the domain dimension are zero.
@isnad1 id=eq.1h5v.s6.4b2c9baac9a0 from=translated src=- shape=32731e62 vocab=3a05456b
-/
theorem singularValues_of_card_le (A : Matrix m n 𝕜) {i : ℕ} (hi : Fintype.card n ≤ i) :
    A.singularValues i = 0 := by
  have hfin : finrank 𝕜 (EuclideanSpace 𝕜 n) ≤ i := by
    simpa [finrank_euclideanSpace] using hi
  exact A.toEuclideanLin.singularValues_of_finrank_le hfin

/-- On the first `dim(domain)` indices, singular values square to the eigenvalues of `A†A`.
@isnad1 id=eq.0h5v.s14.b343e969eaa9 from=translated src=- shape=c3ce668d vocab=aefd6e9f
-/
theorem sq_singularValues_fin (A : Matrix m n 𝕜) (i : Fin (Fintype.card n)) :
    A.singularValues i ^ 2 =
      A.toEuclideanLin.isSymmetric_adjoint_comp_self.eigenvalues finrank_euclideanSpace i :=
  A.toEuclideanLin.sq_singularValues_fin finrank_euclideanSpace i

/--
The HDP Remark 4.1.4 statement in linear-map form: the square of each singular value is an
eigenvalue of the self-adjoint positive operator `A†A`.
@isnad1 id=haseigen.1h5v.s14.86c5f74e5557 from=translated src=- shape=eaf9dd71 vocab=93b6fa5d
-/
theorem hasEigenvalue_adjoint_comp_self_sq_singularValues
    (A : Matrix m n 𝕜) {i : ℕ} (hi : i < Fintype.card n) :
    Module.End.HasEigenvalue (LinearMap.adjoint A.toEuclideanLin ∘ₗ A.toEuclideanLin)
      (A.singularValues i ^ 2) := by
  have hfin : i < finrank 𝕜 (EuclideanSpace 𝕜 n) := by
    simpa [finrank_euclideanSpace] using hi
  exact A.toEuclideanLin.hasEigenvalue_adjoint_comp_self_sq_singularValues hfin

/-- The Euclidean linear map associated to `Aᴴ * A` is `A† ∘ A`.
@isnad1 id=eq.0h4v.s14.60cd8a9f6e8a from=translated src=- shape=dc7dc17f vocab=bce614bb
-/
theorem conjTranspose_mul_self_toEuclideanLin [DecidableEq m] (A : Matrix m n 𝕜) :
    (Aᴴ * A).toEuclideanLin = LinearMap.adjoint A.toEuclideanLin ∘ₗ A.toEuclideanLin := by
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint A]
  simpa [Matrix.toEuclideanLin_eq_toLin_orthonormal] using Matrix.toLin_mul
    (v₁ := (EuclideanSpace.basisFun n 𝕜).toBasis)
    (v₂ := (EuclideanSpace.basisFun m 𝕜).toBasis)
    (v₃ := (EuclideanSpace.basisFun n 𝕜).toBasis) Aᴴ A

/-- The square of each singular value is an eigenvalue of the literal matrix `Aᴴ * A`.
@isnad1 id=haseigen.1h5v.s12.f7418be10b62 from=translated src=- shape=ec3415ee vocab=5114ce72
-/
theorem hasEigenvalue_conjTranspose_mul_self_sq_singularValues [DecidableEq m]
    (A : Matrix m n 𝕜) {i : ℕ} (hi : i < Fintype.card n) :
    Module.End.HasEigenvalue (Aᴴ * A).toEuclideanLin (A.singularValues i ^ 2) := by
  rw [conjTranspose_mul_self_toEuclideanLin]
  exact A.hasEigenvalue_adjoint_comp_self_sq_singularValues hi

/-- The support of the singular-value sequence has cardinality equal to the rank.
@isnad1 id=eq.0h4v.s13.0a8d1675d84a from=translated src=- shape=8befe63d vocab=e6f5d04d
-/
theorem support_singularValues (A : Matrix m n 𝕜) :
    A.singularValues.support = Finset.range (finrank 𝕜 A.toEuclideanLin.range) :=
  A.toEuclideanLin.support_singularValues

/-- A singular value is positive exactly before the rank of the associated linear map.
@isnad1 id=iff.0h5v.s13.e03bb02b3078 from=translated src=- shape=18c3f6f3 vocab=30e26149
-/
theorem singularValues_pos_iff_lt_finrank_range (A : Matrix m n 𝕜) {i : ℕ} :
    0 < A.singularValues i ↔ i < finrank 𝕜 A.toEuclideanLin.range :=
  A.toEuclideanLin.singularValues_pos_iff_lt_finrank_range

/-- A singular value vanishes exactly at or after the rank of the associated linear map.
@isnad1 id=iff.0h5v.s13.f8770daee7d5 from=translated src=- shape=4fd32c95 vocab=19732506
-/
theorem singularValues_eq_zero_iff_le_finrank_range (A : Matrix m n 𝕜) {i : ℕ} :
    A.singularValues i = 0 ↔ finrank 𝕜 A.toEuclideanLin.range ≤ i :=
  A.toEuclideanLin.singularValues_eq_zero_iff_le_finrank_range

/-- A matrix has injective associated map iff all domain-indexed singular values are positive.
@isnad1 id=iff.0h4v.s12.a5817d81e6f2 from=translated src=- shape=ca17055c vocab=51235ccc
-/
theorem injective_toEuclideanLin_iff_singularValues_pos (A : Matrix m n 𝕜) :
    Function.Injective A.toEuclideanLin ↔ ∀ i < Fintype.card n, 0 < A.singularValues i := by
  simpa [finrank_euclideanSpace]
    using A.toEuclideanLin.injective_iff_forall_lt_finrank_singularValues_pos

/--
The right singular vectors of a matrix, chosen as an orthonormal eigenbasis of `A†A`. This is the
`v_i` basis in HDP Theorem 4.1.1.
-/
noncomputable def rightSingularVectorBasis (A : Matrix m n 𝕜) :
    OrthonormalBasis (Fin (Fintype.card n)) 𝕜 (EuclideanSpace 𝕜 n) :=
  A.toEuclideanLin.isSymmetric_adjoint_comp_self.eigenvectorBasis finrank_euclideanSpace

/--
The right singular vectors diagonalize `A†A`, with eigenvalues equal to squared singular values:
`A†A v_i = s_i^2 v_i`.
@isnad1 id=eq.0h5v.s14.e1decb864420 from=translated src=- shape=1ef98fd6 vocab=b5034693
-/
theorem adjoint_comp_self_apply_rightSingularVectorBasis
    (A : Matrix m n 𝕜) (i : Fin (Fintype.card n)) :
    (LinearMap.adjoint A.toEuclideanLin ∘ₗ A.toEuclideanLin)
        (A.rightSingularVectorBasis i) =
      ((A.singularValues i ^ 2 : ℝ) : 𝕜) • A.rightSingularVectorBasis i := by
  rw [rightSingularVectorBasis]
  have h :=
    A.toEuclideanLin.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis
      finrank_euclideanSpace i
  rw [← A.sq_singularValues_fin i] at h
  exact h

/--
The left singular vector associated to a nonzero singular value, defined as `s_i⁻¹ A v_i`. For
zero singular values this definition is still total, but the main equation below is stated under
`s_i ≠ 0`.
-/
noncomputable def leftSingularVector (A : Matrix m n 𝕜) (i : Fin (Fintype.card n)) :
    EuclideanSpace 𝕜 m :=
  (((A.singularValues i : ℝ) : 𝕜)⁻¹) • A.toEuclideanLin (A.rightSingularVectorBasis i)

/-- The SVD proof relation `A v_i = s_i u_i` for nonzero singular values.
@isnad1 id=eq.1h5v.s12.df8be753e0c1 from=translated src=- shape=734dc9ab vocab=4ba55c49
-/
theorem apply_rightSingularVectorBasis_eq_smul_leftSingularVector
    (A : Matrix m n 𝕜) {i : Fin (Fintype.card n)} (hi : A.singularValues i ≠ 0) :
    A.toEuclideanLin (A.rightSingularVectorBasis i) =
      ((A.singularValues i : ℝ) : 𝕜) • A.leftSingularVector i := by
  unfold leftSingularVector
  rw [smul_smul]
  have hci : ((A.singularValues i : ℝ) : 𝕜) ≠ 0 := by
    simpa only [ne_eq, RCLike.ofReal_eq_zero] using hi
  rw [mul_inv_cancel₀ hci]
  simp

/-- Right singular vectors with zero singular value lie in the kernel of `A`.
@isnad1 id=eq.1h5v.s12.6ce7bd28f9ce from=translated src=- shape=e2e520a6 vocab=b6715bea
-/
theorem apply_rightSingularVectorBasis_eq_zero_of_singularValues_eq_zero
    (A : Matrix m n 𝕜) {i : Fin (Fintype.card n)} (hi : A.singularValues i = 0) :
    A.toEuclideanLin (A.rightSingularVectorBasis i) = 0 := by
  have hker :
      A.rightSingularVectorBasis i ∈
        (LinearMap.adjoint A.toEuclideanLin ∘ₗ A.toEuclideanLin).ker := by
    have hzero : A.toEuclideanLin.singularValues (i : ℕ) = 0 := by
      simpa [Matrix.singularValues] using hi
    rw [LinearMap.mem_ker]
    rw [A.adjoint_comp_self_apply_rightSingularVectorBasis i]
    simp [hzero]
  have hkerA : A.rightSingularVectorBasis i ∈ A.toEuclideanLin.ker := by
    simpa [LinearMap.ker_adjoint_comp_self] using hker
  exact LinearMap.mem_ker.mp hkerA

/--
The SVD proof relation `A v_i = s_i u_i`, with the zero singular-value case included by the
kernel lemma above.
@isnad1 id=eq.0h5v.s12.f734e4b853d9 from=translated src=- shape=6f7f066b vocab=4ba55c49
-/
theorem apply_rightSingularVectorBasis_eq_smul_leftSingularVector'
    (A : Matrix m n 𝕜) (i : Fin (Fintype.card n)) :
    A.toEuclideanLin (A.rightSingularVectorBasis i) =
      ((A.singularValues i : ℝ) : 𝕜) • A.leftSingularVector i := by
  by_cases hi : A.singularValues i = 0
  · rw [A.apply_rightSingularVectorBasis_eq_zero_of_singularValues_eq_zero hi]
    rw [hi]
    simp
  · exact A.apply_rightSingularVectorBasis_eq_smul_leftSingularVector hi

/-- Applying `A` to a right singular vector has norm equal to the corresponding singular value.
@isnad1 id=eq.0h5v.s12.7eae5f3eac9a from=translated src=- shape=310576d2 vocab=dd1f0853
-/
theorem norm_apply_rightSingularVectorBasis
    (A : Matrix m n 𝕜) (i : Fin (Fintype.card n)) :
    ‖A.toEuclideanLin (A.rightSingularVectorBasis i)‖ = A.singularValues i := by
  refine (sq_eq_sq₀ (norm_nonneg _) (A.singularValues_nonneg i)).mp ?_
  calc
    ‖A.toEuclideanLin (A.rightSingularVectorBasis i)‖ ^ 2 =
        RCLike.re (inner 𝕜 (A.toEuclideanLin (A.rightSingularVectorBasis i))
          (A.toEuclideanLin (A.rightSingularVectorBasis i))) := by
      exact norm_sq_eq_re_inner (𝕜 := 𝕜) _
    _ = RCLike.re (inner 𝕜
          ((LinearMap.adjoint A.toEuclideanLin ∘ₗ A.toEuclideanLin)
            (A.rightSingularVectorBasis i))
          (A.rightSingularVectorBasis i)) := by
      rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left]
    _ = RCLike.re (inner 𝕜
          (((A.singularValues i ^ 2 : ℝ) : 𝕜) • A.rightSingularVectorBasis i)
          (A.rightSingularVectorBasis i)) := by
      rw [A.adjoint_comp_self_apply_rightSingularVectorBasis i]
    _ = A.singularValues i ^ 2 := by
      simp [inner_smul_left, OrthonormalBasis.norm_eq_one, RCLike.ofReal_pow]

/-- Nonzero left singular vectors are unit vectors.
@isnad1 id=eq.1h5v.s6.8c219fa9a0d1 from=translated src=- shape=6457c81d vocab=2005470d
-/
theorem norm_leftSingularVector_of_singularValues_ne_zero
    (A : Matrix m n 𝕜) {i : Fin (Fintype.card n)} (hi : A.singularValues i ≠ 0) :
    ‖A.leftSingularVector i‖ = 1 := by
  unfold leftSingularVector
  rw [norm_smul]
  rw [A.norm_apply_rightSingularVectorBasis i]
  have hpos : 0 < A.singularValues i := lt_of_le_of_ne' (A.singularValues_nonneg i) hi
  rw [norm_inv, RCLike.norm_ofReal, abs_of_pos hpos]
  exact inv_mul_cancel₀ hi

/--
The left singular vectors indexed by nonzero singular values are orthonormal. Together with the
right singular-vector orthonormal basis, this records the orthonormal-family part of HDP
Theorem 4.1.1.
@isnad1 id=orthonor.0h4v.s7.4625341f0960 from=translated src=- shape=c4a5d310 vocab=6d79e2c1
-/
theorem orthonormal_leftSingularVector_of_singularValues_ne_zero
    (A : Matrix m n 𝕜) :
    Orthonormal 𝕜
      (fun i : { i : Fin (Fintype.card n) // A.singularValues i ≠ 0 } =>
        A.leftSingularVector i) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  by_cases hij : i = j
  · subst j
    simp [A.norm_leftSingularVector_of_singularValues_ne_zero i.property,
      inner_self_eq_norm_sq_to_K]
    first
      | (all_goals grind; done; trace "PORTFOLIO-OK grind")
      | (all_goals simp_all; done; trace "PORTFOLIO-OK simp_all")
      | (all_goals aesop; done; trace "PORTFOLIO-OK aesop")
      | (all_goals omega; done; trace "PORTFOLIO-OK omega")
      | (all_goals norm_num; done; trace "PORTFOLIO-OK norm_num")
      | (all_goals positivity; done; trace "PORTFOLIO-OK positivity")
      | (all_goals linarith; done; trace "PORTFOLIO-OK linarith")
      | (all_goals decide; done; trace "PORTFOLIO-OK decide")
      | (all_goals tauto; done; trace "PORTFOLIO-OK tauto")
  · have hne : (i : Fin (Fintype.card n)) ≠ (j : Fin (Fintype.card n)) := by
      intro hval
      exact hij (Subtype.ext hval)
    have hmap :
        inner 𝕜 (A.toEuclideanLin (A.rightSingularVectorBasis i))
            (A.toEuclideanLin (A.rightSingularVectorBasis j)) = 0 := by
      calc
        inner 𝕜 (A.toEuclideanLin (A.rightSingularVectorBasis i))
            (A.toEuclideanLin (A.rightSingularVectorBasis j)) =
            inner 𝕜 ((LinearMap.adjoint A.toEuclideanLin ∘ₗ A.toEuclideanLin)
              (A.rightSingularVectorBasis i)) (A.rightSingularVectorBasis j) := by
          rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left]
        _ = inner 𝕜
            (((A.singularValues i ^ 2 : ℝ) : 𝕜) • A.rightSingularVectorBasis i)
            (A.rightSingularVectorBasis j) := by
          rw [A.adjoint_comp_self_apply_rightSingularVectorBasis i]
        _ = 0 := by
          rw [inner_smul_left]
          simp [A.rightSingularVectorBasis.inner_eq_zero hne]
    rw [ite_eq_right hij]
    unfold leftSingularVector
    rw [inner_smul_left, inner_smul_right, hmap]
    simp

/--
Operator-action form of the finite-dimensional SVD reconstruction: expanding `x` in the right
singular-vector orthonormal basis and applying `A` gives the sum of the singular-value weighted
left singular vectors.
@isnad1 id=eq.0h5v.s12.82faafa49fb9 from=translated src=- shape=980666cf vocab=f7ed7566
-/
theorem toEuclideanLin_apply_eq_sum_singularValue_leftSingularVector
    (A : Matrix m n 𝕜) (x : EuclideanSpace 𝕜 n) :
    A.toEuclideanLin x =
      ∑ i : Fin (Fintype.card n),
        A.rightSingularVectorBasis.repr x i •
          (((A.singularValues i : ℝ) : 𝕜) • A.leftSingularVector i) := by
  calc
    A.toEuclideanLin x =
        A.toEuclideanLin
          (∑ i : Fin (Fintype.card n),
            A.rightSingularVectorBasis.repr x i • A.rightSingularVectorBasis i) := by
      rw [A.rightSingularVectorBasis.sum_repr x]
    _ = ∑ i : Fin (Fintype.card n),
          A.rightSingularVectorBasis.repr x i •
            A.toEuclideanLin (A.rightSingularVectorBasis i) := by
      simp [map_sum, map_smul]
    _ = ∑ i : Fin (Fintype.card n),
          A.rightSingularVectorBasis.repr x i •
            (((A.singularValues i : ℝ) : 𝕜) • A.leftSingularVector i) := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [A.apply_rightSingularVectorBasis_eq_smul_leftSingularVector' i]

/--
Rank-one form of the SVD reconstruction after applying to a vector:
`A x = Σ i, s_i (u_i ⊗ v_i*) x`.
@isnad1 id=eq.0h5v.s15.34577a5765d2 from=translated src=- shape=5d82fcc9 vocab=add02235
-/
theorem toEuclideanLin_apply_eq_sum_singularValue_rankOne
    (A : Matrix m n 𝕜) (x : EuclideanSpace 𝕜 n) :
    A.toEuclideanLin x =
      ∑ i : Fin (Fintype.card n),
        (((A.singularValues i : ℝ) : 𝕜) •
          InnerProductSpace.rankOne 𝕜
            (A.leftSingularVector i) (A.rightSingularVectorBasis i)) x := by
  rw [A.toEuclideanLin_apply_eq_sum_singularValue_leftSingularVector x]
  simp only [OrthonormalBasis.repr_apply_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  change
    inner 𝕜 (A.rightSingularVectorBasis i) x •
        (((A.singularValues i : ℝ) : 𝕜) • A.leftSingularVector i) =
      ((A.singularValues i : ℝ) : 𝕜) •
        (inner 𝕜 (A.rightSingularVectorBasis i) x • A.leftSingularVector i)
  rw [smul_smul, smul_smul]
  exact congrArg (fun c : 𝕜 ↦ c • A.leftSingularVector i) (mul_comm _ _)

/-- The Euclidean linear map of `vecMulVec u (star v)` is the rank-one operator `u ⊗ v*`.
@isnad1 id=eq.0h5v.s14.7073e1cc1bfe from=translated src=- shape=3bba8b9b vocab=b1e56a19
-/
theorem vecMulVec_star_toEuclideanLin_eq_rankOne
    (u : EuclideanSpace 𝕜 m) (v : EuclideanSpace 𝕜 n) :
    (Matrix.vecMulVec u (star v)).toEuclideanLin =
      (InnerProductSpace.rankOne 𝕜 u v).toLinearMap := by
  have h :=
    congrArg Matrix.toEuclideanLin
      (InnerProductSpace.symm_toEuclideanLin_rankOne (𝕜 := 𝕜) u v)
  simpa using h.symm

/--
Literal matrix form of the SVD reconstruction:
`A = Σ i, s_i • vecMulVec u_i (star v_i)`, i.e. `A = Σ i s_i u_i v_iᴴ`.
-/
theorem eq_sum_singularValue_vecMulVec (A : Matrix m n 𝕜) :
    A =
      ∑ i : Fin (Fintype.card n),
        ((A.singularValues i : ℝ) : 𝕜) •
          Matrix.vecMulVec (A.leftSingularVector i) (star (A.rightSingularVectorBasis i)) := by
  apply Matrix.toEuclideanLin.injective
  apply LinearMap.ext
  intro x
  rw [A.toEuclideanLin_apply_eq_sum_singularValue_rankOne x]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [vecMulVec_star_toEuclideanLin_eq_rankOne]
  rfl

/-- Matrix with columns equal to the left singular vectors used in the SVD reconstruction. -/
noncomputable def leftSingularMatrix (A : Matrix m n 𝕜) :
    Matrix m (Fin (Fintype.card n)) 𝕜 :=
  (EuclideanSpace.basisFun m 𝕜).toBasis.toMatrix A.leftSingularVector

/-- Diagonal matrix whose diagonal entries are the singular values of `A`. -/
noncomputable def singularValueDiagonalMatrix (A : Matrix m n 𝕜) :
    Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) 𝕜 :=
  Matrix.diagonal fun i => ((A.singularValues i : ℝ) : 𝕜)

/-- Matrix with columns equal to the right singular vectors used in the SVD reconstruction. -/
noncomputable def rightSingularMatrix (A : Matrix m n 𝕜) :
    Matrix n (Fin (Fintype.card n)) 𝕜 :=
  (EuclideanSpace.basisFun n 𝕜).toBasis.toMatrix A.rightSingularVectorBasis

/-- The right-singular-vector matrix has orthonormal columns: `VᴴV = I`.
@isnad1 id=eq.0h4v.s7.237844a0880e from=translated src=- shape=0592e5b2 vocab=da756a80
-/
theorem rightSingularMatrix_conjTranspose_mul_self (A : Matrix m n 𝕜) :
    A.rightSingularMatrixᴴ * A.rightSingularMatrix = 1 := by
  simp [rightSingularMatrix]

/-- The right-singular-vector matrix is unitary after identifying its two finite index types.
@isnad1 id=eq.0h4v.s7.dbc515556be5 from=translated src=- shape=782d244a vocab=da756a80
-/
theorem rightSingularMatrix_mul_conjTranspose (A : Matrix m n 𝕜) :
    A.rightSingularMatrix * A.rightSingularMatrixᴴ = 1 := by
  simp [rightSingularMatrix]

/--
Rectangular matrix form of the SVD reconstruction:
`A = U * Σ * Vᴴ`, where the columns of `U` and `V` are the chosen left and right singular vectors
and `Σ` is diagonal with entries `s_i`.
-/
theorem eq_leftSingularMatrix_mul_diagonal_mul_conjTranspose_rightSingularMatrix
    (A : Matrix m n 𝕜) :
    A =
      A.leftSingularMatrix * A.singularValueDiagonalMatrix *
        A.rightSingularMatrixᴴ := by
  nth_rw 1 [A.eq_sum_singularValue_vecMulVec]
  ext a b
  simp [leftSingularMatrix, singularValueDiagonalMatrix, rightSingularMatrix,
    Matrix.mul_apply, Matrix.diagonal, sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
    Basis.toMatrix_apply, EuclideanSpace.basisFun_repr, RCLike.real_smul_eq_coe_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring

/--
Operator-action form of the right Gram decomposition:
`A† A x = Σ i, s_i^2 (v_i ⊗ v_i*) x`.
@isnad1 id=eq.0h5v.s15.81be46398e9b from=translated src=- shape=cc3921b3 vocab=0e71e231
-/
theorem adjoint_comp_self_apply_eq_sum_sq_singularValue_rankOne
    (A : Matrix m n 𝕜) (x : EuclideanSpace 𝕜 n) :
    (LinearMap.adjoint A.toEuclideanLin ∘ₗ A.toEuclideanLin) x =
      ∑ i : Fin (Fintype.card n),
        (((A.singularValues i ^ 2 : ℝ) : 𝕜) •
          InnerProductSpace.rankOne 𝕜
            (A.rightSingularVectorBasis i) (A.rightSingularVectorBasis i)) x := by
  calc
    (LinearMap.adjoint A.toEuclideanLin ∘ₗ A.toEuclideanLin) x =
        (LinearMap.adjoint A.toEuclideanLin ∘ₗ A.toEuclideanLin)
          (∑ i : Fin (Fintype.card n),
            A.rightSingularVectorBasis.repr x i • A.rightSingularVectorBasis i) := by
      rw [A.rightSingularVectorBasis.sum_repr x]
    _ = ∑ i : Fin (Fintype.card n),
          A.rightSingularVectorBasis.repr x i •
            (LinearMap.adjoint A.toEuclideanLin ∘ₗ A.toEuclideanLin)
              (A.rightSingularVectorBasis i) := by
      simp [map_sum, map_smul]
    _ = ∑ i : Fin (Fintype.card n),
          A.rightSingularVectorBasis.repr x i •
            (((A.singularValues i ^ 2 : ℝ) : 𝕜) • A.rightSingularVectorBasis i) := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [A.adjoint_comp_self_apply_rightSingularVectorBasis i]
    _ = ∑ i : Fin (Fintype.card n),
        (((A.singularValues i ^ 2 : ℝ) : 𝕜) •
          InnerProductSpace.rankOne 𝕜
            (A.rightSingularVectorBasis i) (A.rightSingularVectorBasis i)) x := by
      simp only [OrthonormalBasis.repr_apply_apply]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      change
        inner 𝕜 (A.rightSingularVectorBasis i) x •
            (((A.singularValues i ^ 2 : ℝ) : 𝕜) • A.rightSingularVectorBasis i) =
          ((A.singularValues i ^ 2 : ℝ) : 𝕜) •
            (inner 𝕜 (A.rightSingularVectorBasis i) x • A.rightSingularVectorBasis i)
      rw [smul_smul, smul_smul]
      exact congrArg (fun c : 𝕜 ↦ c • A.rightSingularVectorBasis i) (mul_comm _ _)

/--
Literal matrix form of HDP Remark 4.1.4 for the right Gram matrix:
`Aᴴ * A = Σ i, s_i^2 • vecMulVec v_i (star v_i)`.
@isnad1 id=eq.0h4v.s9.0b54b8461163 from=translated src=- shape=54b7c7b7 vocab=5c5a260a
-/
theorem conjTranspose_mul_self_eq_sum_sq_singularValue_vecMulVec [DecidableEq m]
    (A : Matrix m n 𝕜) :
    Aᴴ * A =
      ∑ i : Fin (Fintype.card n),
        ((A.singularValues i ^ 2 : ℝ) : 𝕜) •
          Matrix.vecMulVec (A.rightSingularVectorBasis i) (star (A.rightSingularVectorBasis i)) := by
  apply Matrix.toEuclideanLin.injective
  apply LinearMap.ext
  intro x
  rw [A.conjTranspose_mul_self_toEuclideanLin]
  rw [A.adjoint_comp_self_apply_eq_sum_sq_singularValue_rankOne x]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [vecMulVec_star_toEuclideanLin_eq_rankOne]
  rfl

/-- The Euclidean linear map associated to `A * Aᴴ` is `A ∘ A†`.
@isnad1 id=eq.0h4v.s14.c79e405a6da5 from=translated src=- shape=42782b82 vocab=bce614bb
-/
theorem mul_conjTranspose_toEuclideanLin [DecidableEq m] (A : Matrix m n 𝕜) :
    (A * Aᴴ).toEuclideanLin = A.toEuclideanLin ∘ₗ LinearMap.adjoint A.toEuclideanLin := by
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint A]
  simpa [Matrix.toEuclideanLin_eq_toLin_orthonormal] using Matrix.toLin_mul
    (v₁ := (EuclideanSpace.basisFun m 𝕜).toBasis)
    (v₂ := (EuclideanSpace.basisFun n 𝕜).toBasis)
    (v₃ := (EuclideanSpace.basisFun m 𝕜).toBasis) A Aᴴ

/--
Operator-action form of the left Gram decomposition:
`A A† y = Σ i, s_i^2 (u_i ⊗ u_i*) y`.
@isnad1 id=eq.0h5v.s15.47240fdede44 from=translated src=- shape=8186964b vocab=770c4e79
-/
theorem self_adjoint_apply_eq_sum_sq_singularValue_leftRankOne
    (A : Matrix m n 𝕜) (y : EuclideanSpace 𝕜 m) :
    (A.toEuclideanLin ∘ₗ LinearMap.adjoint A.toEuclideanLin) y =
      ∑ i : Fin (Fintype.card n),
        (((A.singularValues i ^ 2 : ℝ) : 𝕜) •
          InnerProductSpace.rankOne 𝕜
            (A.leftSingularVector i) (A.leftSingularVector i)) y := by
  calc
    (A.toEuclideanLin ∘ₗ LinearMap.adjoint A.toEuclideanLin) y =
        A.toEuclideanLin (LinearMap.adjoint A.toEuclideanLin y) := rfl
    _ = ∑ i : Fin (Fintype.card n),
          A.rightSingularVectorBasis.repr (LinearMap.adjoint A.toEuclideanLin y) i •
            (((A.singularValues i : ℝ) : 𝕜) • A.leftSingularVector i) := by
      rw [A.toEuclideanLin_apply_eq_sum_singularValue_leftSingularVector]
    _ = ∑ i : Fin (Fintype.card n),
          inner 𝕜 (A.rightSingularVectorBasis i) (LinearMap.adjoint A.toEuclideanLin y) •
            (((A.singularValues i : ℝ) : 𝕜) • A.leftSingularVector i) := by
      simp only [OrthonormalBasis.repr_apply_apply]
    _ = ∑ i : Fin (Fintype.card n),
          inner 𝕜 (A.toEuclideanLin (A.rightSingularVectorBasis i)) y •
            (((A.singularValues i : ℝ) : 𝕜) • A.leftSingularVector i) := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [LinearMap.adjoint_inner_right]
    _ = ∑ i : Fin (Fintype.card n),
          inner 𝕜 (((A.singularValues i : ℝ) : 𝕜) • A.leftSingularVector i) y •
            (((A.singularValues i : ℝ) : 𝕜) • A.leftSingularVector i) := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [A.apply_rightSingularVectorBasis_eq_smul_leftSingularVector' i]
    _ = ∑ i : Fin (Fintype.card n),
        (((A.singularValues i ^ 2 : ℝ) : 𝕜) •
          InnerProductSpace.rankOne 𝕜
            (A.leftSingularVector i) (A.leftSingularVector i)) y := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      change
        inner 𝕜 (((A.singularValues i : ℝ) : 𝕜) • A.leftSingularVector i) y •
            (((A.singularValues i : ℝ) : 𝕜) • A.leftSingularVector i) =
          ((A.singularValues i ^ 2 : ℝ) : 𝕜) •
            (inner 𝕜 (A.leftSingularVector i) y • A.leftSingularVector i)
      rw [inner_smul_left, smul_smul, smul_smul]
      simp only [RCLike.conj_ofReal, RCLike.ofReal_pow]
      rw [pow_two]
      ring_nf

/--
Literal matrix form of HDP Remark 4.1.4 for the left Gram matrix:
`A * Aᴴ = Σ i, s_i^2 • vecMulVec u_i (star u_i)`.
@isnad1 id=eq.0h4v.s8.17328122e787 from=translated src=- shape=8260031d vocab=89df9d85
-/
theorem mul_conjTranspose_eq_sum_sq_singularValue_vecMulVec [DecidableEq m]
    (A : Matrix m n 𝕜) :
    A * Aᴴ =
      ∑ i : Fin (Fintype.card n),
        ((A.singularValues i ^ 2 : ℝ) : 𝕜) •
          Matrix.vecMulVec (A.leftSingularVector i) (star (A.leftSingularVector i)) := by
  apply Matrix.toEuclideanLin.injective
  apply LinearMap.ext
  intro y
  rw [A.mul_conjTranspose_toEuclideanLin]
  rw [A.self_adjoint_apply_eq_sum_sq_singularValue_leftRankOne y]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [vecMulVec_star_toEuclideanLin_eq_rankOne]
  rfl

/-- The left singular vectors satisfy `A A† u_i = s_i² u_i`.
@isnad1 id=eq.0h5v.s14.cbf8694f44c5 from=translated src=- shape=6a4ba118 vocab=55631240
-/
theorem self_adjoint_apply_leftSingularVector
    (A : Matrix m n 𝕜) (i : Fin (Fintype.card n)) :
    (A.toEuclideanLin ∘ₗ LinearMap.adjoint A.toEuclideanLin) (A.leftSingularVector i) =
      ((A.singularValues i ^ 2 : ℝ) : 𝕜) • A.leftSingularVector i := by
  let s : 𝕜 := (A.singularValues i : ℝ)
  let v := A.rightSingularVectorBasis i
  calc
    (A.toEuclideanLin ∘ₗ LinearMap.adjoint A.toEuclideanLin) (A.leftSingularVector i)
        = s⁻¹ • A.toEuclideanLin
            ((LinearMap.adjoint A.toEuclideanLin ∘ₗ A.toEuclideanLin) v) := by
          simp [leftSingularVector, LinearMap.comp_apply, s, v]
    _ = s⁻¹ • A.toEuclideanLin (((A.singularValues i ^ 2 : ℝ) : 𝕜) • v) := by
          rw [A.adjoint_comp_self_apply_rightSingularVectorBasis i]
    _ = s⁻¹ • (((A.singularValues i ^ 2 : ℝ) : 𝕜) • A.toEuclideanLin v) := by
          rw [map_smul]
    _ = ((A.singularValues i ^ 2 : ℝ) : 𝕜) • A.leftSingularVector i := by
          simp [leftSingularVector, smul_smul, mul_comm, s, v]

end Matrix

/-! ## Spectral decomposition for Hermitian matrices -/

namespace Matrix
namespace IsHermitian

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]
variable {A : Matrix n n 𝕜} (hA : A.IsHermitian)

/--
Eigenvalues of a Hermitian matrix, read through its associated Euclidean linear map. These are
ordered as in Mathlib's self-adjoint spectral theorem.
-/
noncomputable def eigenvaluesToEuclideanLin : Fin (Fintype.card n) → ℝ :=
  (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues finrank_euclideanSpace

/--
An orthonormal eigenbasis of a Hermitian matrix, read through its associated Euclidean linear map.
This is the basis `u_i` in HDP's spectral decomposition.
-/
noncomputable def eigenvectorBasisToEuclideanLin :
    OrthonormalBasis (Fin (Fintype.card n)) 𝕜 (EuclideanSpace 𝕜 n) :=
  (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvectorBasis finrank_euclideanSpace

/-- A Hermitian matrix acts diagonally on its Euclidean eigenbasis.
@isnad1 id=eq.1h4v.s12.f5b6dc89cda6 from=translated src=- shape=92834d22 vocab=30970446
-/
theorem apply_eigenvectorBasisToEuclideanLin (i : Fin (Fintype.card n)) :
    A.toEuclideanLin (hA.eigenvectorBasisToEuclideanLin i) =
      (hA.eigenvaluesToEuclideanLin i : 𝕜) • hA.eigenvectorBasisToEuclideanLin i := by
  exact (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).apply_eigenvectorBasis
    finrank_euclideanSpace i

/--
Matrix-form spectral decomposition of a Hermitian matrix in its orthonormal eigenbasis:
the matrix of `A` in that basis is diagonal with the real eigenvalues on the diagonal.
@isnad1 id=eq.1h3v.s13.0d7ae793c2a6 from=translated src=- shape=19356bdf vocab=572de4f5
-/
theorem spectral_decomposition_toEuclideanLin :
    letI b := hA.eigenvectorBasisToEuclideanLin.toBasis
    A.toEuclideanLin.toMatrix b b =
      Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvaluesToEuclideanLin) := by
  exact (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).toMatrix_eigenvectorBasis
    finrank_euclideanSpace

/--
Literal rank-one spectral decomposition of a Hermitian matrix:
`A = Σ i, λ_i • vecMulVec u_i (star u_i)`.
-/
theorem eq_sum_eigenvalue_vecMulVec :
    A =
      ∑ i : Fin (Fintype.card n),
        (hA.eigenvaluesToEuclideanLin i : 𝕜) •
          Matrix.vecMulVec (hA.eigenvectorBasisToEuclideanLin i)
            (star (hA.eigenvectorBasisToEuclideanLin i)) := by
  apply Matrix.toEuclideanLin.injective
  apply LinearMap.ext
  intro x
  calc
    A.toEuclideanLin x =
        A.toEuclideanLin
          (∑ i : Fin (Fintype.card n),
            hA.eigenvectorBasisToEuclideanLin.repr x i •
              hA.eigenvectorBasisToEuclideanLin i) := by
      rw [hA.eigenvectorBasisToEuclideanLin.sum_repr x]
    _ = ∑ i : Fin (Fintype.card n),
          hA.eigenvectorBasisToEuclideanLin.repr x i •
            A.toEuclideanLin (hA.eigenvectorBasisToEuclideanLin i) := by
      simp [map_sum, map_smul]
    _ = ∑ i : Fin (Fintype.card n),
          hA.eigenvectorBasisToEuclideanLin.repr x i •
            ((hA.eigenvaluesToEuclideanLin i : 𝕜) •
              hA.eigenvectorBasisToEuclideanLin i) := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [hA.apply_eigenvectorBasisToEuclideanLin i]
    _ = ∑ i : Fin (Fintype.card n),
          (((hA.eigenvaluesToEuclideanLin i : ℝ) : 𝕜) •
            InnerProductSpace.rankOne 𝕜
              (hA.eigenvectorBasisToEuclideanLin i) (hA.eigenvectorBasisToEuclideanLin i)) x := by
      simp only [OrthonormalBasis.repr_apply_apply]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      change
        inner 𝕜 (hA.eigenvectorBasisToEuclideanLin i) x •
            ((hA.eigenvaluesToEuclideanLin i : 𝕜) • hA.eigenvectorBasisToEuclideanLin i) =
          (hA.eigenvaluesToEuclideanLin i : 𝕜) •
            (inner 𝕜 (hA.eigenvectorBasisToEuclideanLin i) x •
              hA.eigenvectorBasisToEuclideanLin i)
      rw [smul_smul, smul_smul]
      exact congrArg (fun c : 𝕜 ↦ c • hA.eigenvectorBasisToEuclideanLin i) (mul_comm _ _)
    _ =
        (∑ i : Fin (Fintype.card n),
          (hA.eigenvaluesToEuclideanLin i : 𝕜) •
            Matrix.vecMulVec (hA.eigenvectorBasisToEuclideanLin i)
              (star (hA.eigenvectorBasisToEuclideanLin i))).toEuclideanLin x := by
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Matrix.vecMulVec_star_toEuclideanLin_eq_rankOne]
      rfl

end IsHermitian
end Matrix

/-! ## Orthogonal projections -/

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
variable {ι : Type*} [Fintype ι]

/-- Orthogonal projection onto a subspace, as an endomorphism, is a symmetric projection.
@isnad1 id=issymmet.0h3v.s7.d00ed5866f94 from=translated src=- shape=bc1e45a3 vocab=d281540c
-/
theorem starProjection_isSymmetricProjection :
    (U.starProjection : E →ₗ[𝕜] E).IsSymmetricProjection :=
  U.isSymmetricProjection_starProjection

/-- The fixed points of the orthogonal projection onto `U` are exactly the vectors in `U`.
@isnad1 id=iff.0h4v.s8.721abf87bb62 from=translated src=- shape=3af3f5a1 vocab=76fce27e
-/
theorem starProjection_eq_self_iff_mem {x : E} : U.starProjection x = x ↔ x ∈ U :=
  U.starProjection_eq_self_iff

/-- Orthogonal projection onto `U`, valued in `U`, expanded in an orthonormal basis of `U`.
@isnad1 id=eq.0h6v.s11.fe481911b96e from=translated src=- shape=ae650ee8 vocab=b8bee117
-/
theorem orthogonalProjectionOnto_apply_eq_sum
    (b : OrthonormalBasis ι 𝕜 U) (x : E) :
    U.orthogonalProjectionOnto x =
      ∑ i : ι, inner 𝕜 (b i : E) x • b i :=
  b.orthogonalProjectionOnto_apply_eq_sum x

/--
Orthogonal projection onto `U`, valued in `U`, as a sum of rank-one maps associated to an
orthonormal basis of `U`.
@isnad1 id=eq.0h5v.s15.d2b81c79344d from=translated src=- shape=106d1936 vocab=62c88ab1
-/
theorem orthogonalProjectionOnto_eq_sum_rankOne (b : OrthonormalBasis ι 𝕜 U) :
    U.orthogonalProjectionOnto =
      ∑ i : ι, InnerProductSpace.rankOne 𝕜 (b i) (b i : E) :=
  b.orthogonalProjectionOnto_eq_sum_rankOne

/-- Orthogonal projection onto `U`, as an endomorphism, expanded in an orthonormal basis of `U`.
@isnad1 id=eq.0h6v.s10.1362be3d56c5 from=translated src=- shape=04b1ba4c vocab=dbf94539
-/
theorem starProjection_apply_eq_sum (b : OrthonormalBasis ι 𝕜 U) (x : E) :
    U.starProjection x =
      ∑ i : ι, inner 𝕜 (b i : E) x • (b i : E) := by
  rw [Submodule.starProjection_apply]
  simpa [map_sum] using congrArg Subtype.val (b.orthogonalProjectionOnto_apply_eq_sum x)

/--
Orthogonal projection onto `U`, as an endomorphism, is the sum of rank-one projections associated
to an orthonormal basis of `U`.
@isnad1 id=eq.0h5v.s13.d3da63deead7 from=translated src=- shape=54ca2d8e vocab=51cf6430
-/
theorem starProjection_eq_sum_rankOne (b : OrthonormalBasis ι 𝕜 U) :
    U.starProjection =
      ∑ i : ι, InnerProductSpace.rankOne 𝕜 (b i : E) (b i : E) :=
  b.starProjection_eq_sum_rankOne

end Submodule
