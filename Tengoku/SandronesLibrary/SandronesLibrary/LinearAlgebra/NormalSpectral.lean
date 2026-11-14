/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.LinearAlgebra.NormalMatrix
import Tengoku.Seed.Analysis.InnerProductSpace.JointEigenspace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# LinearAlgebra / NormalSpectral —— 正规矩阵的酉谱定理

本文件证明一般复正规矩阵可被酉矩阵对角化。证明先把正规矩阵分解成两个可交换的
Hermitian 矩阵，再将联合特征空间的无限指标缩到有限谱，收集共同特征向量构成的
正交归一基，最后把换基矩阵识别为酉矩阵。

> **Entry**: linear-algebra.matrix.normal
-/

namespace SandronesLibrary.LinearAlgebra.NormalMatrix

open scoped Matrix
open SandronesLibrary.LinearAlgebra.OrthogonalUnitary

variable {n : Type*} [Fintype n] [DecidableEq n]

set_option maxHeartbeats 2000000 in
/-- 可交换 Hermitian 矩阵存在共同特征向量组成的正交归一基。-/
private theorem commuting_hermitian_joint_orthonormalBasis
    {H K : Matrix n n ℂ}
    (hH : IsHermitianMatrix H) (hK : IsHermitianMatrix K)
    (hcomm : H * K = K * H) :
    ∃ (b : OrthonormalBasis n ℂ (EuclideanSpace ℂ n)) (a c : n → ℂ),
      (∀ j, H *ᵥ ⇑(b j) = a j • ⇑(b j)) ∧
      (∀ j, K *ᵥ ⇑(b j) = c j • ⇑(b j)) := by
  let T := Matrix.toEuclideanLin H
  let S := Matrix.toEuclideanLin K
  have hTs : T.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hH
  have hSs : S.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hK
  have hTS : Commute T S := by
    rw [commute_iff_eq]
    apply LinearMap.ext
    intro x
    rw [Module.End.mul_apply, Module.End.mul_apply]
    dsimp only [T, S]
    apply PiLp.ext
    intro i
    simp only [Matrix.ofLp_toLpLin]
    calc
      (H *ᵥ (K *ᵥ x.ofLp)) i = ((H * K) *ᵥ x.ofLp) i :=
        congrFun (Matrix.mulVec_mulVec x.ofLp H K) i
      _ = ((K * H) *ᵥ x.ofLp) i := by rw [hcomm]
      _ = (K *ᵥ (H *ᵥ x.ofLp)) i :=
        congrFun (Matrix.mulVec_mulVec x.ofLp K H).symm i
  let sT : Finset ℂ := Finset.univ.image
    (fun i : Fin (Fintype.card n) => (hTs.eigenvalues finrank_euclideanSpace i : ℂ))
  let sS : Finset ℂ := Finset.univ.image
    (fun i : Fin (Fintype.card n) => (hSs.eigenvalues finrank_euclideanSpace i : ℂ))
  let V : (↥sS × ↥sT) → Submodule ℂ (EuclideanSpace ℂ n) := fun z =>
    Module.End.eigenspace T z.2.1 ⊓ Module.End.eigenspace S z.1.1
  let f : (↥sS × ↥sT) → ℂ × ℂ := fun z => (z.1.1, z.2.1)
  have hf : Function.Injective f := by
    intro x y hxy
    apply Prod.ext <;> apply Subtype.ext
    · exact congrArg Prod.fst hxy
    · exact congrArg Prod.snd hxy
  have hAll := hTs.directSum_isInternal_of_commute hSs hTS
  have hAllOrth := hTs.orthogonalFamily_eigenspace_inf_eigenspace hSs
  have hInd : iSupIndep V := by
    change iSupIndep ((fun i : ℂ × ℂ =>
      Module.End.eigenspace T i.2 ⊓ Module.End.eigenspace S i.1) ∘ f)
    exact hAll.submodule_iSupIndep.comp hf
  have hTop : ⨆ z, V z = ⊤ := by
    apply top_unique
    rw [← hAll.submodule_iSup_eq_top]
    refine iSup_le fun z => ?_
    let W := Module.End.eigenspace T z.2 ⊓ Module.End.eigenspace S z.1
    by_cases hW : W = ⊥
    · simpa only [W, hW] using (bot_le : (⊥ : Submodule ℂ (EuclideanSpace ℂ n)) ≤ ⨆ z, V z)
    · have hTne : Module.End.eigenspace T z.2 ≠ ⊥ := by
        intro h
        apply hW
        simp [W, h]
      have hSne : Module.End.eigenspace S z.1 ≠ ⊥ := by
        intro h
        apply hW
        simp [W, h]
      obtain ⟨iT, hiT⟩ := hTs.exists_eigenvalues_eq finrank_euclideanSpace
        (Module.End.hasEigenvalue_iff.mpr hTne)
      obtain ⟨iS, hiS⟩ := hSs.exists_eigenvalues_eq finrank_euclideanSpace
        (Module.End.hasEigenvalue_iff.mpr hSne)
      have hzT : z.2 ∈ sT := by
        rw [← hiT]
        exact Finset.mem_image.mpr ⟨iT, Finset.mem_univ _, rfl⟩
      have hzS : z.1 ∈ sS := by
        rw [← hiS]
        exact Finset.mem_image.mpr ⟨iS, Finset.mem_univ _, rfl⟩
      let z' : ↥sS × ↥sT := (⟨z.1, hzS⟩, ⟨z.2, hzT⟩)
      exact le_iSup V z'
  have hInt : DirectSum.IsInternal V :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hInd hTop
  have hOrth : OrthogonalFamily ℂ (fun z => V z) (fun z => (V z).subtypeₗᵢ) := by
    simpa only [V, f] using hAllOrth.comp hf
  let ecard : Fin (Fintype.card n) ≃ n :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  let e₀ := hInt.subordinateOrthonormalBasis finrank_euclideanSpace hOrth
  let e : OrthonormalBasis n ℂ (EuclideanSpace ℂ n) := e₀.reindex ecard
  let χ : n → ↥sS × ↥sT := fun j =>
    hInt.subordinateOrthonormalBasisIndex finrank_euclideanSpace (ecard.symm j) hOrth
  refine ⟨e, fun j => (χ j).2.1, fun j => (χ j).1.1, ?_, ?_⟩
  · intro j
    have hj := hInt.subordinateOrthonormalBasis_subordinate
      finrank_euclideanSpace (ecard.symm j) hOrth
    have heq := Module.End.mem_eigenspace_iff.mp hj.1
    have heq' := congrArg (fun x : EuclideanSpace ℂ n => x.ofLp) heq
    dsimp only [e, χ]
    rw [OrthonormalBasis.reindex_apply]
    have he₀ : e₀ = hInt.subordinateOrthonormalBasis finrank_euclideanSpace hOrth := rfl
    rw [he₀]
    simpa only [T, Matrix.ofLp_toLpLin, Matrix.toLin'_apply', Matrix.mulVecLin_apply,
      WithLp.ofLp_smul] using heq'
  · intro j
    have hj := hInt.subordinateOrthonormalBasis_subordinate
      finrank_euclideanSpace (ecard.symm j) hOrth
    have heq := Module.End.mem_eigenspace_iff.mp hj.2
    have heq' := congrArg (fun x : EuclideanSpace ℂ n => x.ofLp) heq
    dsimp only [e, χ]
    rw [OrthonormalBasis.reindex_apply]
    have he₀ : e₀ = hInt.subordinateOrthonormalBasis finrank_euclideanSpace hOrth := rfl
    rw [he₀]
    simpa only [S, Matrix.ofLp_toLpLin, Matrix.toLin'_apply', Matrix.mulVecLin_apply,
      WithLp.ofLp_smul] using heq'

/-- 两个可交换 Hermitian 矩阵可以被同一个酉矩阵同时对角化。-/
private theorem commuting_hermitian_simultaneously_diagonalizable
    {H K : Matrix n n ℂ}
    (hH : IsHermitianMatrix H) (hK : IsHermitianMatrix K)
    (hcomm : H * K = K * H) :
    ∃ (U : Matrix n n ℂ) (a b : n → ℂ),
      IsUnitaryMatrix U ∧
      H = U * Matrix.diagonal a * Uᴴ ∧
      K = U * Matrix.diagonal b * Uᴴ := by
  obtain ⟨e, a, b, hHe, hKe⟩ :=
    commuting_hermitian_joint_orthonormalBasis hH hK hcomm
  let U : Matrix n n ℂ :=
    (EuclideanSpace.basisFun n ℂ).toBasis.toMatrix e.toBasis
  have hUmem : U ∈ Matrix.unitaryGroup n ℂ :=
    (EuclideanSpace.basisFun n ℂ).toMatrix_orthonormalBasis_mem_unitary e
  have hU : IsUnitaryMatrix U := by
    exact hUmem.1
  have hU_apply (i j : n) : U i j = ⇑(e j) i := rfl
  have hHU : H * U = U * Matrix.diagonal a := by
    ext i j
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, hU_apply, Matrix.diagonal, mul_comm] using
      congrFun (hHe j) i
  have hKU : K * U = U * Matrix.diagonal b := by
    ext i j
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, hU_apply, Matrix.diagonal, mul_comm] using
      congrFun (hKe j) i
  have hUright : U * Uᴴ = 1 := by
    change U * star U = 1
    exact hUmem.2
  refine ⟨U, a, b, hU, ?_, ?_⟩
  · calc
      H = H * 1 := by simp
      _ = H * (U * Uᴴ) := by rw [hUright]
      _ = (H * U) * Uᴴ := by rw [Matrix.mul_assoc]
      _ = U * Matrix.diagonal a * Uᴴ := by rw [hHU]
  · calc
      K = K * 1 := by simp
      _ = K * (U * Uᴴ) := by rw [hUright]
      _ = (K * U) * Uᴴ := by rw [Matrix.mul_assoc]
      _ = U * Matrix.diagonal b * Uᴴ := by rw [hKU]

/-- 乘以 `-i` 将斜 Hermitian 矩阵化为 Hermitian 矩阵。-/
private theorem negI_smul_skewHermitian_isHermitian
    {K : Matrix n n ℂ} (hK : IsSkewHermitianMatrix K) :
    IsHermitianMatrix ((-Complex.I) • K) := by
  rw [IsHermitianMatrix, Matrix.conjTranspose_smul, hK]
  simp

/-- 一般复正规矩阵的酉谱定理。
@isnad1 id=ex.1h2v.s6.705a435462f6 from=translated src=- shape=600c6e74 vocab=c61f6d0c
-/
theorem normal_unitary_diagonalization {A : Matrix n n ℂ}
    (hA : IsNormalMatrix A) :
    ∃ (U : Matrix n n ℂ) (eig : n → ℂ),
      IsUnitaryMatrix U ∧
        A = U * Matrix.diagonal eig * Uᴴ := by
  let H := hermitianPart A
  let K := skewHermitianPart A
  have hH : IsHermitianMatrix H := hermitianPart_isHermitian A
  have hK : IsSkewHermitianMatrix K := skewHermitianPart_isSkewHermitian A
  have hKi : IsHermitianMatrix ((-Complex.I) • K) :=
    negI_smul_skewHermitian_isHermitian hK
  have hcomm : H * ((-Complex.I) • K) = ((-Complex.I) • K) * H := by
    have hbase : (A + Aᴴ) * (A - Aᴴ) = (A - Aᴴ) * (A + Aᴴ) := by
      rw [IsNormalMatrix] at hA
      noncomm_ring [hA]
    dsimp [H, K, hermitianPart, skewHermitianPart]
    simp only [Matrix.smul_mul, Matrix.mul_smul]
    rw [hbase]
    module
  obtain ⟨U, a, b, hU, hHd, hKd⟩ :=
    commuting_hermitian_simultaneously_diagonalizable hH hKi hcomm
  refine ⟨U, fun i => a i + Complex.I * b i, hU, ?_⟩
  rw [← hermitian_add_skewHermitian A]
  change H + K = _
  rw [hHd]
  have hK_from : K = Complex.I • ((-Complex.I) • K) := by
    simp [smul_smul]
  rw [hK_from, hKd]
  calc
    _ = (U * Matrix.diagonal a) * Uᴴ +
        (U * (Complex.I • Matrix.diagonal b)) * Uᴴ := by
          congr 1
          rw [← Matrix.smul_mul, Matrix.mul_smul]
    _ = U * (Matrix.diagonal a + Complex.I • Matrix.diagonal b) * Uᴴ := by
          noncomm_ring
    _ = _ := by
      congr 2
      ext i j
      by_cases hij : i = j <;> simp [Matrix.diagonal, hij]

end SandronesLibrary.LinearAlgebra.NormalMatrix
