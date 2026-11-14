/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.LinearAlgebra.JordanNormalForm
import Tengoku.SandronesLibrary.SandronesLibrary.Analysis.FundamentalTheoremAlgebra

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# LinearAlgebra / JordanSimilarity —— 矩阵的 Jordan 相似标准型

> **Entry**: linear-algebra.eigen.jordan-similarity
-/

namespace SandronesLibrary.LinearAlgebra.Jordan

open SandronesLibrary.LinearAlgebra.VectorSpace
open SandronesLibrary.LinearAlgebra.Coordinates

variable {K V : Type*} [Field K] [AddCommGroup V] [LinearSpace K V]

/-- 两个同阶矩阵相似：存在互逆的换基矩阵实现共轭。-/
def MatricesAreSimilar {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n K) : Prop :=
  ∃ P Q : Matrix n n K, P * Q = 1 ∧ Q * P = 1 ∧ B = P * A * Q

private theorem operatorMatrix_reindex_basis
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (b : ι → V) (hb : IsBasis K b)
    (hb' : IsBasis K (fun k => b (e.symm k))) (T : V →ₗ[K] V) :
    operatorMatrix (fun k => b (e.symm k)) hb' T =
      Matrix.reindex e e (operatorMatrix b hb T) := by
  classical
  let B : Module.Basis ι K V := Module.Basis.mk hb.1 (by simpa [hb.2])
  let B' : Module.Basis κ K V := B.reindex e
  have hB (i : ι) : B i = b i := by simp [B]
  have hB' (k : κ) : B' k = b (e.symm k) := by
    simp [B', hB]
  change LinearMap.toMatrix
      (Module.Basis.mk hb'.1 (by simpa [hb'.2]))
      (Module.Basis.mk hb'.1 (by simpa [hb'.2])) T =
    Matrix.reindex e e
      (LinearMap.toMatrix (Module.Basis.mk hb.1 (by simpa [hb.2]))
        (Module.Basis.mk hb.1 (by simpa [hb.2])) T)
  have hmk : Module.Basis.mk hb.1 (by simpa [hb.2]) = B := by
    ext i
    simp [B]
  have hmk' : Module.Basis.mk hb'.1 (by simpa [hb'.2]) = B' := by
    ext k
    simp [hB']
  rw [hmk, hmk']
  ext i j
  simp [LinearMap.toMatrix_apply, B', Matrix.reindex_apply]

/-- 代数闭域上的每个方阵都相似于一个 Jordan 标准矩阵。-/
theorem matrix_is_similar_to_jordan [IsAlgClosed K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) :
    ∃ (d : JordanFormData K)
      (e : (Σ i : d.Block, Fin (d.length i + 1)) ≃ Fin n),
      MatricesAreSimilar A (Matrix.reindex e e (jordanNormalMatrix d)) := by
  classical
  let T : (Fin n → K) →ₗ[K] (Fin n → K) := Matrix.toLin' A
  obtain ⟨d, hd⟩ := exists_jordan_normal_basis T
  letI := d.blockFintype
  change ∃ (b : (Σ i : d.Block, Fin (d.length i + 1)) → (Fin n → K))
    (hb : IsBasis K b), operatorMatrix b hb T = jordanNormalMatrix d at hd
  obtain ⟨b, hb, hmatrix⟩ := hd
  let I := Σ i : d.Block, Fin (d.length i + 1)
  let B : Module.Basis I K (Fin n → K) :=
    Module.Basis.mk hb.1 (by simpa [hb.2])
  have hcard : Fintype.card I = n := by
    have h := Module.finrank_eq_card_basis B
    simpa [I] using h.symm
  let e : I ≃ Fin n := Fintype.equivOfCardEq (by simpa using hcard)
  let b' : Fin n → (Fin n → K) := fun i => b (e.symm i)
  let B' : Module.Basis (Fin n) K (Fin n → K) := B.reindex e
  have hB' (i : Fin n) : B' i = b' i := by
    simp [B', B, b', e]
  have hB'fun : (B' : Fin n → (Fin n → K)) = b' := funext hB'
  have hb' : IsBasis K b' := by
    refine ⟨?_, ?_⟩
    · rw [← hB'fun]
      exact B'.linearIndependent
    · rw [← hB'fun]
      simpa using B'.span_eq
  have hJordan : operatorMatrix b' hb' T =
      Matrix.reindex e e (jordanNormalMatrix d) := by
    rw [operatorMatrix_reindex_basis e b hb hb' T, hmatrix]
  let std : Fin n → (Fin n → K) := fun i => Pi.single i 1
  have hstd : IsBasis K std := by
    let Std := Pi.basisFun K (Fin n)
    have hStd (i : Fin n) : Std i = std i := by
      ext j
      simp [Std, std, Pi.basisFun_apply]
    have hStdFun : (Std : Fin n → (Fin n → K)) = std := funext hStd
    refine ⟨?_, ?_⟩
    · rw [← hStdFun]
      exact Std.linearIndependent
    · rw [← hStdFun]
      simpa using Std.span_eq
  have hstandardMatrix : operatorMatrix std hstd T = A := by
    change LinearMap.toMatrix (Module.Basis.mk hstd.1 (by simpa [hstd.2]))
      (Module.Basis.mk hstd.1 (by simpa [hstd.2])) T = A
    have hBasisEq : Module.Basis.mk hstd.1 (by simpa [hstd.2]) =
        Pi.basisFun K (Fin n) := by
      ext i j
      simp [std, Pi.basisFun_apply]
    rw [hBasisEq, LinearMap.toMatrix_eq_toMatrix']
    exact LinearMap.toMatrix'_toLin' A
  let P := transitionMatrix std b' hstd hb'
  let Q := transitionMatrix b' std hb' hstd
  refine ⟨d, e, P, Q, ?_, ?_, ?_⟩
  · exact transitionMatrix_mul_reverse std b' hstd hb'
  · exact reverse_mul_transitionMatrix std b' hstd hb'
  · rw [← hJordan, operatorMatrix_change_basis std b' hstd hb' T,
      hstandardMatrix]

/-- **代数学基本定理的矩阵应用**：每个复方阵都相似于 Jordan 标准矩阵。

`FundamentalTheoremAlgebra` 先证明复数域代数闭；一般的代数闭域 Jordan 定理随后给出
有限个 Jordan 块、将这些块重编号为原矩阵下标的等价，以及实现相似变换的互逆矩阵。-/
theorem complex_matrix_is_similar_to_jordan {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃ (d : JordanFormData ℂ)
      (e : (Σ i : d.Block, Fin (d.length i + 1)) ≃ Fin n),
      MatricesAreSimilar A (Matrix.reindex e e (jordanNormalMatrix d)) := by
  letI : IsAlgClosed ℂ :=
    SandronesLibrary.Analysis.Complex.complex_is_algebraically_closed
  exact matrix_is_similar_to_jordan A

end SandronesLibrary.LinearAlgebra.Jordan
