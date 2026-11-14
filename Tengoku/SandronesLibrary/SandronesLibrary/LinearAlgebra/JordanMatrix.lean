/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.LinearAlgebra.JordanDecomposition

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# LinearAlgebra / JordanMatrix —— Jordan 链基的块对角矩阵

本文件把抽象的 Jordan 链族基转化为教材中的块对角 Jordan 矩阵。

> **Entry**: linear-algebra.eigen.jordan-block
-/

namespace SandronesLibrary.LinearAlgebra.Jordan

open SandronesLibrary.LinearAlgebra.VectorSpace
open SandronesLibrary.LinearAlgebra.Coordinates

variable {K V : Type*} [Field K] [AddCommGroup V] [LinearSpace K V]

/-- Jordan 链族按 `(链号, 链内位置)` 排列时，算子矩阵是相应 Jordan 块的块对角矩阵。-/
theorem operatorMatrix_eq_blockDiagonal_jordan
    (T : V →ₗ[K] V) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ι → K) (length : ι → ℕ)
    (b : (i : ι) → Fin (length i + 1) → V)
    (hb : IsBasis K (fun p : Σ i : ι, Fin (length i + 1) => b p.1 p.2) ∧
      ∀ i, IsJordanChain T (μ i) (b i)) :
    operatorMatrix (fun p : Σ i : ι, Fin (length i + 1) => b p.1 p.2) hb.1 T =
      Matrix.blockDiagonal' (fun i => jordanBlock (μ i) (length i)) := by
  classical
  let flat := fun p : Σ i : ι, Fin (length i + 1) => b p.1 p.2
  let B := Module.Basis.mk hb.1.1 (by simpa [hb.1.2])
  have hB (p : Σ i : ι, Fin (length i + 1)) : B p = flat p := by
    simp only [B, Module.Basis.coe_mk]
    rfl
  change LinearMap.toMatrix B B T =
    Matrix.blockDiagonal' (fun i => jordanBlock (μ i) (length i))
  ext p q
  rcases p with ⟨i, k⟩
  rcases q with ⟨j, l⟩
  refine Fin.cases ?_ (fun s => ?_) l
  · rw [LinearMap.toMatrix_apply]
    have hchain := (hb.2 j).2.1
    rw [show T (B ⟨j, 0⟩) = μ j • B ⟨j, 0⟩ by
      simpa [hB, flat] using hchain]
    by_cases hij : i = j
    · subst i
      by_cases hk : k = 0
      · subst k
        simp [Matrix.blockDiagonal'_apply, jordanBlock]
      · simp [Matrix.blockDiagonal'_apply, jordanBlock, Finsupp.single_apply, hk,
          Ne.symm hk]
    · simp [Matrix.blockDiagonal'_apply, jordanBlock, Finsupp.single_apply, hij]
  · rw [LinearMap.toMatrix_apply]
    have hchain := (hb.2 j).2.2 s
    rw [show T (B ⟨j, s.succ⟩) = μ j • B ⟨j, s.succ⟩ + B ⟨j, s.castSucc⟩ by
      simpa [hB, flat] using hchain]
    by_cases hij : i = j
    · subst i
      by_cases hsucc : k = s.succ
      · subst k
        simp [Matrix.blockDiagonal'_apply, jordanBlock, Finsupp.single_apply,
          Fin.ext_iff]
      · by_cases hprev : k = s.castSucc
        · subst k
          simp [Matrix.blockDiagonal'_apply, jordanBlock, Finsupp.single_apply,
            Fin.ext_iff]
        · have hvalSucc : k.val ≠ s.val + 1 := by
            intro h
            apply hsucc
            exact Fin.ext h
          have hvalPrev : k.val ≠ s.val := by
            intro h
            apply hprev
            exact Fin.ext h
          simp [Matrix.blockDiagonal'_apply, jordanBlock, Finsupp.single_apply,
            hsucc, hprev, hvalSucc, hvalPrev]
    · simp [Matrix.blockDiagonal'_apply, jordanBlock, Finsupp.single_apply, hij]

/-- 幂零算子在某组基下的矩阵是零特征值 Jordan 块的块对角矩阵。-/
theorem nilpotent_operator_has_jordan_matrix [IsFiniteDimensional K V]
    (N : V →ₗ[K] V) (hN : IsNilpotent N) :
    ∃ (r : ℕ) (length : Fin r → ℕ)
      (b : (i : Fin r) → Fin (length i + 1) → V)
      (hb : IsJordanBasisFamily N r (fun _ => 0) length b),
      operatorMatrix (fun p : Σ i : Fin r, Fin (length i + 1) => b p.1 p.2)
          hb.1 N = Matrix.blockDiagonal' (fun i => jordanBlock 0 (length i)) := by
  obtain ⟨r, length, b, hb⟩ := nilpotent_exists_jordanBasisFamily N hN
  exact ⟨r, length, b, hb,
    operatorMatrix_eq_blockDiagonal_jordan N (fun _ => 0) length b hb⟩

end SandronesLibrary.LinearAlgebra.Jordan
