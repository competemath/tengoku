/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.LinearAlgebra.SubspaceSumQuotient
import Tengoku.SandronesLibrary.SandronesLibrary.LinearAlgebra.Coordinates
import Tengoku.SandronesLibrary.SandronesLibrary.LinearAlgebra.Eigenvalue

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# LinearAlgebra / Diagonalization —— 特征基、重数与多项式理论

本文件补齐有限维线性算子的标准对角化理论：特征基与对角矩阵表示等价，特征值的
几何重数不超过代数重数，特征多项式满足 Cayley–Hamilton 定理，并定义最小多项式及其
湮灭、整除和最小性。公开签名只使用本库教材层的向量空间、基、维数、矩阵和多项式语言；
mathlib 的模与子模结构仅出现在证明内部。

> **Entry**: linear-algebra.eigen.diagonalization
-/

namespace SandronesLibrary.LinearAlgebra.Diagonalization

open SandronesLibrary.LinearAlgebra.VectorSpace
open SandronesLibrary.LinearAlgebra.Coordinates
open SandronesLibrary.LinearAlgebra.Eigenvalue
open SandronesLibrary.LinearAlgebra.SubspaceTheory

variable {K V : Type*} [Field K] [AddCommGroup V] [LinearSpace K V]

/-- `b` 是 `T` 的特征基：它是一组基，且每个基向量都是某个标量对应的特征向量。-/
def IsEigenbasis {ι : Type*} [Fintype ι] (T : V →ₗ[K] V) (b : ι → V) : Prop :=
  IsBasis K b ∧ ∃ μ : ι → K, ∀ i, T (b i) = μ i • b i

/-- 特征基下，线性算子的矩阵是以相应特征值为对角元的对角矩阵。
@isnad1 id=ex.1h5v.s7.793284ba380c from=translated src=- shape=41451558 vocab=3ed84f8d
-/
theorem operatorMatrix_eq_diagonal_of_eigenbasis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : V →ₗ[K] V) (b : ι → V) (hb : IsEigenbasis T b) :
    ∃ μ : ι → K, operatorMatrix b hb.1 T = Matrix.diagonal μ := by
  rcases hb.2 with ⟨μ, hμ⟩
  refine ⟨μ, ?_⟩
  classical
  let B := Module.Basis.mk hb.1.1 (by simpa [hb.1.2])
  have hB (j : ι) : B j = b j := by simp [B]
  change LinearMap.toMatrix B B T = Matrix.diagonal μ
  ext i j
  rw [LinearMap.toMatrix_apply]
  rw [show T (B j) = μ j • B j by simpa [hB] using hμ j]
  by_cases hij : i = j
  · subst i
    simp
  · simp [hij]

/-- 反过来，若 `T` 在基 `b` 下的矩阵为对角矩阵，则 `b` 是 `T` 的特征基。
@isnad1 id=iseigenb.2h6v.s7.6a13a6070d07 from=translated src=- shape=b5b420e5 vocab=a0ef0d66
-/
theorem eigenbasis_of_operatorMatrix_eq_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : V →ₗ[K] V) (b : ι → V) (hb : IsBasis K b) (μ : ι → K)
    (hdiag : operatorMatrix b hb T = Matrix.diagonal μ) : IsEigenbasis T b := by
  refine ⟨hb, μ, ?_⟩
  intro j
  classical
  let B := Module.Basis.mk hb.1 (by simpa [hb.2])
  have hB (j : ι) : B j = b j := by simp [B]
  apply B.repr.injective
  ext i
  have hij := congrFun (congrFun hdiag i) j
  have hrepr : B.repr (b j) = Finsupp.single j 1 := by
    rw [← hB j]
    exact B.repr_self j
  rw [map_smul]
  calc
    B.repr (T (b j)) i = Matrix.diagonal μ i j := by
      simpa [operatorMatrix, B, LinearMap.toMatrix_apply] using hij
    _ = μ j * B.repr (b j) i := by
      rw [hrepr]
      by_cases h : i = j <;> simp [h]

/-- 特征基判据：存在特征基，当且仅当存在一组基使算子矩阵为对角阵。
@isnad1 id=iff.0h4v.s7.c7255a258150 from=translated src=- shape=cad03cae vocab=a0ef0d66
-/
theorem exists_eigenbasis_iff_exists_diagonal_matrix {ι : Type*} [Fintype ι]
    [DecidableEq ι] (T : V →ₗ[K] V) :
    (∃ b : ι → V, IsEigenbasis T b) ↔
      ∃ (b : ι → V) (hb : IsBasis K b) (μ : ι → K),
        operatorMatrix b hb T = Matrix.diagonal μ := by
  constructor
  · rintro ⟨b, hb⟩
    rcases operatorMatrix_eq_diagonal_of_eigenbasis T b hb with ⟨μ, hμ⟩
    exact ⟨b, hb.1, μ, hμ⟩
  · rintro ⟨b, hb, μ, hμ⟩
    exact ⟨b, eigenbasis_of_operatorMatrix_eq_diagonal T b hb μ hμ⟩

/-- 特征子空间本身是子空间。
@isnad1 id=issubspa.0h4v.s6.b2c040f61dc2 from=translated src=- shape=e9b7a911 vocab=ba8267a4
-/
theorem eigenspace_isSubspace (T : V →ₗ[K] V) (μ : K) :
    IsSubspace K (eigenspace K T μ) := by
  refine ⟨⟨0, by simp [eigenspace]⟩, ?_, ?_⟩
  · intro x hx y hy
    simp only [eigenspace, Set.mem_ofPred_eq] at hx hy ⊢
    rw [map_add, hx, hy, smul_add]
  · intro c x hx
    simp only [eigenspace, Set.mem_ofPred_eq] at hx ⊢
    rw [map_smul, hx, smul_smul, smul_smul, mul_comm]

/-- 特征值 `μ` 的几何重数：对应特征子空间的维数。-/
noncomputable def geometricMultiplicity (T : V →ₗ[K] V) (μ : K) : ℕ :=
  subspaceDim K (eigenspace K T μ) (eigenspace_isSubspace T μ)

/-- 线性算子的特征多项式。-/
noncomputable def characteristicPolynomial [IsFiniteDimensional K V]
    (T : V →ₗ[K] V) : Polynomial K :=
  LinearMap.charpoly T

/-- 特征值 `μ` 的代数重数：它作为特征多项式根的重数。-/
noncomputable def algebraicMultiplicity [IsFiniteDimensional K V]
    (T : V →ₗ[K] V) (μ : K) : ℕ :=
  (characteristicPolynomial T).rootMultiplicity μ

/-- 几何重数不超过代数重数。
@isnad1 id=le.0h4v.s6.7ac47bbe978b from=translated src=- shape=177ada54 vocab=00f04aa0
-/
theorem geometricMultiplicity_le_algebraicMultiplicity [IsFiniteDimensional K V]
    (T : V →ₗ[K] V) (μ : K) :
    geometricMultiplicity T μ ≤ algebraicMultiplicity T μ := by
  let S : Submodule K V :=
    { carrier := eigenspace K T μ
      zero_mem' := subspace_zero_mem (eigenspace_isSubspace T μ)
      add_mem' := by
        intro x y hx hy
        exact (eigenspace_isSubspace T μ).2.1 hx hy
      smul_mem' := by
        intro c x hx
        exact (eigenspace_isSubspace T μ).2.2 c hx }
  have hS : S = Module.End.eigenspace T μ := by
    ext x
    exact Module.End.mem_eigenspace_iff.symm
  change Module.finrank K S ≤
    Polynomial.rootMultiplicity μ (LinearMap.charpoly T)
  rw [hS]
  exact LinearMap.finrank_eigenspace_le T μ

/-- Cayley–Hamilton 定理：线性算子代入自身的特征多项式得到零算子。
@isnad1 id=eq.0h3v.s9.5390aee840fe from=translated src=- shape=1fb6e180 vocab=a8839bf0
-/
theorem cayleyHamilton [IsFiniteDimensional K V] (T : V →ₗ[K] V) :
    Polynomial.aeval T (characteristicPolynomial T) = 0 := by
  exact LinearMap.aeval_self_charpoly T

/-- 线性算子的最小多项式。-/
noncomputable def minimalPolynomial [IsFiniteDimensional K V]
    (T : V →ₗ[K] V) : Polynomial K :=
  minpoly K T

/-- 最小多项式代入算子后为零。
@isnad1 id=eq.0h3v.s9.d859afe1f576 from=translated src=- shape=1fb6e180 vocab=a059b520
-/
theorem minimalPolynomial_aeval [IsFiniteDimensional K V] (T : V →ₗ[K] V) :
    Polynomial.aeval T (minimalPolynomial T) = 0 := by
  exact minpoly.aeval K T

/-- 最小多项式整除特征多项式。
@isnad1 id=dvd.0h3v.s7.ea9152d3eaed from=translated src=- shape=320a600d vocab=517864d9
-/
theorem minimalPolynomial_dvd_characteristicPolynomial [IsFiniteDimensional K V]
    (T : V →ₗ[K] V) : minimalPolynomial T ∣ characteristicPolynomial T := by
  exact LinearMap.minpoly_dvd_charpoly T

/-- 最小性：任意能湮灭 `T` 的多项式都被最小多项式整除。
@isnad1 id=dvd.1h4v.s9.cf4a6c099028 from=translated src=- shape=56d99a4b vocab=11518746
-/
theorem minimalPolynomial_dvd_of_aeval_eq_zero [IsFiniteDimensional K V]
    (T : V →ₗ[K] V) (p : Polynomial K) (hp : Polynomial.aeval T p = 0) :
    minimalPolynomial T ∣ p := by
  exact minpoly.dvd K T hp

end SandronesLibrary.LinearAlgebra.Diagonalization
