/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.LinearAlgebra.MatrixSVD

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# LinearAlgebra / MatrixPolar —— 极分解

本文件从奇异值分解构造有限维实或复内积空间之间线性映射的极分解
`T = U |T|`。正因子 `|T|` 在右奇异基上逐坐标乘以奇异值，因此正半定并满足
`|T|² = T†T`；因子 `U` 把正奇异方向等距送到相应左奇异方向，并在核方向取零。

这里的“部分等距”采用教材定义：在线性映射核的正交方向上保持范数。公开接口始终
使用有限维 `LinearMap`；连续线性映射只在证明正性时用于复用秩一算子的底层结果。

> **Entry**: linear-algebra.decomposition.polar
-/

namespace SandronesLibrary.LinearAlgebra.MatrixDecomposition

open Module

universe u v

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
  {F : Type v} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-- 线性映射是部分等距，若它在核的正交方向上保持范数。这里将“与核正交”直接写成
对所有被 `U` 消去的向量内积为零，避免在教材层接口暴露子空间结构。-/
def IsPartialIsometry (U : E →ₗ[𝕜] F) : Prop :=
  ∀ x, (∀ z, U z = 0 → inner 𝕜 x z = 0) → ‖U x‖ = ‖x‖

/-- 映射 `T` 的模 `|T|`：在 `T†T` 的有序正交特征基上，将第 `i` 个基向量乘以
第 `i` 个奇异值。-/
noncomputable def absoluteValue (T : E →ₗ[𝕜] F) : E →ₗ[𝕜] E :=
  (rightSingularBasis T).toBasis.constr 𝕜 fun i =>
    (T.singularValues i : 𝕜) • rightSingularBasis T i

/-- 给定扩充后的左奇异基，构造极分解中的部分等距因子。正奇异方向被送到对应
左奇异向量，秩之后的核方向被送到零。-/
noncomputable def polarPartialIsometry (T : E →ₗ[𝕜] F)
    (b : OrthonormalBasis (Fin (finrank 𝕜 F)) 𝕜 F) : E →ₗ[𝕜] F :=
  (rightSingularBasis T).toBasis.constr 𝕜 fun i =>
    if hi : i.val < finrank 𝕜 T.range then
      b (rangeIndexEmbedding T ⟨i.val, hi⟩)
    else 0

/-- `|T|` 在第 `i` 个右奇异向量上的作用是乘以第 `i` 个奇异值。-/
theorem absoluteValue_apply_rightBasis (T : E →ₗ[𝕜] F)
    (i : Fin (finrank 𝕜 E)) :
    absoluteValue T (rightSingularBasis T i) =
      (T.singularValues i : 𝕜) • rightSingularBasis T i := by
  exact (rightSingularBasis T).toBasis.constr_basis 𝕜 _ i

/-- `|T|` 是沿右奇异方向的非负秩一算子之和。这个表示式直接给出正半定性。-/
theorem absoluteValue_eq_sum_rankOne (T : E →ₗ[𝕜] F) :
    absoluteValue T = (∑ i : Fin (finrank 𝕜 E),
      (T.singularValues i : 𝕜) •
        InnerProductSpace.rankOne 𝕜 (rightSingularBasis T i)
          (rightSingularBasis T i)).toLinearMap := by
  apply (rightSingularBasis T).toBasis.ext
  intro j
  rw [absoluteValue]
  rw [(rightSingularBasis T).toBasis.constr_basis]
  change _ = (∑ i : Fin (finrank 𝕜 E),
    (T.singularValues i : 𝕜) •
      InnerProductSpace.rankOne 𝕜 (rightSingularBasis T i)
        (rightSingularBasis T i)) (rightSingularBasis T j)
  rw [_root_.sum_apply]
  simp_rw [smul_apply, InnerProductSpace.rankOne_apply, smul_smul]
  rw [Finset.sum_eq_single j]
  · rw [(orthonormal_iff_ite.mp (rightSingularBasis T).orthonormal j j)]
    simp
  · intro i hi hij
    rw [(orthonormal_iff_ite.mp (rightSingularBasis T).orthonormal i j), ite_eq_right hij]
    simp
  · simp

/-- 映射的模 `|T|` 是正半定算子。-/
theorem absoluteValue_isPositive (T : E →ₗ[𝕜] F) :
    (absoluteValue T).IsPositive := by
  rw [absoluteValue_eq_sum_rankOne T]
  apply ContinuousLinearMap.IsPositive.toLinearMap
  apply ContinuousLinearMap.isPositive_sum Finset.univ
  intro i hi
  apply (InnerProductSpace.isPositive_rankOne_self (rightSingularBasis T i)).smul_of_nonneg
  exact_mod_cast T.singularValues_nonneg i

/-- 映射的模是 `T†T` 的正半定平方根：`|T|² = T†T`。-/
theorem absoluteValue_sq (T : E →ₗ[𝕜] F) :
    (absoluteValue T).comp (absoluteValue T) = T.adjoint.comp T := by
  apply (rightSingularBasis T).toBasis.ext
  intro i
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  change absoluteValue T (absoluteValue T (rightSingularBasis T i)) =
    T.adjoint (T (rightSingularBasis T i))
  rw [
    absoluteValue_apply_rightBasis, map_smul,
    absoluteValue_apply_rightBasis, smul_smul]
  have heig := T.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis rfl i
  change T.adjoint (T (rightSingularBasis T i)) = _ at heig
  rw [heig, ← T.sq_singularValues_fin rfl i]
  simp [rightSingularBasis, pow_two]

theorem tail_coordinates_zero_of_orthogonal_kernel (T : E →ₗ[𝕜] F)
    (b : OrthonormalBasis (Fin (finrank 𝕜 F)) 𝕜 F) (x : E)
    (hx : ∀ z, polarPartialIsometry T b z = 0 → inner 𝕜 x z = 0) :
    ∀ i : Fin (finrank 𝕜 E), finrank 𝕜 T.range ≤ i.val →
      (rightSingularBasis T).repr x i = 0 := by
  intro i hi
  have hU := (rightSingularBasis T).toBasis.constr_basis 𝕜
    (fun j => if hj : j.val < finrank 𝕜 T.range then
      b (rangeIndexEmbedding T ⟨j.val, hj⟩) else 0) i
  change polarPartialIsometry T b (rightSingularBasis T i) = _ at hU
  rw [dite_eq_right (Nat.not_lt.mpr hi)] at hU
  have hinner := hx (rightSingularBasis T i) hU
  rw [OrthonormalBasis.repr_apply_apply]
  rw [← inner_conj_symm] at hinner
  exact star_eq_zero.mp hinner

private def rankIndexSubtypeEquiv {r n : ℕ} (h : r ≤ n) :
    {i : Fin n // i.val < r} ≃ Fin r where
  toFun i := ⟨i.val.val, i.property⟩
  invFun i := ⟨Fin.castLE h i, by simp⟩
  left_inv i := by ext; rfl
  right_inv i := by ext; rfl

theorem polarPartialIsometry_apply_eq_rank_sum (T : E →ₗ[𝕜] F)
    (b : OrthonormalBasis (Fin (finrank 𝕜 F)) 𝕜 F) (x : E) :
    polarPartialIsometry T b x =
      ∑ i : Fin (finrank 𝕜 T.range),
        (rightSingularBasis T).repr x
            (Fin.castLE (LinearMap.finrank_range_le T) i) •
          b (rangeIndexEmbedding T i) := by
  classical
  nth_rw 1 [← (rightSingularBasis T).sum_repr x]
  rw [map_sum]
  simp_rw [map_smul]
  have hbasis (j : Fin (finrank 𝕜 E)) :
      polarPartialIsometry T b (rightSingularBasis T j) =
        if hj : j.val < finrank 𝕜 T.range then
          b (rangeIndexEmbedding T ⟨j.val, hj⟩) else 0 := by
    exact (rightSingularBasis T).toBasis.constr_basis 𝕜 _ j
  simp_rw [hbasis]
  simp only [smul_dite, smul_zero]
  let p : Fin (finrank 𝕜 E) → Prop := fun j => j.val < finrank 𝕜 T.range
  let f : Fin (finrank 𝕜 E) → F := fun j =>
    if h : p j then (rightSingularBasis T).repr x j •
      b (rangeIndexEmbedding T ⟨j.val, h⟩) else 0
  change (∑ j, f j) = _
  calc
    (∑ j, f j) = ∑ j ∈ Finset.univ.filter p, f j := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j hj
      by_cases h : p j
      · rw [ite_eq_left h]
      · rw [ite_eq_right h]
        simp [f, h]
    _ = ∑ j : {j : Fin (finrank 𝕜 E) // p j}, f j := by
      exact Finset.sum_subtype _ (fun j => by simp [p]) f
    _ = _ := by
      apply Fintype.sum_equiv
        (rankIndexSubtypeEquiv (LinearMap.finrank_range_le T))
      intro i
      dsimp [f, p, rankIndexSubtypeEquiv]
      rw [dite_eq_left i.property]

theorem rank_sum_norm_eq_of_tail_coordinates_zero (T : E →ₗ[𝕜] F)
    (b : OrthonormalBasis (Fin (finrank 𝕜 F)) 𝕜 F) (x : E)
    (hx : ∀ i : Fin (finrank 𝕜 E), finrank 𝕜 T.range ≤ i.val →
      (rightSingularBasis T).repr x i = 0) :
    ‖∑ i : Fin (finrank 𝕜 T.range),
        (rightSingularBasis T).repr x
            (Fin.castLE (LinearMap.finrank_range_le T) i) •
          b (rangeIndexEmbedding T i)‖ = ‖x‖ := by
  classical
  let c : Fin (finrank 𝕜 T.range) → 𝕜 := fun i =>
    (rightSingularBasis T).repr x
      (Fin.castLE (LinearMap.finrank_range_le T) i)
  let v : Fin (finrank 𝕜 T.range) → F := fun i =>
    b (rangeIndexEmbedding T i)
  have hv : Orthonormal 𝕜 v :=
    b.orthonormal.comp (rangeIndexEmbedding T) (rangeIndexEmbedding T).injective
  let p : Fin (finrank 𝕜 E) → Prop := fun i => i.val < finrank 𝕜 T.range
  let g : Fin (finrank 𝕜 E) → ℝ := fun i =>
    ‖(rightSingularBasis T).repr x i‖ ^ 2
  have hsum : (∑ i, g i) = ∑ j : Fin (finrank 𝕜 T.range),
      g (Fin.castLE (LinearMap.finrank_range_le T) j) := by
    calc
      (∑ i, g i) = ∑ i ∈ Finset.univ.filter p, g i := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i hi
        by_cases hip : p i
        · rw [ite_eq_left hip]
        · rw [ite_eq_right hip]
          have hz := hx i (Nat.le_of_not_gt hip)
          simp [g, hz]
      _ = ∑ i : {i : Fin (finrank 𝕜 E) // p i}, g i := by
        exact Finset.sum_subtype _ (fun i => by simp [p]) g
      _ = _ := by
        apply Fintype.sum_equiv
          (rankIndexSubtypeEquiv (LinearMap.finrank_range_le T))
        intro i
        rfl
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  change ‖∑ i, c i • v i‖ ^ 2 = ‖x‖ ^ 2
  calc
    ‖∑ i, c i • v i‖ ^ 2 = RCLike.re (inner 𝕜 (∑ i, c i • v i) (∑ i, c i • v i)) :=
      norm_sq_eq_re_inner _
    _ = RCLike.re (∑ i, starRingEnd 𝕜 (c i) * c i) := by
      rw [hv.inner_sum c c Finset.univ]
    _ = ∑ i, ‖c i‖ ^ 2 := by
      rw [map_sum]
      simp [RCLike.conj_mul]
    _ = ∑ i, g (Fin.castLE (LinearMap.finrank_range_le T) i) := by rfl
    _ = ∑ i, g i := hsum.symm
    _ = ‖x‖ ^ 2 := by
      rw [← (rightSingularBasis T).repr.norm_map x,
        EuclideanSpace.norm_sq_eq]

theorem polarPartialIsometry_norm_eq_of_tail_coordinates_zero (T : E →ₗ[𝕜] F)
    (b : OrthonormalBasis (Fin (finrank 𝕜 F)) 𝕜 F) (x : E)
    (hx : ∀ i : Fin (finrank 𝕜 E), finrank 𝕜 T.range ≤ i.val →
      (rightSingularBasis T).repr x i = 0) :
    ‖polarPartialIsometry T b x‖ = ‖x‖ := by
  rw [polarPartialIsometry_apply_eq_rank_sum]
  exact rank_sum_norm_eq_of_tail_coordinates_zero T b x hx

/-- 由左右奇异方向配对得到的线性映射确实是部分等距。-/
theorem polarPartialIsometry_isPartialIsometry (T : E →ₗ[𝕜] F)
    (b : OrthonormalBasis (Fin (finrank 𝕜 F)) 𝕜 F) :
    IsPartialIsometry (polarPartialIsometry T b) := by
  intro x hx
  exact polarPartialIsometry_norm_eq_of_tail_coordinates_zero T b x
    (tail_coordinates_zero_of_orthogonal_kernel T b x hx)

/-- 部分等距因子与正因子的乘积还原原映射：`U |T| = T`。-/
theorem polarPartialIsometry_comp_absoluteValue (T : E →ₗ[𝕜] F)
    (b : OrthonormalBasis (Fin (finrank 𝕜 F)) 𝕜 F)
    (hb : ∀ i : Fin (finrank 𝕜 T.range),
      b (rangeIndexEmbedding T i) = leftSingularVector T i) :
    (polarPartialIsometry T b).comp (absoluteValue T) = T := by
  apply (rightSingularBasis T).toBasis.ext
  intro i
  rw [LinearMap.comp_apply]
  change polarPartialIsometry T b (absoluteValue T (rightSingularBasis T i)) =
    T (rightSingularBasis T i)
  rw [absoluteValue_apply_rightBasis, map_smul]
  have hU := (rightSingularBasis T).toBasis.constr_basis 𝕜
    (fun j => if hj : j.val < finrank 𝕜 T.range then
      b (rangeIndexEmbedding T ⟨j.val, hj⟩) else 0) i
  change polarPartialIsometry T b (rightSingularBasis T i) = _ at hU
  rw [hU]
  by_cases hi : i.val < finrank 𝕜 T.range
  · rw [dite_eq_left hi, hb ⟨i.val, hi⟩]
    exact (map_rightSingularBasis_eq_smul_leftSingularVector T ⟨i.val, hi⟩).symm
  · rw [dite_eq_right hi]
    have hzero := map_rightSingularBasis_eq_zero_of_finrank_range_le T i
      (Nat.le_of_not_gt hi)
    simpa using hzero.symm

/-- 线性映射的极分解证书：正半定因子平方为 `T†T`，部分等距因子与它的乘积为 `T`。-/
structure PolarDecomposition (T : E →ₗ[𝕜] F) where
  positivePart : E →ₗ[𝕜] E
  partialIsometry : E →ₗ[𝕜] F
  positive : positivePart.IsPositive
  square : positivePart.comp positivePart = T.adjoint.comp T
  isPartialIsometry : IsPartialIsometry partialIsometry
  factorization : partialIsometry.comp positivePart = T

/-- 任意有限维实或复内积空间之间的线性映射都存在极分解。-/
theorem exists_polarDecomposition (T : E →ₗ[𝕜] F) :
    Nonempty (PolarDecomposition T) := by
  obtain ⟨b, hb⟩ := exists_leftSingularBasis T
  exact ⟨{
    positivePart := absoluteValue T
    partialIsometry := polarPartialIsometry T b
    positive := absoluteValue_isPositive T
    square := absoluteValue_sq T
    isPartialIsometry := polarPartialIsometry_isPartialIsometry T b
    factorization := polarPartialIsometry_comp_absoluteValue T b hb }⟩

end SandronesLibrary.LinearAlgebra.MatrixDecomposition
