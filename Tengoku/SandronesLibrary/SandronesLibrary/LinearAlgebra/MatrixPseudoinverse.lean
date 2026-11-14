/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.LinearAlgebra.MatrixPolar

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# LinearAlgebra / MatrixPseudoinverse —— Moore–Penrose 伪逆

本文件在有限维实或复内积空间上，从奇异值分解构造 Moore–Penrose 伪逆。
构造在正奇异值方向上乘以奇异值的倒数，在其余左奇异方向上取零。随后逐一验证
四条 Penrose 方程：两个反身方程，以及 `TT⁺`、`T⁺T` 的对称性。

后两条性质通过把两个复合映射写成正交基向量对应的秩一投影之和得到；这也明确说明
它们分别是值域投影与核的正交补投影。最终的存在定理只暴露有限维线性映射和四条
教材式性质，不在公开签名中暴露实现所用的子空间结构。

> **Entry**: linear-algebra.decomposition.pseudoinverse
-/

namespace SandronesLibrary.LinearAlgebra.MatrixDecomposition

open Module

universe u v

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
  {F : Type v} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-- 给定扩充左奇异基的 Moore–Penrose 伪逆候选：在前 `rank T` 个方向上
除以对应奇异值，在左零空间方向上取零。-/
noncomputable def pseudoinverseWith (T : E →ₗ[𝕜] F)
    (b : OrthonormalBasis (Fin (finrank 𝕜 F)) 𝕜 F) : F →ₗ[𝕜] E :=
  b.toBasis.constr 𝕜 fun j =>
    if hj : j.val < finrank 𝕜 T.range then
      ((T.singularValues j : 𝕜)⁻¹) •
        rightSingularBasis T
          (Fin.castLE (LinearMap.finrank_range_le T) ⟨j.val, hj⟩)
    else 0

/-- 第一条 Penrose 方程 `TT⁺T = T`。证明在右奇异基上逐方向计算。
@isnad1 id=eq.1h5v.s11.31d50178ad84 from=translated src=- shape=bf2ff1a2 vocab=083a546e
-/
theorem pseudoinverseWith_penrose_one (T : E →ₗ[𝕜] F)
    (b : OrthonormalBasis (Fin (finrank 𝕜 F)) 𝕜 F)
    (hb : ∀ i : Fin (finrank 𝕜 T.range),
      b (rangeIndexEmbedding T i) = leftSingularVector T i) :
    T.comp ((pseudoinverseWith T b).comp T) = T := by
  apply (rightSingularBasis T).toBasis.ext
  intro i
  simp only [LinearMap.comp_apply]
  change T (pseudoinverseWith T b (T (rightSingularBasis T i))) =
    T (rightSingularBasis T i)
  by_cases hi : i.val < finrank 𝕜 T.range
  · let k : Fin (finrank 𝕜 T.range) := ⟨i.val, hi⟩
    have hT := map_rightSingularBasis_eq_smul_leftSingularVector T k
    have hσ : T.singularValues k ≠ 0 := ne_of_gt
      (T.singularValues_pos_iff_lt_finrank_range.mpr k.isLt)
    rw [show rightSingularBasis T i = rightSingularBasis T
      (Fin.castLE (LinearMap.finrank_range_le T) k) by rfl]
    rw [hT, ← hb k, map_smul]
    have hG := b.toBasis.constr_basis 𝕜
      (fun j => if hj : j.val < finrank 𝕜 T.range then
        ((T.singularValues j : 𝕜)⁻¹) • rightSingularBasis T
          (Fin.castLE (LinearMap.finrank_range_le T) ⟨j.val, hj⟩) else 0)
      (rangeIndexEmbedding T k)
    change pseudoinverseWith T b (b (rangeIndexEmbedding T k)) = _ at hG
    rw [hG]
    rw [dite_eq_left (by exact k.isLt)]
    change T ((T.singularValues k : 𝕜) •
      ((T.singularValues k : 𝕜)⁻¹ •
        rightSingularBasis T (Fin.castLE (LinearMap.finrank_range_le T) k))) =
      (T.singularValues k : 𝕜) • b (rangeIndexEmbedding T k)
    rw [map_smul, map_smul, hT, ← hb k, smul_smul, smul_smul]
    have hσK : (T.singularValues k : 𝕜) ≠ 0 := by exact_mod_cast hσ
    field_simp
  · have hT := map_rightSingularBasis_eq_zero_of_finrank_range_le T i
      (Nat.le_of_not_gt hi)
    simp [hT]

/-- 第二条 Penrose 方程 `T⁺TT⁺ = T⁺`。正奇异值及其倒数相消，零方向保持为零。
@isnad1 id=eq.1h5v.s11.4cb3a257064c from=translated src=- shape=b69f0612 vocab=083a546e
-/
theorem pseudoinverseWith_penrose_two (T : E →ₗ[𝕜] F)
    (b : OrthonormalBasis (Fin (finrank 𝕜 F)) 𝕜 F)
    (hb : ∀ i : Fin (finrank 𝕜 T.range),
      b (rangeIndexEmbedding T i) = leftSingularVector T i) :
    (pseudoinverseWith T b).comp (T.comp (pseudoinverseWith T b)) =
      pseudoinverseWith T b := by
  apply b.toBasis.ext
  intro j
  simp only [LinearMap.comp_apply]
  have hG := b.toBasis.constr_basis 𝕜
    (fun q => if hq : q.val < finrank 𝕜 T.range then
      ((T.singularValues q : 𝕜)⁻¹) • rightSingularBasis T
        (Fin.castLE (LinearMap.finrank_range_le T) ⟨q.val, hq⟩) else 0) j
  change pseudoinverseWith T b (b j) = _ at hG
  change pseudoinverseWith T b (T (pseudoinverseWith T b (b j))) =
    pseudoinverseWith T b (b j)
  rw [hG]
  by_cases hj : j.val < finrank 𝕜 T.range
  · rw [dite_eq_left hj]
    let k : Fin (finrank 𝕜 T.range) := ⟨j.val, hj⟩
    have hσ : T.singularValues k ≠ 0 := ne_of_gt
      (T.singularValues_pos_iff_lt_finrank_range.mpr k.isLt)
    have hT := map_rightSingularBasis_eq_smul_leftSingularVector T k
    have hGk := b.toBasis.constr_basis 𝕜
      (fun q => if hq : q.val < finrank 𝕜 T.range then
        ((T.singularValues q : 𝕜)⁻¹) • rightSingularBasis T
          (Fin.castLE (LinearMap.finrank_range_le T) ⟨q.val, hq⟩) else 0)
      (rangeIndexEmbedding T k)
    change pseudoinverseWith T b (b (rangeIndexEmbedding T k)) = _ at hGk
    have hidx : rangeIndexEmbedding T k = j := by
      apply Fin.ext
      rfl
    rw [hidx] at hGk
    change pseudoinverseWith T b
      (T (((T.singularValues k : 𝕜)⁻¹) •
        rightSingularBasis T (Fin.castLE (LinearMap.finrank_range_le T) k))) = _
    rw [map_smul, hT, ← hb k, map_smul, map_smul]
    rw [hidx, hGk, dite_eq_left hj]
    have hσK : (T.singularValues k : 𝕜) ≠ 0 := by exact_mod_cast hσ
    dsimp [k] at hσK ⊢
    simp [smul_smul, hσK]
  · rw [dite_eq_right hj]
    simp

/-- 从一组正交基向量选出的秩一投影之和，在被选中的基向量上为恒等，
在未选中的基向量上为零。
@isnad1 id=eq.0h7v.s12.d9d1096f9e25 from=translated src=- shape=9735e078 vocab=e1ec1a1b
-/
theorem orthonormalBasis_sum_rankOne_apply
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    {m r : ℕ} (b : OrthonormalBasis (Fin m) 𝕜 G)
    (e : Fin r ↪ Fin m) (j : Fin m) :
    (∑ i : Fin r, InnerProductSpace.rankOne 𝕜 (b (e i)) (b (e i))) (b j) =
      if _h : ∃ i, e i = j then b j else 0 := by
  simp only [_root_.sum_apply, InnerProductSpace.rankOne_apply]
  by_cases h : ∃ i, e i = j
  · obtain ⟨i, rfl⟩ := h
    rw [dite_eq_left ⟨i, rfl⟩]
    rw [Finset.sum_eq_single i]
    · simp
    · intro q _ hqi
      have he : e q ≠ e i := fun h => hqi (e.injective h)
      rw [orthonormal_iff_ite.mp b.orthonormal]
      simp [he]
    · simp
  · rw [dite_eq_right h]
    apply Finset.sum_eq_zero
    intro i _
    have he : e i ≠ j := fun hij => h ⟨i, hij⟩
    rw [orthonormal_iff_ite.mp b.orthonormal]
    simp [he]

/-- `TT⁺` 在扩充左奇异基上的作用：值域方向保持不变，其余方向归零。
@isnad1 id=eq.1h6v.s12.e811e4aa7313 from=translated src=- shape=a3382f31 vocab=9de1de28
-/
theorem rangeProjection_apply_leftBasis (T : E →ₗ[𝕜] F)
    (b : OrthonormalBasis (Fin (finrank 𝕜 F)) 𝕜 F)
    (hb : ∀ i : Fin (finrank 𝕜 T.range),
      b (rangeIndexEmbedding T i) = leftSingularVector T i)
    (j : Fin (finrank 𝕜 F)) :
    T (pseudoinverseWith T b (b j)) =
      if _h : j.val < finrank 𝕜 T.range then b j else 0 := by
  have hG := b.toBasis.constr_basis 𝕜
    (fun q => if hq : q.val < finrank 𝕜 T.range then
      ((T.singularValues q : 𝕜)⁻¹) • rightSingularBasis T
        (Fin.castLE (LinearMap.finrank_range_le T) ⟨q.val, hq⟩) else 0) j
  change pseudoinverseWith T b (b j) = _ at hG
  rw [hG]
  by_cases hj : j.val < finrank 𝕜 T.range
  · rw [dite_eq_left hj, dite_eq_left hj]
    let k : Fin (finrank 𝕜 T.range) := ⟨j.val, hj⟩
    have hT := map_rightSingularBasis_eq_smul_leftSingularVector T k
    have hσ : T.singularValues k ≠ 0 := ne_of_gt
      (T.singularValues_pos_iff_lt_finrank_range.mpr k.isLt)
    have hidx : rangeIndexEmbedding T k = j := Fin.ext rfl
    change T (((T.singularValues k : 𝕜)⁻¹) •
      rightSingularBasis T (Fin.castLE (LinearMap.finrank_range_le T) k)) = b j
    rw [map_smul, hT, ← hb k, hidx, smul_smul]
    have hσK : (T.singularValues k : 𝕜) ≠ 0 := by exact_mod_cast hσ
    simp [hσK]
  · rw [dite_eq_right hj, dite_eq_right hj]
    simp

/-- `T⁺T` 在右奇异基上的作用：正奇异方向保持不变，核方向归零。
@isnad1 id=eq.1h6v.s12.9a2214b29200 from=translated src=- shape=3dd9a51a vocab=bfbff530
-/
theorem kernelProjection_apply_rightBasis (T : E →ₗ[𝕜] F)
    (b : OrthonormalBasis (Fin (finrank 𝕜 F)) 𝕜 F)
    (hb : ∀ i : Fin (finrank 𝕜 T.range),
      b (rangeIndexEmbedding T i) = leftSingularVector T i)
    (j : Fin (finrank 𝕜 E)) :
    pseudoinverseWith T b (T (rightSingularBasis T j)) =
      if _h : j.val < finrank 𝕜 T.range then rightSingularBasis T j else 0 := by
  by_cases hj : j.val < finrank 𝕜 T.range
  · rw [dite_eq_left hj]
    let k : Fin (finrank 𝕜 T.range) := ⟨j.val, hj⟩
    have hT := map_rightSingularBasis_eq_smul_leftSingularVector T k
    have hσ : T.singularValues k ≠ 0 := ne_of_gt
      (T.singularValues_pos_iff_lt_finrank_range.mpr k.isLt)
    rw [show rightSingularBasis T j = rightSingularBasis T
      (Fin.castLE (LinearMap.finrank_range_le T) k) by rfl]
    rw [hT, ← hb k, map_smul]
    have hG := b.toBasis.constr_basis 𝕜
      (fun q => if hq : q.val < finrank 𝕜 T.range then
        ((T.singularValues q : 𝕜)⁻¹) • rightSingularBasis T
          (Fin.castLE (LinearMap.finrank_range_le T) ⟨q.val, hq⟩) else 0)
      (rangeIndexEmbedding T k)
    change pseudoinverseWith T b (b (rangeIndexEmbedding T k)) = _ at hG
    rw [hG, dite_eq_left (by exact k.isLt)]
    change (T.singularValues k : 𝕜) •
      (((T.singularValues k : 𝕜)⁻¹) •
        rightSingularBasis T (Fin.castLE (LinearMap.finrank_range_le T) k)) = _
    have hσK : (T.singularValues k : 𝕜) ≠ 0 := by exact_mod_cast hσ
    simp [smul_smul, hσK]
  · rw [dite_eq_right hj]
    have hT := map_rightSingularBasis_eq_zero_of_finrank_range_le T j
      (Nat.le_of_not_gt hj)
    simp [hT]

/-- `TT⁺` 是由左奇异向量生成的秩一正交投影之和。
@isnad1 id=eq.1h5v.s14.77c42b2916fd from=translated src=- shape=2c003fc0 vocab=e0c1cfe0
-/
theorem pseudoinverseWith_rangeProjection_eq_sum_rankOne (T : E →ₗ[𝕜] F)
    (b : OrthonormalBasis (Fin (finrank 𝕜 F)) 𝕜 F)
    (hb : ∀ i : Fin (finrank 𝕜 T.range),
      b (rangeIndexEmbedding T i) = leftSingularVector T i) :
    T.comp (pseudoinverseWith T b) =
      (∑ i : Fin (finrank 𝕜 T.range),
        InnerProductSpace.rankOne 𝕜 (b (rangeIndexEmbedding T i))
          (b (rangeIndexEmbedding T i))).toLinearMap := by
  apply b.toBasis.ext
  intro j
  simp only [LinearMap.comp_apply]
  change T (pseudoinverseWith T b (b j)) = _
  rw [rangeProjection_apply_leftBasis T b hb j]
  change _ = (∑ i : Fin (finrank 𝕜 T.range),
    InnerProductSpace.rankOne 𝕜 (b (rangeIndexEmbedding T i))
      (b (rangeIndexEmbedding T i))) (b j)
  rw [orthonormalBasis_sum_rankOne_apply b (rangeIndexEmbedding T) j]
  have hiff : j.val < finrank 𝕜 T.range ↔
      ∃ i, rangeIndexEmbedding T i = j := by
    constructor
    · intro hj
      exact ⟨⟨j.val, hj⟩, Fin.ext rfl⟩
    · rintro ⟨i, hi⟩
      have hval := congrArg Fin.val hi.symm
      rw [hval]
      exact i.isLt
  by_cases hj : j.val < finrank 𝕜 T.range
  · rw [dite_eq_left hj, dite_eq_left (hiff.mp hj)]
  · rw [dite_eq_right hj, dite_eq_right (fun h => hj (hiff.mpr h))]

/-- `T⁺T` 是由正奇异值对应的右奇异向量生成的秩一正交投影之和。
@isnad1 id=eq.1h5v.s13.229ad126065a from=translated src=- shape=0d07a544 vocab=50cdf392
-/
theorem pseudoinverseWith_kernelProjection_eq_sum_rankOne (T : E →ₗ[𝕜] F)
    (b : OrthonormalBasis (Fin (finrank 𝕜 F)) 𝕜 F)
    (hb : ∀ i : Fin (finrank 𝕜 T.range),
      b (rangeIndexEmbedding T i) = leftSingularVector T i) :
    (pseudoinverseWith T b).comp T =
      (∑ i : Fin (finrank 𝕜 T.range),
        InnerProductSpace.rankOne 𝕜
          (rightSingularBasis T (Fin.castLE (LinearMap.finrank_range_le T) i))
          (rightSingularBasis T (Fin.castLE
            (LinearMap.finrank_range_le T) i))).toLinearMap := by
  apply (rightSingularBasis T).toBasis.ext
  intro j
  simp only [LinearMap.comp_apply]
  change pseudoinverseWith T b (T (rightSingularBasis T j)) = _
  rw [kernelProjection_apply_rightBasis T b hb j]
  change _ = (∑ i : Fin (finrank 𝕜 T.range),
    InnerProductSpace.rankOne 𝕜
      (rightSingularBasis T ((Fin.castLEEmb (LinearMap.finrank_range_le T)) i))
      (rightSingularBasis T ((Fin.castLEEmb (LinearMap.finrank_range_le T)) i)))
        (rightSingularBasis T j)
  rw [orthonormalBasis_sum_rankOne_apply (rightSingularBasis T)
    (Fin.castLEEmb (LinearMap.finrank_range_le T)) j]
  have hiff : j.val < finrank 𝕜 T.range ↔
      ∃ i, (Fin.castLEEmb (LinearMap.finrank_range_le T)) i = j := by
    constructor
    · intro hj
      exact ⟨⟨j.val, hj⟩, Fin.ext rfl⟩
    · rintro ⟨i, hi⟩
      have hval := congrArg Fin.val hi.symm
      rw [hval]
      exact i.isLt
  by_cases hj : j.val < finrank 𝕜 T.range
  · rw [dite_eq_left hj, dite_eq_left (hiff.mp hj)]
  · rw [dite_eq_right hj, dite_eq_right (fun h => hj (hiff.mpr h))]

/-- 第三条 Penrose 方程：`TT⁺` 是对称算子。
@isnad1 id=issymmet.1h5v.s11.055cd2002fe3 from=translated src=- shape=7ceaf0ea vocab=17787d83
-/
theorem pseudoinverseWith_rangeProjection_symmetric (T : E →ₗ[𝕜] F)
    (b : OrthonormalBasis (Fin (finrank 𝕜 F)) 𝕜 F)
    (hb : ∀ i : Fin (finrank 𝕜 T.range),
      b (rangeIndexEmbedding T i) = leftSingularVector T i) :
    (T.comp (pseudoinverseWith T b)).IsSymmetric := by
  rw [pseudoinverseWith_rangeProjection_eq_sum_rankOne T b hb]
  exact (ContinuousLinearMap.isPositive_sum Finset.univ fun i hi =>
    InnerProductSpace.isPositive_rankOne_self _).toLinearMap.isSymmetric

/-- 第四条 Penrose 方程：`T⁺T` 是对称算子。
@isnad1 id=issymmet.1h5v.s11.11f63b73675a from=translated src=- shape=1f5a25d6 vocab=17787d83
-/
theorem pseudoinverseWith_kernelProjection_symmetric (T : E →ₗ[𝕜] F)
    (b : OrthonormalBasis (Fin (finrank 𝕜 F)) 𝕜 F)
    (hb : ∀ i : Fin (finrank 𝕜 T.range),
      b (rangeIndexEmbedding T i) = leftSingularVector T i) :
    ((pseudoinverseWith T b).comp T).IsSymmetric := by
  rw [pseudoinverseWith_kernelProjection_eq_sum_rankOne T b hb]
  exact (ContinuousLinearMap.isPositive_sum Finset.univ fun i hi =>
    InnerProductSpace.isPositive_rankOne_self _).toLinearMap.isSymmetric

/-- Moore–Penrose 伪逆证书：两个反身方程以及两个正交投影的对称性。-/
structure MoorePenrosePseudoinverse (T : E →ₗ[𝕜] F) where
  inverse : F →ₗ[𝕜] E
  penrose_one : T.comp (inverse.comp T) = T
  penrose_two : inverse.comp (T.comp inverse) = inverse
  rangeProjection_symmetric : (T.comp inverse).IsSymmetric
  kernelProjection_symmetric : (inverse.comp T).IsSymmetric

/-- 每个有限维实或复内积空间之间的线性映射都存在 Moore–Penrose 伪逆。
@isnad1 id=nonempty.0h4v.s7.da5a5f509dc6 from=translated src=- shape=739f8803 vocab=dd929702
-/
theorem exists_moorePenrosePseudoinverse (T : E →ₗ[𝕜] F) :
    Nonempty (MoorePenrosePseudoinverse T) := by
  obtain ⟨b, hb⟩ := exists_leftSingularBasis T
  exact ⟨{
    inverse := pseudoinverseWith T b
    penrose_one := pseudoinverseWith_penrose_one T b hb
    penrose_two := pseudoinverseWith_penrose_two T b hb
    rangeProjection_symmetric := pseudoinverseWith_rangeProjection_symmetric T b hb
    kernelProjection_symmetric := pseudoinverseWith_kernelProjection_symmetric T b hb }⟩

/-- `x₀` 是方程 `Tx = y` 的最小二乘解，若它使残差范数在所有候选向量中最小。
该定义只使用线性映射和范数，适合作为教材层公开接口。-/
def IsLeastSquaresSolution (T : E →ₗ[𝕜] F) (y : F) (x₀ : E) : Prop :=
  ∀ x, ‖T x₀ - y‖ ≤ ‖T x - y‖

omit [FiniteDimensional 𝕜 F] in
/-- 对称幂等算子 `P` 的像中，`Py` 是离 `y` 最近的向量。

证明把任意像中向量 `z` 的误差分解成
`z - y = (z - Py) + (Py - y)`。前一项仍在 `P` 的像中，后一项被 `P`
消去；对称性说明两项正交，因此结论由勾股恒等式得到。
@isnad1 id=le.3h5v.s9.9daae00e1dbb from=translated src=- shape=e7b10763 vocab=a8c9d3bf
-/
theorem symmetric_idempotent_residual_minimal (P : F →ₗ[𝕜] F)
    (hsym : P.IsSymmetric) (hidem : P.comp P = P)
    (y z : F) (hz : P z = z) :
    ‖P y - y‖ ≤ ‖z - y‖ := by
  let a := z - P y
  let r := P y - y
  have hPa : P a = a := by
    dsimp [a]
    have h := LinearMap.congr_fun hidem y
    have hPP : P (P y) = P y := by
      simpa only [LinearMap.comp_apply] using h
    rw [map_sub, hz, hPP]
  have hPr : P r = 0 := by
    dsimp [r]
    rw [map_sub]
    have h := LinearMap.congr_fun hidem y
    rw [show P (P y) = P y by simpa only [LinearMap.comp_apply] using h]
    simp
  have har : inner 𝕜 a r = 0 := by
    rw [← hPa, hsym, hPr, inner_zero_right]
  have hdecomp : z - y = a + r := by
    dsimp [a, r]
    abel
  have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero a r har
  rw [hdecomp]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [pow_two]
  rw [hpyth]
  exact le_add_of_nonneg_left (mul_self_nonneg ‖a‖)

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
/-- Moore–Penrose 伪逆给出的 `T⁺y` 是 `Tx = y` 的最小二乘解。
@isnad1 id=isleasts.0h6v.s8.9397e77a67d6 from=translated src=- shape=1d6cd8cf vocab=1692259a
-/
theorem MoorePenrosePseudoinverse.isLeastSquaresSolution
    {T : E →ₗ[𝕜] F} (G : MoorePenrosePseudoinverse T) (y : F) :
    IsLeastSquaresSolution T y (G.inverse y) := by
  intro x
  let P := T.comp G.inverse
  apply symmetric_idempotent_residual_minimal P
      G.rangeProjection_symmetric (y := y) (z := T x)
  · apply LinearMap.ext
    intro q
    change T (G.inverse (T (G.inverse q))) = T (G.inverse q)
    have h := LinearMap.congr_fun G.penrose_two q
    change G.inverse (T (G.inverse q)) = G.inverse q at h
    rw [h]
  · exact LinearMap.congr_fun G.penrose_one x

/-- 每个有限维最小二乘问题都有解；一个规范选择是 Moore–Penrose 解 `T⁺y`。
@isnad1 id=ex.0h5v.s7.92b4a3be9f2b from=translated src=- shape=2cac59f7 vocab=594d5264
-/
theorem exists_leastSquaresSolution (T : E →ₗ[𝕜] F) (y : F) :
    ∃ x₀, IsLeastSquaresSolution T y x₀ := by
  obtain ⟨G⟩ := exists_moorePenrosePseudoinverse T
  exact ⟨G.inverse y, G.isLeastSquaresSolution y⟩

end SandronesLibrary.LinearAlgebra.MatrixDecomposition
