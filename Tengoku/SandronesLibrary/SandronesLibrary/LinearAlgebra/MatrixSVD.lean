/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.LinearAlgebra.MatrixSchur
import Tengoku.Seed.Analysis.InnerProductSpace.SingularValues

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# LinearAlgebra / MatrixSVD —— 奇异值分解

本文件对有限维实或复内积空间之间的线性映射建立完整 SVD。右奇异向量取自正算子
`T†T` 的有序正交特征基；正奇异值对应的像向量除以奇异值得到正交归一的左奇异
向量族，再将其扩充为值域空间的正交基。排在秩之后的右奇异向量属于 `T` 的核。

> **Entry**: linear-algebra.decomposition.svd
-/

namespace SandronesLibrary.LinearAlgebra.MatrixDecomposition

open Module

universe u v

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
  {F : Type v} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-- 有限维线性映射的诱导算子范数。公开接口保持在线性代数的 `LinearMap` 层；
连续线性映射只用于复用底层范数实现。-/
noncomputable def operatorNorm (T : E →ₗ[𝕜] F) : ℝ :=
  ‖T.toContinuousLinearMap‖

/-- 有限维线性映射的算子范数非负。
@isnad1 id=le.0h4v.s7.d2979a415e68 from=translated src=- shape=47639602 vocab=ace2c342
-/
theorem operatorNorm_nonneg (T : E →ₗ[𝕜] F) : 0 ≤ operatorNorm T := by
  exact ContinuousLinearMap.opNorm_nonneg _

/-- 算子范数控制每个向量的像的范数。
@isnad1 id=le.0h5v.s8.a22ab83a5880 from=translated src=- shape=154ed9c4 vocab=b9255314
-/
theorem norm_apply_le_operatorNorm_mul_norm (T : E →ₗ[𝕜] F) (x : E) :
    ‖T x‖ ≤ operatorNorm T * ‖x‖ := by
  exact T.toContinuousLinearMap.le_opNorm x

/-- 算子范数为零，当且仅当线性映射为零。
@isnad1 id=iff.0h4v.s9.3ff60ac6b6d7 from=translated src=- shape=1bd8bc59 vocab=b37516fe
-/
theorem operatorNorm_eq_zero_iff (T : E →ₗ[𝕜] F) : operatorNorm T = 0 ↔ T = 0 := by
  rw [operatorNorm, norm_eq_zero]
  constructor
  · intro h
    apply LinearMap.ext
    intro x
    exact DFunLike.congr_fun h x
  · intro h
    subst T
    rfl

/-- 有限维线性映射的算子范数对复合满足次乘性。
@isnad1 id=le.0h6v.s9.a6efffe5d389 from=translated src=- shape=e3383144 vocab=d0a6d081
-/
theorem operatorNorm_comp_le
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    (S : F →ₗ[𝕜] G) (T : E →ₗ[𝕜] F) :
    operatorNorm (S.comp T) ≤ operatorNorm S * operatorNorm T := by
  change ‖(S.comp T).toContinuousLinearMap‖ ≤
    ‖S.toContinuousLinearMap‖ * ‖T.toContinuousLinearMap‖
  have hcomp : (S.comp T).toContinuousLinearMap =
      S.toContinuousLinearMap.comp T.toContinuousLinearMap := by
    ext x
    rfl
  rw [hcomp]
  exact ContinuousLinearMap.opNorm_comp_le _ _

/-- 正算子的最大特征值不超过算子范数。

取最大特征值对应的单位特征向量，将算子范数的逐点估计应用于该向量即可。
@isnad1 id=le.2h3v.s8.a3ff2082f681 from=translated src=- shape=8fa317dd vocab=8e03c84c
-/
theorem first_eigenvalue_le_operatorNorm
    (S : E →ₗ[𝕜] E) (hS : S.IsPositive)
    (hE : 0 < finrank 𝕜 E) :
    hS.isSymmetric.eigenvalues rfl ⟨0, hE⟩ ≤ operatorNorm S := by
  let i : Fin (finrank 𝕜 E) := ⟨0, hE⟩
  let v := hS.isSymmetric.eigenvectorBasis rfl i
  have hbound := norm_apply_le_operatorNorm_mul_norm S v
  rw [hS.isSymmetric.apply_eigenvectorBasis rfl i,
    norm_smul, OrthonormalBasis.norm_eq_one, mul_one, mul_one] at hbound
  simpa [Real.norm_eq_abs, abs_of_nonneg (hS.nonneg_eigenvalues rfl i)] using hbound

/-- 正算子的算子范数不超过其最大特征值。

在按特征值降序排列的正交特征基中，正算子逐坐标乘以非负特征值；每个特征值都
不超过第一个特征值。对各坐标模长的平方求和便得到所需范数估计。
@isnad1 id=le.2h3v.s8.8f18b736349f from=translated src=- shape=503c751d vocab=8e03c84c
-/
theorem operatorNorm_le_first_eigenvalue
    (S : E →ₗ[𝕜] E) (hS : S.IsPositive)
    (hE : 0 < finrank 𝕜 E) :
    operatorNorm S ≤ hS.isSymmetric.eigenvalues rfl ⟨0, hE⟩ := by
  let i0 : Fin (finrank 𝕜 E) := ⟨0, hE⟩
  let b := hS.isSymmetric.eigenvectorBasis rfl
  let μ := hS.isSymmetric.eigenvalues rfl i0
  have hμ : 0 ≤ μ := hS.nonneg_eigenvalues rfl i0
  change ‖S.toContinuousLinearMap‖ ≤ μ
  refine ContinuousLinearMap.opNorm_le_bound _ hμ fun x => ?_
  rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg hμ (norm_nonneg _))]
  change ‖S x‖ ^ 2 ≤ (μ * ‖x‖) ^ 2
  rw [← b.repr.norm_map (S x), ← b.repr.norm_map x, mul_pow,
    EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hi0 : i0 ≤ i := by
    exact Fin.mk_le_mk.mpr (Nat.zero_le _)
  have hμi : hS.isSymmetric.eigenvalues rfl i ≤ μ :=
    hS.isSymmetric.eigenvalues_antitone rfl hi0
  have hμi0 : 0 ≤ hS.isSymmetric.eigenvalues rfl i :=
    hS.nonneg_eigenvalues rfl i
  rw [hS.isSymmetric.eigenvectorBasis_apply_self_apply rfl x i,
    norm_mul, RCLike.norm_ofReal, abs_of_nonneg hμi0]
  change (_ * ‖b.repr x i‖) ^ 2 ≤ μ ^ 2 * ‖b.repr x i‖ ^ 2
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right
    ((sq_le_sq₀ hμi0 hμ).mpr hμi) (sq_nonneg ‖b.repr x i‖)

/-- 正算子的算子范数等于其按降序排列的第一个特征值。
@isnad1 id=eq.2h3v.s8.290b9029d7f8 from=translated src=- shape=503c751d vocab=4fb49e9a
-/
theorem operatorNorm_positive_eq_first_eigenvalue
    (S : E →ₗ[𝕜] E) (hS : S.IsPositive)
    (hE : 0 < finrank 𝕜 E) :
    operatorNorm S = hS.isSymmetric.eigenvalues rfl ⟨0, hE⟩ := by
  exact le_antisymm (operatorNorm_le_first_eigenvalue S hS hE)
    (first_eigenvalue_le_operatorNorm S hS hE)

/-- 正维定义域上，线性映射的算子范数等于第一奇异值。
@isnad1 id=eq.1h4v.s8.6ecb29ef4952 from=translated src=- shape=1687c199 vocab=26acf2bc
-/
theorem operatorNorm_eq_first_singularValue_of_pos_finrank (T : E →ₗ[𝕜] F)
    (hE : 0 < finrank 𝕜 E) :
    operatorNorm T = T.singularValues 0 := by
  have hself := operatorNorm_positive_eq_first_eigenvalue
    (T.adjoint.comp T) T.isPositive_adjoint_comp_self hE
  have hnormsq : operatorNorm (T.adjoint.comp T) = operatorNorm T * operatorNorm T := by
    letI := FiniteDimensional.complete 𝕜 E
    letI := FiniteDimensional.complete 𝕜 F
    exact ContinuousLinearMap.norm_adjoint_comp_self T.toContinuousLinearMap
  have hσsq : T.singularValues 0 ^ 2 =
      T.isSymmetric_adjoint_comp_self.eigenvalues rfl ⟨0, hE⟩ :=
    T.sq_singularValues_of_lt rfl hE
  apply sq_eq_sq₀ (operatorNorm_nonneg T) (T.singularValues_nonneg 0) |>.mp
  rw [sq]
  exact hnormsq.symm.trans (hself.trans hσsq.symm)

/-- 任意有限维线性映射的算子范数等于第一奇异值。

若定义域维数为正，这就是正算子 `T†T` 的最大特征值公式；零维时定义域只有零向量，
因而映射及其全部奇异值均为零。
@isnad1 id=eq.0h4v.s7.cc54e9bd3627 from=translated src=- shape=8e2594af vocab=caafb999
-/
theorem operatorNorm_eq_first_singularValue (T : E →ₗ[𝕜] F) :
    operatorNorm T = T.singularValues 0 := by
  by_cases hE : 0 < finrank 𝕜 E
  · exact operatorNorm_eq_first_singularValue_of_pos_finrank T hE
  · have hzero : finrank 𝕜 E = 0 := Nat.eq_zero_of_not_pos hE
    letI : Subsingleton E := Module.finrank_zero_iff.mp hzero
    have hT : T = 0 := by
      ext x
      have hx : x = 0 := Subsingleton.elim _ _
      subst x
      simp
    subst T
    have hop : operatorNorm (0 : E →ₗ[𝕜] F) = 0 :=
      (operatorNorm_eq_zero_iff _).mpr rfl
    rw [hop, LinearMap.singularValues_zero]
    rfl

/-- `T†T` 的有序特征基，即 SVD 的右奇异向量基。-/
noncomputable def rightSingularBasis (T : E →ₗ[𝕜] F) :
    OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E :=
  T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl

/-- 第 `i` 个正奇异值对应的归一化左奇异向量。-/
noncomputable def leftSingularVector (T : E →ₗ[𝕜] F)
    (i : Fin (finrank 𝕜 T.range)) : F :=
  ((T.singularValues i : 𝕜)⁻¹) •
    T (rightSingularBasis T (Fin.castLE (LinearMap.finrank_range_le T) i))

/-- 正奇异值对应的左右奇异向量满足 `T vᵢ = σᵢ uᵢ`。
@isnad1 id=eq.0h5v.s11.b006cc9f6d7b from=translated src=- shape=21adda6c vocab=ffe80e74
-/
theorem map_rightSingularBasis_eq_smul_leftSingularVector (T : E →ₗ[𝕜] F)
    (i : Fin (finrank 𝕜 T.range)) :
    T (rightSingularBasis T (Fin.castLE (LinearMap.finrank_range_le T) i)) =
      (T.singularValues i : 𝕜) • leftSingularVector T i := by
  have hσ : T.singularValues i ≠ 0 := ne_of_gt <|
    T.singularValues_pos_iff_lt_finrank_range.mpr i.isLt
  simp [leftSingularVector, smul_smul, hσ]

/-- 归一化后的正奇异向量族在值域中正交归一。
@isnad1 id=orthonor.0h4v.s9.b689b6569868 from=translated src=- shape=ff056566 vocab=3199f369
-/
theorem orthonormal_leftSingularVector (T : E →ₗ[𝕜] F) :
    Orthonormal 𝕜 (leftSingularVector T) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  let ii : Fin (finrank 𝕜 E) := Fin.castLE (LinearMap.finrank_range_le T) i
  let jj : Fin (finrank 𝕜 E) := Fin.castLE (LinearMap.finrank_range_le T) j
  let v := rightSingularBasis T
  have heig := T.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis rfl jj
  have heig' : T.adjoint (T (v jj)) =
      (T.isSymmetric_adjoint_comp_self.eigenvalues rfl jj : 𝕜) • v jj := by
    change T.adjoint (T
      (T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl jj)) = _ at heig
    change T.adjoint (T
      (T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl jj)) = _
    exact heig
  have hsq : T.isSymmetric_adjoint_comp_self.eigenvalues rfl jj =
      T.singularValues j ^ 2 := by
    rw [← T.sq_singularValues_fin rfl jj]
    rfl
  have hvinner : inner 𝕜 (v ii) (v jj) = if i = j then 1 else 0 := by
    simpa [ii, jj] using (orthonormal_iff_ite.mp v.orthonormal ii jj)
  have hinner : inner 𝕜 (T (v ii)) (T (v jj)) =
      (T.singularValues j : 𝕜) ^ 2 * (if i = j then 1 else 0) := by
    calc
      _ = inner 𝕜 (v ii) (T.adjoint (T (v jj))) :=
        (T.adjoint_inner_right (v ii) (T (v jj))).symm
      _ = inner 𝕜 (v ii)
          ((T.isSymmetric_adjoint_comp_self.eigenvalues rfl jj : 𝕜) • v jj) := by
        rw [heig']
      _ = _ := by rw [inner_smul_right, hsq, hvinner]; norm_cast
  have hσi : T.singularValues i ≠ 0 := ne_of_gt <|
    T.singularValues_pos_iff_lt_finrank_range.mpr i.isLt
  have hσj : T.singularValues j ≠ 0 := ne_of_gt <|
    T.singularValues_pos_iff_lt_finrank_range.mpr j.isLt
  simp only [leftSingularVector, inner_smul_left, inner_smul_right]
  rw [hinner]
  by_cases hij : i = j
  · subst j
    simp only [ite_eq_left]
    have hσiK : (T.singularValues i : 𝕜) ≠ 0 := by exact_mod_cast hσi
    have hstar : (starRingEnd 𝕜) (T.singularValues i : 𝕜) =
        (T.singularValues i : 𝕜) := by simp
    rw [map_inv₀, hstar]
    field_simp
  · simp [hij]

/-- 将非零奇异值的秩索引按原序嵌入值域基索引。-/
noncomputable def rangeIndexEmbedding (T : E →ₗ[𝕜] F) :
    Fin (finrank 𝕜 T.range) ↪ Fin (finrank 𝕜 F) :=
  Fin.castLEEmb (Submodule.finrank_le T.range)

/-- 正左奇异向量可扩充为整个值域空间的一组正交归一基。
@isnad1 id=ex.0h4v.s11.a11af32777aa from=translated src=- shape=e155b621 vocab=f1978863
-/
theorem exists_leftSingularBasis (T : E →ₗ[𝕜] F) :
    ∃ b : OrthonormalBasis (Fin (finrank 𝕜 F)) 𝕜 F,
      ∀ i : Fin (finrank 𝕜 T.range),
        b (rangeIndexEmbedding T i) = leftSingularVector T i := by
  classical
  let r := finrank 𝕜 T.range
  let m := finrank 𝕜 F
  let s : Set (Fin m) := {i | i.val < r}
  let w : Fin m → F := fun i => if h : i.val < r then
    leftSingularVector T ⟨i.val, h⟩ else 0
  have hw : Orthonormal 𝕜 (s.domRestrict w) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hi : i.val.val < r := i.property
    have hj : j.val.val < r := j.property
    have horth := orthonormal_iff_ite.mp (orthonormal_leftSingularVector T)
      (⟨i.val.val, hi⟩ : Fin r) (⟨j.val.val, hj⟩ : Fin r)
    simpa [Set.domRestrict, w, hi, hj, Fin.ext_iff, Subtype.ext_iff] using horth
  obtain ⟨b, hb⟩ := hw.exists_orthonormalBasis_extension_of_card_eq (by simp [m])
  refine ⟨b, fun i => ?_⟩
  have hi : (rangeIndexEmbedding T i).val < r := i.isLt
  rw [hb (rangeIndexEmbedding T i) hi]
  change (if h : i.val < r then leftSingularVector T ⟨i.val, h⟩ else 0) = _
  rw [dite_eq_left i.isLt]

/-- 排在秩之后的右奇异向量属于核。
@isnad1 id=eq.1h5v.s10.d2351f69d4ac from=translated src=- shape=558d5bfd vocab=b97ad557
-/
theorem map_rightSingularBasis_eq_zero_of_finrank_range_le
    (T : E →ₗ[𝕜] F) (i : Fin (finrank 𝕜 E))
    (hi : finrank 𝕜 T.range ≤ i.val) :
    T (rightSingularBasis T i) = 0 := by
  have hσ : T.singularValues i = 0 :=
    T.singularValues_eq_zero_iff_le_finrank_range.mpr hi
  have heig := T.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis rfl i
  have hsq := T.sq_singularValues_fin rfl i
  have hcomp : (T.adjoint ∘ₗ T) (rightSingularBasis T i) = 0 := by
    change (T.adjoint ∘ₗ T)
      (T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl i) = 0
    rw [heig, ← hsq, hσ]
    simp
  have hmem : rightSingularBasis T i ∈ (T.adjoint ∘ₗ T).ker :=
    LinearMap.mem_ker.mpr hcomp
  rw [T.ker_adjoint_comp_self] at hmem
  exact LinearMap.mem_ker.mp hmem

/-- 线性映射的完整 SVD 证书；正奇异值部分成对，剩余右奇异向量落在核中。-/
structure SingularValueDecomposition (T : E →ₗ[𝕜] F) where
  rightBasis : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E
  leftBasis : OrthonormalBasis (Fin (finrank 𝕜 F)) 𝕜 F
  map_right : ∀ i : Fin (finrank 𝕜 E),
    if hi : i.val < finrank 𝕜 T.range then
      T (rightBasis i) = (T.singularValues i : 𝕜) •
        leftBasis (rangeIndexEmbedding T ⟨i.val, hi⟩)
    else T (rightBasis i) = 0

/-- 任意有限维实或复内积空间之间的线性映射都有 SVD。
@isnad1 id=nonempty.0h4v.s7.21e6af275ca9 from=translated src=- shape=739f8803 vocab=a82bd993
-/
theorem exists_singularValueDecomposition (T : E →ₗ[𝕜] F) :
    Nonempty (SingularValueDecomposition T) := by
  obtain ⟨u, hu⟩ := exists_leftSingularBasis T
  refine ⟨{
    rightBasis := rightSingularBasis T
    leftBasis := u
    map_right := fun i => ?_ }⟩
  split_ifs with hi
  · let k : Fin (finrank 𝕜 T.range) := ⟨i.val, hi⟩
    have hmap := map_rightSingularBasis_eq_smul_leftSingularVector T k
    rw [← hu k] at hmap
    exact hmap
  · exact map_rightSingularBasis_eq_zero_of_finrank_range_le T i (Nat.le_of_not_gt hi)

/-- SVD 的矩形对角矩阵：仅前 `rank T` 个对角元为正奇异值。-/
noncomputable def singularDiagonal (T : E →ₗ[𝕜] F) :
    Matrix (Fin (finrank 𝕜 F)) (Fin (finrank 𝕜 E)) 𝕜 := fun i j =>
  if _hj : j.val < finrank 𝕜 T.range then
    if i.val = j.val then (T.singularValues j : 𝕜) else 0
  else 0

/-- SVD 证书给出的左右奇异基下，`T` 的矩阵就是矩形奇异值对角矩阵。
@isnad1 id=eq.0h5v.s11.cae9275ec8d7 from=translated src=- shape=a9900896 vocab=65034302
-/
theorem SingularValueDecomposition.toMatrix_eq_singularDiagonal
    {T : E →ₗ[𝕜] F} (d : SingularValueDecomposition T) :
    LinearMap.toMatrix d.rightBasis.toBasis d.leftBasis.toBasis T =
      singularDiagonal T := by
  classical
  ext i j
  by_cases hj : j.val < finrank 𝕜 T.range
  · have hmap := d.map_right j
    rw [dite_eq_left hj] at hmap
    rw [LinearMap.toMatrix_apply]
    change (d.leftBasis.toBasis.repr (T (d.rightBasis j))) i = _
    rw [hmap]
    simp [singularDiagonal, hj, rangeIndexEmbedding, Fin.ext_iff, Algebra.smul_def]
  · have hmap := d.map_right j
    rw [dite_eq_right hj] at hmap
    rw [LinearMap.toMatrix_apply]
    change (d.leftBasis.toBasis.repr (T (d.rightBasis j))) i = _
    rw [hmap]
    simp [singularDiagonal, hj]

/-- 标准坐标下的左奇异向量换基矩阵。-/
noncomputable def SingularValueDecomposition.leftMatrix
    {T : E →ₗ[𝕜] F} (d : SingularValueDecomposition T) :
    Matrix (Fin (finrank 𝕜 F)) (Fin (finrank 𝕜 F)) 𝕜 :=
  (stdOrthonormalBasis 𝕜 F).toBasis.toMatrix d.leftBasis.toBasis

/-- 标准坐标下的右奇异向量换基矩阵。-/
noncomputable def SingularValueDecomposition.rightMatrix
    {T : E →ₗ[𝕜] F} (d : SingularValueDecomposition T) :
    Matrix (Fin (finrank 𝕜 E)) (Fin (finrank 𝕜 E)) 𝕜 :=
  (stdOrthonormalBasis 𝕜 E).toBasis.toMatrix d.rightBasis.toBasis

/-- 左换基矩阵为酉矩阵。
@isnad1 id=mem.0h5v.s10.037f7a48d97d from=translated src=- shape=a47ebb6b vocab=2ac28b56
-/
theorem SingularValueDecomposition.leftMatrix_unitary
    {T : E →ₗ[𝕜] F} (d : SingularValueDecomposition T) :
    d.leftMatrix ∈ Matrix.unitaryGroup (Fin (finrank 𝕜 F)) 𝕜 := by
  exact (stdOrthonormalBasis 𝕜 F).toMatrix_orthonormalBasis_mem_unitary d.leftBasis

/-- 右换基矩阵为酉矩阵。
@isnad1 id=mem.0h5v.s10.766a2377d158 from=translated src=- shape=532b6933 vocab=76c51625
-/
theorem SingularValueDecomposition.rightMatrix_unitary
    {T : E →ₗ[𝕜] F} (d : SingularValueDecomposition T) :
    d.rightMatrix ∈ Matrix.unitaryGroup (Fin (finrank 𝕜 E)) 𝕜 := by
  exact (stdOrthonormalBasis 𝕜 E).toMatrix_orthonormalBasis_mem_unitary d.rightBasis

/-- 右奇异基的逆换基矩阵是右换基矩阵的共轭转置。
@isnad1 id=eq.0h5v.s9.ddf9c3567240 from=translated src=- shape=86c0d4de vocab=28e82d83
-/
theorem SingularValueDecomposition.rightBasis_toMatrix_standard_eq_conjTranspose
    {T : E →ₗ[𝕜] F} (d : SingularValueDecomposition T) :
    d.rightBasis.toBasis.toMatrix (stdOrthonormalBasis 𝕜 E).toBasis =
      Matrix.conjTranspose d.rightMatrix := by
  classical
  ext i j
  simp [SingularValueDecomposition.rightMatrix, Basis.toMatrix_apply,
    OrthonormalBasis.repr_apply_apply, inner_conj_symm]

/-- 标准正交基下的矩阵满足经典乘积形式 `U Σ Vᴴ`。
@isnad1 id=eq.0h5v.s12.36990a4167ef from=translated src=- shape=67807eea vocab=dc113712
-/
theorem SingularValueDecomposition.standardMatrix_eq_mul_singularDiagonal_mul_conjTranspose
    {T : E →ₗ[𝕜] F} (d : SingularValueDecomposition T) :
    LinearMap.toMatrix (stdOrthonormalBasis 𝕜 E).toBasis
        (stdOrthonormalBasis 𝕜 F).toBasis T =
      d.leftMatrix * singularDiagonal T * Matrix.conjTranspose d.rightMatrix := by
  rw [← d.rightBasis_toMatrix_standard_eq_conjTranspose,
    ← d.toMatrix_eq_singularDiagonal]
  exact (basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
    (stdOrthonormalBasis 𝕜 E).toBasis d.rightBasis.toBasis
    (stdOrthonormalBasis 𝕜 F).toBasis d.leftBasis.toBasis T).symm

/-- 任意矩形实或复矩阵（视作坐标线性映射）都有 SVD。
@isnad1 id=nonempty.0h4v.s12.35721ec67025 from=translated src=- shape=973f1700 vocab=2f63a792
-/
theorem exists_matrixSingularValueDecomposition
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m n 𝕜) :
    Nonempty (SingularValueDecomposition (Matrix.toEuclideanLin A)) := by
  exact exists_singularValueDecomposition (Matrix.toEuclideanLin A)

/-- 非零奇异值的个数等于映射的秩。
@isnad1 id=eq.0h4v.s9.54722a84b02d from=translated src=- shape=f01a0f8c vocab=12ba4890
-/
theorem card_support_singularValues_eq_rank (T : E →ₗ[𝕜] F) :
    T.singularValues.support.card = finrank 𝕜 T.range := by
  exact T.card_support_singularValues

/-- 第 `i` 个奇异值为正，当且仅当 `i` 小于映射的秩。
@isnad1 id=iff.0h5v.s9.d6e5e968e5c3 from=translated src=- shape=51824123 vocab=cbedc602
-/
theorem singularValue_pos_iff_lt_rank (T : E →ₗ[𝕜] F) (i : ℕ) :
    0 < T.singularValues i ↔ i < finrank 𝕜 T.range := by
  exact T.singularValues_pos_iff_lt_finrank_range

/-- 映射单射，当且仅当其定义域维数范围内的奇异值全部严格为正。
@isnad1 id=iff.0h4v.s8.b6789779bb3c from=translated src=- shape=8f3967c5 vocab=e9e204c2
-/
theorem injective_iff_singularValues_pos (T : E →ₗ[𝕜] F) :
    Function.Injective T ↔ ∀ i < finrank 𝕜 E, 0 < T.singularValues i := by
  exact T.injective_iff_forall_lt_finrank_singularValues_pos

end SandronesLibrary.LinearAlgebra.MatrixDecomposition
