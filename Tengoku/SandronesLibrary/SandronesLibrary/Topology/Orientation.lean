/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.NormedSpace
import Tengoku.Seed.LinearAlgebra.Orientation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 有限维实向量空间的定向

定向区分一组坐标与其“镜像坐标”。在 `n` 维实向量空间中，一个定向可以理解为
所有有序基的两个等价类之一：行列式为正的换基留在同一类，行列式为负的换基进入
另一类。Mathlib 用非零顶次交替形式的正射线精确实现这一概念；本模块把该实现包装
成教材中常用的接口。

这里处理的是欧氏型空间的**线性定向**，足以表达多元积分和微分形式中的保向坐标
变换。一般流形的可定向性还需要定向图册以及坐标转换的局部相容条件，属于后续
拓扑与微分几何内容，不应混入这个基础层。

> **Entry**: topology.orientation.vector-space
-/

noncomputable section

namespace SandronesLibrary.Topology.Orientation

universe u

/-- `n` 维实向量空间的定向。索引 `Fin n` 记录顶次交替形式的次数。-/
abbrev VectorOrientation (E : Type u) [AddCommGroup E] [Module ℝ E] (n : ℕ) :=
  _root_.Orientation ℝ E (Fin n)

/-- 一个有序基诱导的定向。两个基诱导同一定向，当且仅当它们之间的换基行列式为正。-/
def orientationOfBasis {E : Type u} [AddCommGroup E] [Module ℝ E] {n : ℕ}
    (b : Module.Basis (Fin n) ℝ E) : VectorOrientation E n :=
  b.orientation

/-- 线性自同构保持给定定向。-/
def IsOrientationPreserving {E : Type u} [AddCommGroup E] [Module ℝ E] {n : ℕ}
    (o : VectorOrientation E n) (f : E ≃ₗ[ℝ] E) : Prop :=
  _root_.Orientation.map (Fin n) f o = o

/-- 线性自同构反转给定定向。-/
def IsOrientationReversing {E : Type u} [AddCommGroup E] [Module ℝ E] {n : ℕ}
    (o : VectorOrientation E n) (f : E ≃ₗ[ℝ] E) : Prop :=
  _root_.Orientation.map (Fin n) f o = -o

/-- 恒等线性同构保持任意定向。
@isnad1 id=isorient.0h3v.s5.d77055ed37c6 from=translated src=- shape=3e16b796 vocab=302752d7
-/
theorem isOrientationPreserving_refl {E : Type u} [AddCommGroup E] [Module ℝ E]
    {n : ℕ} (o : VectorOrientation E n) :
    IsOrientationPreserving o (LinearEquiv.refl ℝ E) := by
  simp [IsOrientationPreserving]

/-- 在维数匹配时，每个线性自同构或者保向，或者反向。
@isnad1 id=or.1h4v.s6.fa5fea4a3180 from=translated src=- shape=f83c667e vocab=7a5c496c
-/
theorem preserving_or_reversing {E : Type u} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] {n : ℕ} (o : VectorOrientation E n)
    (f : E ≃ₗ[ℝ] E) (hdim : n = Module.finrank ℝ E) :
    IsOrientationPreserving o f ∨ IsOrientationReversing o f := by
  exact _root_.Orientation.eq_or_eq_neg
    (_root_.Orientation.map (Fin n) f o) o (by simpa using hdim)

/-- **保向的行列式判据**：线性自同构保向，当且仅当其行列式为正。
@isnad1 id=iff.1h4v.s9.c43f609e203a from=translated src=- shape=551a323c vocab=57c11161
-/
theorem isOrientationPreserving_iff_det_pos
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {n : ℕ} (o : VectorOrientation E n)
    (f : E ≃ₗ[ℝ] E) (hdim : n = Module.finrank ℝ E) :
    IsOrientationPreserving o f ↔ 0 < LinearMap.det (f : E →ₗ[ℝ] E) := by
  exact _root_.Orientation.map_eq_iff_det_pos o f (by simpa using hdim)

/-- **反向的行列式判据**：线性自同构反向，当且仅当其行列式为负。
@isnad1 id=iff.1h4v.s9.f8f1c436cac5 from=translated src=- shape=1dd18c28 vocab=99d0298e
-/
theorem isOrientationReversing_iff_det_neg
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {n : ℕ} (o : VectorOrientation E n)
    (f : E ≃ₗ[ℝ] E) (hdim : n = Module.finrank ℝ E) :
    IsOrientationReversing o f ↔ LinearMap.det (f : E →ₗ[ℝ] E) < 0 := by
  exact _root_.Orientation.map_eq_neg_iff_det_neg o f (by simpa using hdim)

/-- 调整基的最后一个向量后，可以让任意基符合指定定向。
@isnad1 id=eq.0h4v.s6.702881860e3f from=translated src=- shape=aadeb4ca vocab=d512b448
-/
theorem adjustedBasis_has_orientation
    {E : Type u} [AddCommGroup E] [Module ℝ E] {n : ℕ} [NeZero n]
    (b : Module.Basis (Fin n) ℝ E) (o : VectorOrientation E n) :
    (b.adjustToOrientation o).orientation = o := by
  exact Module.Basis.orientation_adjustToOrientation b o

end SandronesLibrary.Topology.Orientation
