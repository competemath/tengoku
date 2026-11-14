/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.FunctionalAnalysis.WeakStarTopology
import Tengoku.Seed.Analysis.Normed.Operator.NormedSpace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 对偶算子

连续线性算子 `T : E →L F` 的对偶算子把 `f ∈ F*` 送到 `f ∘ T ∈ E*`。当前 Mathlib 没有
`ContinuousLinearMap.dualMap` 专名，但 `T.precomp ℝ` 已完整承载这张连续线性映射。本文件只建立
一个教材具名桥，不重建预复合实现。
-/

namespace SandronesLibrary.FunctionalAnalysis

variable {E F G : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- 连续线性算子的对偶算子，由 Mathlib 的连续预复合承载。

> **Entry**: functional-analysis.dual-operator.definition-/
noncomputable def dualOperator (T : E →L[ℝ] F) :
    StrongDual ℝ F →L[ℝ] StrongDual ℝ E :=
  T.precomp ℝ

/-- 对偶算子的元素化定义是 `(T' f)(x) = f(Tx)`。-/
@[simp]
theorem dualOperator_apply (T : E →L[ℝ] F) (f : StrongDual ℝ F) (x : E) :
    dualOperator T f x = f (T x) := by
  rfl

/-- 对偶算子在每个泛函上满足标准范数估计。-/
theorem norm_dualOperator_apply_le (T : E →L[ℝ] F) (f : StrongDual ℝ F) :
    ‖dualOperator T f‖ ≤ ‖T‖ * ‖f‖ := by
  simpa [dualOperator, mul_comm] using f.opNorm_comp_le T

/-- 对偶算子的算子范数不超过原算子范数。-/
theorem norm_dualOperator_le (T : E →L[ℝ] F) : ‖dualOperator T‖ ≤ ‖T‖ := by
  apply (dualOperator T).opNorm_le_bound (norm_nonneg T)
  intro f
  exact norm_dualOperator_apply_le T f

/-- 对偶算子将复合次序反转。-/
theorem dualOperator_comp (S : F →L[ℝ] G) (T : E →L[ℝ] F) :
    dualOperator (S.comp T) = (dualOperator T).comp (dualOperator S) := by
  ext f x
  rfl

/-- 恒等算子的对偶仍是恒等算子。-/
theorem dualOperator_id :
    dualOperator (ContinuousLinearMap.id ℝ E) = ContinuousLinearMap.id ℝ (StrongDual ℝ E) := by
  ext f x
  rfl

end SandronesLibrary.FunctionalAnalysis
