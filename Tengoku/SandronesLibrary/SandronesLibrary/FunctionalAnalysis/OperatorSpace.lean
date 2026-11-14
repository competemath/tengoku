/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.FunctionalAnalysis.Operator
import Tengoku.Seed.Analysis.Normed.Operator.Banach

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 算子范数与算子空间的完备性

`ContinuousLinearMap` 自带的范数就是教材中的算子范数。本文件不重新用下确界定义同一个范数，而是
用全局估计和最小上界性质解释其教材含义，并说明当值域是 Banach 空间时，连续线性算子空间也是
Banach 空间。
-/

namespace SandronesLibrary.FunctionalAnalysis

open SandronesLibrary.Topology.NormedSpace

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [NormedLinearSpace ℝ E] [NormedLinearSpace ℝ F]

/-- 算子范数与所有范数一样非负。

> **Entry**: functional-analysis.operator.space-/
theorem operatorNorm_nonneg (T : E →L[ℝ] F) : 0 ≤ ‖T‖ := by
  exact norm_nonneg T

/-- 算子范数控制每个输出：`‖T x‖ ≤ ‖T‖ · ‖x‖`。-/
theorem norm_apply_le_operatorNorm (T : E →L[ℝ] F) (x : E) :
    ‖T x‖ ≤ ‖T‖ * ‖x‖ := by
  exact T.le_opNorm x

/-- 若非负常数 `C` 已经能全局控制 `T`，那么算子范数不会大于 `C`。-/
theorem operatorNorm_le_of_bound (T : E →L[ℝ] F) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x : E, ‖T x‖ ≤ C * ‖x‖) : ‖T‖ ≤ C := by
  exact T.opNorm_le_bound hC hbound

/-- 算子范数的最小界刻画：它本身是一个全局放大界，并且不大于任何其他非负全局界。-/
theorem operatorNorm_is_least_bound (T : E →L[ℝ] F) :
    (∀ x : E, ‖T x‖ ≤ ‖T‖ * ‖x‖) ∧
      ∀ C : ℝ, 0 ≤ C → (∀ x : E, ‖T x‖ ≤ C * ‖x‖) → ‖T‖ ≤ C := by
  exact ⟨norm_apply_le_operatorNorm T, fun _ hC hbound ↦
    operatorNorm_le_of_bound T hC hbound⟩

/-- 若值域 `F` 是 Banach 空间，则从 `E` 到 `F` 的连续线性算子在算子范数下构成完备空间。-/
theorem continuousLinearMap_complete [BanachSpace F] : CompleteSpace (E →L[ℝ] F) := by
  infer_instance

end SandronesLibrary.FunctionalAnalysis
