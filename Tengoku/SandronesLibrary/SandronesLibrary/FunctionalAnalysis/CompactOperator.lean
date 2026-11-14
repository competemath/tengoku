/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.FunctionalAnalysis.OperatorSpace
import Tengoku.Seed.Analysis.Normed.Operator.Compact.FiniteDimension

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 紧算子

本文件直接采用 Mathlib 的谓词 `IsCompactOperator`，并把它与单位球像相对紧的教材定义对齐。
紧算子仍由普通连续线性映射承载，不建立平行包装类型。
-/

namespace SandronesLibrary.FunctionalAnalysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- 连续线性映射紧，当且仅当开单位球像的闭包紧。

> **Entry**: functional-analysis.compact-operator.definition-/
theorem compactOperator_iff_isCompact_closure_image_unitBall (T : E →L[ℝ] F) :
    IsCompactOperator T ↔
      IsCompact (closure (T '' Metric.ball (0 : E) 1)) := by
  exact isCompactOperator_iff_isCompact_closure_image_ball T.toLinearMap zero_lt_one

/-- 零算子是紧算子。-/
theorem zero_isCompactOperator : IsCompactOperator (0 : E →L[ℝ] F) := by
  exact isCompactOperator_zero

/-- 值域有限维的连续线性映射是紧算子。-/
theorem isCompactOperator_of_finiteDimensional_codomain [FiniteDimensional ℝ F]
    (T : E →L[ℝ] F) : IsCompactOperator T := by
  exact isCompactOperator_of_locallyCompactSpace_dom T

/-- 定义域有限维的连续线性映射是紧算子。-/
theorem isCompactOperator_of_finiteDimensional_domain [FiniteDimensional ℝ E]
    (T : E →L[ℝ] F) : IsCompactOperator T := by
  exact isCompactOperator_of_locallyCompactSpace_rng T

/-- 恒等算子紧当且仅当空间有限维。-/
theorem identity_isCompactOperator_iff_finiteDimensional :
    IsCompactOperator (ContinuousLinearMap.id ℝ E) ↔ FiniteDimensional ℝ E := by
  change IsCompactOperator (id : E → E) ↔ FiniteDimensional ℝ E
  exact isCompactOperator_id_iff_finiteDimensional

end SandronesLibrary.FunctionalAnalysis
