/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.FunctionalAnalysis.WeakStarTopology
import Tengoku.Seed.Analysis.Normed.Module.WeakDual

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Banach–Alaoglu 定理

连续对偶的范数闭球在弱星拓扑下紧致。正式集合必须写在 `WeakDual ℝ E` 中；
`WeakDual.toStrongDual` 只用于读取同一泛函的范数。
-/

namespace SandronesLibrary.FunctionalAnalysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- 对偶范数闭球在弱星拓扑下是闭集。

> **Entry**: functional-analysis.banach-alaoglu-/
theorem weakStar_isClosed_closedBall (f : StrongDual ℝ E) (r : ℝ) :
    IsClosed (WeakDual.toStrongDual ⁻¹' Metric.closedBall f r) := by
  exact WeakDual.isClosed_closedBall f r

/-- Banach–Alaoglu：对偶范数闭球在弱星拓扑下紧致。-/
theorem weakStar_isCompact_closedBall (f : StrongDual ℝ E) (r : ℝ) :
    IsCompact (WeakDual.toStrongDual ⁻¹' Metric.closedBall f r) := by
  exact WeakDual.isCompact_closedBall f r

/-- Banach–Alaoglu 的闭单位球形式。-/
theorem weakStar_isCompact_unitBall :
    IsCompact (WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ E) 1) := by
  exact weakStar_isCompact_closedBall 0 1

end SandronesLibrary.FunctionalAnalysis
