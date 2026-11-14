/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.NormedSpace
import Tengoku.Seed.Analysis.Normed.Operator.ContinuousLinearMap
import Tengoku.Seed.Analysis.Normed.Group.Hom

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 连续线性算子

Mathlib 的 `ContinuousLinearMap` 恰好携带教材所需的两部分数据：线性映射及其连续性证明，因此本
课程直接用它作为正式承载，不再复制一层包装结构。本文件通过全局范数界刻画连续性，解释“连续
线性算子”与教材中常说的“有界线性算子”为何是同一个概念。
-/

namespace SandronesLibrary.FunctionalAnalysis

open SandronesLibrary.Topology.NormedSpace

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [NormedLinearSpace ℝ E] [NormedLinearSpace ℝ F]

/-- 每个连续线性算子都存在一个非负常数 `C`，使所有向量都满足 `‖T x‖ ≤ C ‖x‖`。

这正是正式承载 `E →L[ℝ] F` 所对应的教材“有界性”。

> **Entry**: functional-analysis.operator.continuous-linear-map-/
theorem continuousLinearMap_exists_bound (T : E →L[ℝ] F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E, ‖T x‖ ≤ C * ‖x‖ := by
  exact ⟨‖T‖, norm_nonneg T, T.le_opNorm⟩

/-- 连续线性算子忘掉线性结构后，其底层函数仍然连续。-/
theorem continuousLinearMap_continuous (T : E →L[ℝ] F) : Continuous T := by
  exact T.continuous

/-- 零算子的输出范数恒为零，因此全局界可以取 `C = 0`；这是正式承载的最简单具体例子。-/
theorem continuousLinearMap_zero_bound :
    ∀ x : E, ‖(0 : E →L[ℝ] F) x‖ ≤ 0 * ‖x‖ := by
  intro x
  simp

/-- 实赋范空间之间的线性映射连续，当且仅当它存在非负的全局范数界。

正向由连续线性映射的算子范数给出界；反向则用该界把普通线性映射升级成连续线性映射。这就是
泛函分析中“线性算子连续”等价于“线性算子有界”的标准定理。

> **Entry**: functional-analysis.operator.bounded-iff-/
theorem linearMap_continuous_iff_exists_bound (T : E →ₗ[ℝ] F) :
    Continuous T ↔ ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E, ‖T x‖ ≤ C * ‖x‖ := by
  constructor
  · intro hT
    let L : E →L[ℝ] F := ⟨T, hT⟩
    exact ⟨‖L‖, norm_nonneg L, fun x ↦ by simpa [L] using L.le_opNorm x⟩
  · rintro ⟨C, -, hbound⟩
    change Continuous (fun x ↦ T x)
    exact (T.mkContinuous C hbound).continuous

end SandronesLibrary.FunctionalAnalysis
