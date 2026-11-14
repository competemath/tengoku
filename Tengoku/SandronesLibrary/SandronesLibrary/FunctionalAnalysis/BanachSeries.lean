/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.NormedSpace
import Tengoku.Seed.Analysis.Normed.Group.InfiniteSum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Banach 空间中的绝对可和级数

Mathlib 的 `Summable` 和 `HasSum` 已经准确表达教材中的级数收敛语义，因此本文件直接复用它们。
核心结论是：在 Banach 空间中，若各项范数组成的非负实数级数收敛，则原向量级数也收敛；随后给出
部分和趋于总和以及总和范数不超过各项范数之和两个常用推论。
-/

namespace SandronesLibrary.FunctionalAnalysis

open Filter Finset
open SandronesLibrary.Topology.NormedSpace

variable {E : Type*}
variable [NormedAddCommGroup E] [NormedLinearSpace ℝ E] [BanachSpace E]

/-- 在 Banach 空间中，绝对可和蕴含向量级数可和。

教材中的“范数级数收敛”直接写成 `Summable (fun n ↦ ‖f n‖)`；这里不再建立同义包装谓词。

> **Entry**: functional-analysis.series.summable-/
theorem summable_of_summable_norm {f : ℕ → E}
    (hf : Summable (fun n ↦ ‖f n‖)) : Summable f := by
  exact hf.of_norm

/-- 绝对可和时，前 `N` 项的普通部分和趋于 Mathlib 记号 `∑' n, f n` 表示的级数总和。-/
theorem tendsto_partialSums_tsum_of_summable_norm {f : ℕ → E}
    (hf : Summable (fun n ↦ ‖f n‖)) :
    Tendsto (fun N : ℕ ↦ ∑ n ∈ range N, f n) atTop (nhds (∑' n, f n)) := by
  exact (summable_of_summable_norm hf).hasSum.tendsto_sum_nat

/-- 绝对收敛向量级数的总和范数不超过各项范数之和，这是无穷级数版本的三角不等式。-/
theorem norm_tsum_le_tsum_norm_of_summable {f : ℕ → E}
    (hf : Summable (fun n ↦ ‖f n‖)) :
    ‖∑' n, f n‖ ≤ ∑' n, ‖f n‖ := by
  exact norm_tsum_le_tsum_norm hf

end SandronesLibrary.FunctionalAnalysis
