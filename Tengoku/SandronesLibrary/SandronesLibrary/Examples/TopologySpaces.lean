/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.Closure
import Tengoku.Seed.Topology.Order.DenselyOrdered

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Examples / 拓扑空间：内部、闭包与边界的实直线计算例

本文件为 Wave E3 新登记条目 `topology.space.closure`（内部、闭包与边界）补齐实直线上的
具体计算例：开区间闭包、闭区间内部、开区间边界，以及“开集不必闭、闭集不必开”的
精确反例。

> **Entry**: examples.topology.spaces
-/

noncomputable section

namespace SandronesLibrary.Examples.TopologySpaces

open Set

/-- **开区间的闭包**：`closure (Ioo 0 1) = Icc 0 1`。
@isnad1 id=eq.0h0v.s5.aec5a9f624ca from=translated src=- shape=4c49f5ac vocab=c5397a8e
-/
theorem closure_Ioo_zero_one : closure (Ioo (0 : ℝ) 1) = Icc 0 1 :=
  closure_Ioo (by norm_num)

/-- **闭区间的内部**：`interior (Icc 0 1) = Ioo 0 1`。
@isnad1 id=eq.0h0v.s5.b39ec7186fbf from=translated src=- shape=4c49f5ac vocab=c6dc69fb
-/
theorem interior_Icc_zero_one : interior (Icc (0 : ℝ) 1) = Ioo 0 1 :=
  interior_Icc

/-- **开区间的边界**：`frontier (Ioo 0 1) = {0, 1}`。
@isnad1 id=eq.0h0v.s5.05f506168419 from=translated src=- shape=632fb896 vocab=9988d6e3
-/
theorem frontier_Ioo_zero_one : frontier (Ioo (0 : ℝ) 1) = ({0, 1} : Set ℝ) :=
  frontier_Ioo (by norm_num)

/-- **反例：开集不必闭**。`Ioo 0 1` 的闭包严格大于自身：端点 `1` 落在闭包中但不落在
原集合中。这否定了“开区间等于自己的闭包（即开集闭）”的误认。
@isnad1 id=ne.0h0v.s5.0a239e8ad691 from=translated src=- shape=77c27088 vocab=10f16f74
-/
theorem closure_Ioo_ne_self : closure (Ioo (0 : ℝ) 1) ≠ Ioo 0 1 := by
  intro h
  have hmem : (1 : ℝ) ∈ closure (Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo_zero_one]
    exact right_mem_Icc.mpr (by norm_num)
  rw [h] at hmem
  exact (lt_irrefl (1 : ℝ)) hmem.2

/-- **反例：闭集不必开**。`Icc 0 1` 的内部严格小于自身：端点 `0` 落在原集合中但不落在
内部。这否定了“闭区间等于自己的内部（即闭集开）”的误认。
@isnad1 id=ne.0h0v.s5.14c356f48210 from=translated src=- shape=77c27088 vocab=2e4f136a
-/
theorem interior_Icc_ne_self : interior (Icc (0 : ℝ) 1) ≠ Icc 0 1 := by
  intro h
  have hmem : (0 : ℝ) ∈ interior (Icc (0 : ℝ) 1) := by
    rw [h]
    exact left_mem_Icc.mpr (by norm_num)
  rw [interior_Icc_zero_one] at hmem
  exact (lt_irrefl (0 : ℝ)) hmem.1

end SandronesLibrary.Examples.TopologySpaces
