/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.NormedSpace
import Tengoku.Seed.Analysis.Normed.Group.Quotient

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 闭子空间的商空间

线性子空间直接用 `Submodule` 承载，闭性则写成其底层集合满足 `IsClosed`。Mathlib 的模商和商范数
与教材语义一致，所以本文件集中解释商范数的距离公式、闭性为何不可省略，以及闭子空间商仍为
Banach 空间。
-/

namespace SandronesLibrary.FunctionalAnalysis

open SandronesLibrary.Topology.NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedLinearSpace ℝ E]

/-- `x` 所在陪集的商范数等于 `x` 到子空间的距离。

教材公式 `‖x + S‖ = inf {‖x - s‖ | s ∈ S}` 在 Lean 中由 `Metric.infDist` 表达。

> **Entry**: functional-analysis.subspace.quotient-/
theorem quotientNorm_eq_infDist (S : Submodule ℝ E) (x : E) :
    ‖(Submodule.Quotient.mk x : E ⧸ S)‖ = Metric.infDist x S := by
  exact QuotientAddGroup.norm_mk x

/-- 不假设子空间闭时，商范数为零只能推出 `x` 属于该子空间的闭包。-/
theorem quotientNorm_eq_zero_iff_mem_closure (S : Submodule ℝ E) (x : E) :
    ‖(Submodule.Quotient.mk x : E ⧸ S)‖ = 0 ↔ x ∈ closure (S : Set E) := by
  exact QuotientAddGroup.norm_mk_eq_zero_iff_mem_closure

/-- 子空间闭时，商范数为零当且仅当 `x` 属于子空间，也就是该陪集确实为零。-/
theorem quotientNorm_eq_zero_iff_mem (S : Submodule ℝ E) (hS : IsClosed (S : Set E))
    (x : E) : ‖(Submodule.Quotient.mk x : E ⧸ S)‖ = 0 ↔ x ∈ S := by
  let _ : IsClosed (S : Set E) := hS
  exact QuotientAddGroup.norm_mk_eq_zero

/-- 规范商映射不会增大范数。-/
theorem quotientMap_norm_le (S : Submodule ℝ E) (x : E) :
    ‖(Submodule.Quotient.mk x : E ⧸ S)‖ ≤ ‖x‖ := by
  exact Submodule.Quotient.norm_mk_le S x

/-- Banach 空间对闭线性子空间取商后仍然完备。闭性正是保证商范数分离点并得到完备性的关键。-/
theorem closedSubspace_quotient_complete (S : Submodule ℝ E) (hS : IsClosed (S : Set E))
    [BanachSpace E] : CompleteSpace (E ⧸ S) := by
  let _ : IsClosed (S : Set E) := hS
  infer_instance

end SandronesLibrary.FunctionalAnalysis
