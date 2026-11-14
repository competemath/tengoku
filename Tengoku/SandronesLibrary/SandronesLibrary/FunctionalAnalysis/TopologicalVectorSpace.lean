/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.Seed.Analysis.Normed.Module.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 拓扑向量空间基础

Mathlib 不用一个额外的“拓扑向量空间”结构包装全部数据，而是组合加法拓扑群、模和连续数乘
三个标准接口。本文件固定这层教材语言，并给出其基本展开。
-/

namespace SandronesLibrary.FunctionalAnalysis

variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [Module ℝ E] [ContinuousSMul ℝ E]

omit [Module ℝ E] [ContinuousSMul ℝ E] in
/-- 拓扑向量空间的向量加法是联合连续的。

> **Entry**: functional-analysis.topological-vector-space.foundation
@isnad1 id=continuo.0h1v.s5.2a0138b163c7 from=translated src=- shape=78180ec1 vocab=9f7ac1c5
-/
theorem topologicalVectorSpace_add_continuous :
    Continuous fun p : E × E ↦ p.1 + p.2 := by
  exact continuous_add

omit [Module ℝ E] [ContinuousSMul ℝ E] in
/-- 拓扑向量空间的取负映射连续。
@isnad1 id=continuo.0h1v.s5.db95f3bf4388 from=translated src=- shape=997987b9 vocab=3b1b33d1
-/
theorem topologicalVectorSpace_neg_continuous : Continuous fun x : E ↦ -x := by
  exact continuous_neg

omit [IsTopologicalAddGroup E] in
/-- 拓扑向量空间的标量乘法是标量与向量的联合连续映射。
@isnad1 id=continuo.0h1v.s7.d03499c2241a from=translated src=- shape=70488f6d vocab=59fb437e
-/
theorem topologicalVectorSpace_smul_continuous :
    Continuous fun p : ℝ × E ↦ p.1 • p.2 := by
  exact continuous_smul

/-- 加上固定向量是自同胚，因此任一点的局部问题都可平移到零点。-/
def topologicalVectorSpace_translation (a : E) : E ≃ₜ E :=
  Homeomorph.addLeft a

end SandronesLibrary.FunctionalAnalysis
