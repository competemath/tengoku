/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.FunctionalAnalysis.CompactOperator

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 紧算子的复合与范数极限

紧算子组成连续线性算子空间中的算子理想，并在目标空间完备时对算子范数极限封闭。
-/

namespace SandronesLibrary.FunctionalAnalysis

open Filter

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- 紧算子与连续线性映射预复合后仍紧。

> **Entry**: functional-analysis.compact-operator.composition
@isnad1 id=iscompac.1h5v.s9.3ab12d693968 from=translated src=- shape=2956a233 vocab=72db0751
-/
theorem IsCompactOperator.comp_right {T : F →L[ℝ] G} (hT : IsCompactOperator T)
    (S : E →L[ℝ] F) : IsCompactOperator (T ∘L S) := by
  simpa only [ContinuousLinearMap.coe_comp] using hT.comp_clm S

/-- 紧算子与连续线性映射后复合后仍紧。
@isnad1 id=iscompac.1h5v.s9.99942ff9f205 from=translated src=- shape=2dc7b414 vocab=72db0751
-/
theorem IsCompactOperator.comp_left {T : E →L[ℝ] F} (hT : IsCompactOperator T)
    (S : F →L[ℝ] G) : IsCompactOperator (S ∘L T) := by
  simpa only [ContinuousLinearMap.coe_comp] using hT.clm_comp S

/-- 两个紧算子的和仍是紧算子。
@isnad1 id=iscompac.2h4v.s9.75c05e63c3a8 from=translated src=- shape=f6cb0587 vocab=093bccd6
-/
theorem IsCompactOperator.add_clm {S T : E →L[ℝ] F}
    (hS : IsCompactOperator S) (hT : IsCompactOperator T) :
    IsCompactOperator (S + T) := by
  exact hS.add hT

/-- 若目标空间完备，紧算子的算子范数极限仍是紧算子。
@isnad1 id=iscompac.2h4v.s9.fe4f70424682 from=translated src=- shape=904a1255 vocab=4902915a
-/
theorem isCompactOperator_of_operatorNorm_tendsto [CompleteSpace F]
    {T : ℕ → E →L[ℝ] F} {S : E →L[ℝ] F}
    (hlim : Tendsto T atTop (nhds S)) (hT : ∀ n, IsCompactOperator (T n)) :
    IsCompactOperator S := by
  exact isCompactOperator_of_tendsto hlim (Filter.Eventually.of_forall hT)

end SandronesLibrary.FunctionalAnalysis
