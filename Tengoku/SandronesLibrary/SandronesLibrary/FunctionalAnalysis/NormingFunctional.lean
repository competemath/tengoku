/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.FunctionalAnalysis.HahnBanach

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 范数化泛函与对偶范数刻画

Hahn–Banach 定理保证每个非零向量都存在一个范数为一、并在该向量上取到其范数的连续线性泛函。
结合算子范数的普遍上界，这说明对偶单位球中的泛函值精确恢复原空间范数。
-/

namespace SandronesLibrary.FunctionalAnalysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- 每个非零向量都有一个范数为一并在该向量上取到其范数的连续线性泛函。

> **Entry**: functional-analysis.hahn-banach.norming-functional
@isnad1 id=ex.1h2v.s8.81f38ce9f50f from=translated src=- shape=11dfc696 vocab=9be317ef
-/
theorem exists_norming_functional (x : E) (hx : x ≠ 0) :
    ∃ g : StrongDual ℝ E, ‖g‖ = 1 ∧ g x = ‖x‖ := by
  exact exists_dual_vector ℝ x (norm_ne_zero_iff.mpr hx)

/-- 不要求向量非零时，仍可选择范数至多一且取到向量范数的泛函。
@isnad1 id=ex.0h2v.s8.108c6838a622 from=translated src=- shape=cc78440f vocab=99ecfa86
-/
theorem exists_contracting_norming_functional (x : E) :
    ∃ g : StrongDual ℝ E, ‖g‖ ≤ 1 ∧ g x = ‖x‖ := by
  exact exists_dual_vector'' ℝ x

/-- 对偶单位球中的任意泛函值都不超过原向量范数。
@isnad1 id=le.1h3v.s7.2b42254bd91a from=translated src=- shape=6c58771b vocab=99ecfa86
-/
theorem norm_dual_apply_le_norm (x : E) (g : StrongDual ℝ E) (hg : ‖g‖ ≤ 1) :
    ‖g x‖ ≤ ‖x‖ := by
  calc
    ‖g x‖ ≤ ‖g‖ * ‖x‖ := g.le_opNorm x
    _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hg (norm_nonneg x)
    _ = ‖x‖ := one_mul _

/-- 对偶范数刻画的取到形式：对偶闭单位球中存在泛函，其值的范数恰等于 `‖x‖`。
@isnad1 id=ex.0h2v.s8.acc1a89fff05 from=translated src=- shape=3ff86edb vocab=99ecfa86
-/
theorem exists_dual_unitBall_norm_eq (x : E) :
    ∃ g : StrongDual ℝ E, ‖g‖ ≤ 1 ∧ ‖g x‖ = ‖x‖ := by
  obtain ⟨g, hg, hx⟩ := exists_contracting_norming_functional x
  exact ⟨g, hg, by rw [hx, norm_norm]⟩

/-- 连续对偶分离点：非零向量能被某个连续线性泛函检测出来。
@isnad1 id=ex.1h2v.s7.0a1341e1eb7c from=translated src=- shape=68e46e09 vocab=3df47ed4
-/
theorem exists_dual_apply_ne_zero (x : E) (hx : x ≠ 0) :
    ∃ g : StrongDual ℝ E, g x ≠ 0 := by
  obtain ⟨g, _, hgx⟩ := exists_norming_functional x hx
  exact ⟨g, by rw [hgx]; exact norm_ne_zero_iff.mpr hx⟩

end SandronesLibrary.FunctionalAnalysis
