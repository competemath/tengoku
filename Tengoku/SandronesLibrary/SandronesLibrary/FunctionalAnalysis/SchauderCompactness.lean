/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.FunctionalAnalysis.CompactOperator
import Tengoku.SandronesLibrary.SandronesLibrary.FunctionalAnalysis.DualOperator
import Tengoku.Seed.Analysis.Normed.Module.WeakDual
import Tengoku.Seed.Order.Filter.Finite

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Schauder 对偶紧性定理

本文件证明紧算子的对偶算子仍是紧算子。Mathlib 提供紧算子、弱星对偶和
Banach--Alaoglu 定理，但当前没有把它们组装成这一 Schauder 定理。
-/

namespace SandronesLibrary.FunctionalAnalysis

open Filter Function Metric Set _root_.Topology

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

private noncomputable def weakStarDualOperator (T : E →L[ℝ] F) :
    WeakDual ℝ F → StrongDual ℝ E := fun f ↦ dualOperator T f.toStrongDual

private theorem weakStarDualOperator_continuousOn_dual_unitBall
    (T : E →L[ℝ] F) (hT : IsCompactOperator T) :
    ContinuousOn (weakStarDualOperator T)
      (WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual ℝ F) 1) := by
  let B : Set (WeakDual ℝ F) :=
    WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual ℝ F) 1
  let S : Set F := closure (T '' closedBall (0 : E) 1)
  have hScompact : IsCompact S := hT.isCompact_closure_image_closedBall 1
  rw [Metric.continuousOn_iff']
  intro f hf ε hε
  obtain ⟨t : Set F, htfin, htcover⟩ :=
    (Metric.totallyBounded_iff.mp hScompact.totallyBounded) (ε / 8) (by positivity)
  have heval (y : F) :
      ∀ᶠ g : WeakDual ℝ F in 𝓝 f, ‖g y - f y‖ < ε / 2 := by
    have hcont : Continuous fun g : WeakDual ℝ F ↦ g y := WeakDual.eval_continuous y
    have htend : Tendsto (fun g : WeakDual ℝ F ↦ g y) (𝓝 f) (𝓝 (f y)) :=
      hcont.continuousAt
    rw [Metric.tendsto_nhds] at htend
    simpa [dist_eq_norm] using htend (ε / 2) (by positivity)
  have hall : ∀ᶠ g : WeakDual ℝ F in 𝓝 f, ∀ y ∈ t, ‖g y - f y‖ < ε / 2 :=
    htfin.eventually_all.mpr fun y hy ↦ heval y
  filter_upwards [hall.filter_mono inf_le_left, self_mem_nhdsWithin] with g hg hgB
  rw [dist_eq_norm]
  refine lt_of_le_of_lt ((dualOperator T g.toStrongDual -
    dualOperator T f.toStrongDual).opNorm_le_bound (by positivity : 0 ≤ 3 * ε / 4) ?_)
    (by linarith)
  intro x
  by_cases hx : x = 0
  · subst x
    simp
  have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let z : E := ‖x‖⁻¹ • x
  have hz : ‖z‖ = 1 := by simp [z, norm_smul, hxnorm.ne']
  have hTzS : T z ∈ S := subset_closure ⟨z, by simp [hz], rfl⟩
  obtain ⟨y, hyt, hTzy⟩ := by
    simpa only [mem_iUnion, mem_ball, dist_comm] using htcover hTzS
  have hfnorm : ‖f.toStrongDual‖ ≤ 1 := by simpa [B] using hf
  have hgnorm : ‖g.toStrongDual‖ ≤ 1 := by simpa [B] using hgB
  have hdiffnorm : ‖g.toStrongDual - f.toStrongDual‖ ≤ 2 := by
    calc
      ‖g.toStrongDual - f.toStrongDual‖ ≤ ‖g.toStrongDual‖ + ‖f.toStrongDual‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add hgnorm hfnorm
      _ = 2 := by norm_num
  have hpoint : ‖(g.toStrongDual - f.toStrongDual) (T z)‖ < 3 * ε / 4 := by
    calc
      ‖(g.toStrongDual - f.toStrongDual) (T z)‖
          = ‖(g.toStrongDual - f.toStrongDual) (y + (T z - y))‖ := by
            congr 2
            abel
      _ = ‖(g.toStrongDual - f.toStrongDual) y +
              (g.toStrongDual - f.toStrongDual) (T z - y)‖ := by rw [map_add]
      _
          ≤ ‖(g.toStrongDual - f.toStrongDual) y‖ +
              ‖(g.toStrongDual - f.toStrongDual) (T z - y)‖ := by
            exact norm_add_le ((g.toStrongDual - f.toStrongDual) y)
              ((g.toStrongDual - f.toStrongDual) (T z - y))
      _ ≤ ‖g y - f y‖ + ‖g.toStrongDual - f.toStrongDual‖ * ‖T z - y‖ := by
            apply add_le_add
            · simp
            · exact (g.toStrongDual - f.toStrongDual).le_opNorm _
      _ ≤ ‖g y - f y‖ + 2 * ‖T z - y‖ := by
            exact add_le_add (le_refl _)
              (mul_le_mul_of_nonneg_right hdiffnorm (norm_nonneg (T z - y)))
      _ < ε / 2 + 2 * (ε / 8) := by
            apply add_lt_add (hg y hyt)
            apply mul_lt_mul_of_pos_left _ (by norm_num : (0 : ℝ) < 2)
            simpa [dist_eq_norm, norm_sub_rev] using hTzy
      _ = 3 * ε / 4 := by ring
  have hxrepr : x = ‖x‖ • z := by
    simp [z, smul_smul, hxnorm.ne']
  change ‖(dualOperator T g.toStrongDual - dualOperator T f.toStrongDual) x‖ ≤
    (3 * ε / 4) * ‖x‖
  calc
    ‖(dualOperator T g.toStrongDual - dualOperator T f.toStrongDual) x‖ =
        ‖(dualOperator T g.toStrongDual - dualOperator T f.toStrongDual) (‖x‖ • z)‖ := by
          rw [← hxrepr]
    _ = ‖x‖ * ‖(g.toStrongDual - f.toStrongDual) (T z)‖ := by
          rw [map_smul, norm_smul, Real.norm_eq_abs, abs_norm]
          congr 2
    _ ≤ ‖x‖ * (3 * ε / 4) :=
      mul_le_mul_of_nonneg_left hpoint.le (norm_nonneg x)
    _ = (3 * ε / 4) * ‖x‖ := mul_comm _ _

/-- **Schauder 定理**：Banach 空间之间紧算子的对偶算子仍是紧算子。

证明在弱星对偶单位球上使用 Banach--Alaoglu。原算子单位球像的紧性给出有限网；
有限多个弱星求值条件再借助对偶单位球的一致范数界，提升为对偶算子像中的范数控制。

> **Entry**: functional-analysis.compact-operator.dual
@isnad1 id=iscompac.1h3v.s10.e58dc5cf5664 from=translated src=- shape=ef3c6bfc vocab=de23f467
-/
theorem dualOperator_isCompactOperator [CompleteSpace E] [CompleteSpace F]
    (T : E →L[ℝ] F) (hT : IsCompactOperator T) :
    IsCompactOperator (dualOperator T) := by
  let B : Set (WeakDual ℝ F) :=
    WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual ℝ F) 1
  let A := weakStarDualOperator T
  have hBcompact : IsCompact B := WeakDual.isCompact_closedBall 0 1
  have hABcompact : IsCompact (A '' B) :=
    hBcompact.image_of_continuousOn (weakStarDualOperator_continuousOn_dual_unitBall T hT)
  apply (isCompactOperator_iff_image_closedBall_subset_compact
    (dualOperator T).toLinearMap zero_lt_one).2
  refine ⟨A '' B, hABcompact, ?_⟩
  rintro y ⟨f, hf, rfl⟩
  refine ⟨StrongDual.toWeakDual f, ?_, rfl⟩
  simpa [A, B, mem_closedBall, dist_zero_right] using hf

end SandronesLibrary.FunctionalAnalysis
