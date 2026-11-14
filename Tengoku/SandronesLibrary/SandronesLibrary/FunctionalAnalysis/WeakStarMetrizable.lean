/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.FunctionalAnalysis.BanachAlaoglu

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 可分空间对偶球的弱星可度量化与序列抽取

Banach–Alaoglu 给出弱星紧致；当原空间可分时，弱星紧子集还可度量化，因此对偶闭球具有
教材常用的序列抽取形式。
-/

namespace SandronesLibrary.FunctionalAnalysis

open Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace.SeparableSpace E]

/-- 可分赋范空间的任意弱星紧子集都是可度量化的。

> **Entry**: functional-analysis.weak.metrizable-separable-/
theorem weakStar_metrizable_of_isCompact (K : Set (WeakDual ℝ E)) (hK : IsCompact K) :
    TopologicalSpace.MetrizableSpace K := by
  exact WeakDual.metrizable_of_isCompact ℝ E K hK

/-- 可分赋范空间连续对偶的每个范数闭球都是弱星序列紧的。-/
theorem weakStar_isSeqCompact_closedBall (f : StrongDual ℝ E) (r : ℝ) :
    IsSeqCompact (WeakDual.toStrongDual ⁻¹' Metric.closedBall f r) := by
  exact WeakDual.isSeqCompact_closedBall ℝ E f r

/-- 对偶闭单位球中每个序列都有弱星收敛子列，且极限仍在闭单位球中。-/
theorem exists_weakStar_convergent_subsequence_of_norm_le_one
    (u : ℕ → StrongDual ℝ E) (hu : ∀ n, ‖u n‖ ≤ 1) :
    ∃ f : StrongDual ℝ E, ‖f‖ ≤ 1 ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n ↦ StrongDual.toWeakDual (u (φ n))) atTop
        (nhds (StrongDual.toWeakDual f)) := by
  let S : Set (WeakDual ℝ E) :=
    WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ E) 1
  have huS : ∀ n, StrongDual.toWeakDual (u n) ∈ S := by
    intro n
    simp [S, Metric.mem_closedBall, hu n]
  obtain ⟨a, haS, φ, hφ, hlim⟩ :=
    (weakStar_isSeqCompact_closedBall (E := E) 0 1).subseq_of_frequently_in
      ((Filter.Eventually.of_forall huS).frequently)
  refine ⟨WeakDual.toStrongDual a, ?_, φ, hφ, ?_⟩
  · simpa [S, Metric.mem_closedBall] using haS
  · simpa [Function.comp_def, WeakDual.toWeakDual_toStrongDual] using hlim

end SandronesLibrary.FunctionalAnalysis
