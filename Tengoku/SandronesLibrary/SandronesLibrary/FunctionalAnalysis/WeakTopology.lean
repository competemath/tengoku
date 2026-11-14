/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.FunctionalAnalysis.SeparableDual
import Tengoku.Seed.Analysis.LocallyConvex.WeakSpace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 赋范空间的弱拓扑

Mathlib 的 `WeakSpace ℝ E` 是 `E` 的类型同义词，其拓扑是使每个连续线性泛函连续的最弱
拓扑。本文件直接使用该承载，展开弱收敛的逐泛函判据，并证明范数收敛蕴含弱收敛。
-/

namespace SandronesLibrary.FunctionalAnalysis

open Filter

variable {E F α : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- 在弱拓扑下，每个原连续对偶泛函仍连续。

> **Entry**: functional-analysis.weak-topology.definition
@isnad1 id=continuo.0h2v.s9.35ac0b42bc7d from=translated src=- shape=0046c17a vocab=74f959bf
-/
theorem weak_evaluation_continuous (f : StrongDual ℝ E) :
    Continuous fun x : WeakSpace ℝ E ↦ f ((toWeakSpace ℝ E).symm x) := by
  exact WeakBilin.eval_continuous (topDualPairing ℝ E).flip f

/-- 弱收敛当且仅当每个连续线性泛函上的数值都收敛。
@isnad1 id=iff.0h5v.s10.eac0305329a2 from=translated src=- shape=40831316 vocab=ffa8a5be
-/
theorem weak_tendsto_iff_forall_dual {l : Filter α} {u : α → E} {x : E} :
    Tendsto (fun i ↦ toWeakSpace ℝ E (u i)) l (nhds (toWeakSpace ℝ E x)) ↔
      ∀ f : StrongDual ℝ E, Tendsto (fun i ↦ f (u i)) l (nhds (f x)) := by
  apply WeakBilin.tendsto_iff_forall_eval_tendsto
  intro y z hyz
  by_contra hyz'
  obtain ⟨f, hf⟩ := SeparatingDual.exists_separating_of_ne (R := ℝ) hyz'
  exact hf (DFunLike.congr_fun hyz f)

/-- 范数拓扑下的收敛总蕴含弱收敛。
@isnad1 id=tendsto.1h5v.s10.dd4424f7fb0a from=translated src=- shape=1f0ea02d vocab=dd882a12
-/
theorem norm_tendsto_implies_weak {l : Filter α} {u : α → E} {x : E}
    (hu : Tendsto u l (nhds x)) :
    Tendsto (fun i ↦ toWeakSpace ℝ E (u i)) l (nhds (toWeakSpace ℝ E x)) := by
  exact (toWeakSpaceCLM ℝ E).continuous.continuousAt.tendsto.comp hu

/-- 连续线性映射保持弱收敛。
@isnad1 id=tendsto.1h7v.s11.4b737782e3e0 from=translated src=- shape=74957a3b vocab=ecc3fb9f
-/
theorem weak_tendsto_map (T : E →L[ℝ] F) {l : Filter α} {u : α → E} {x : E}
    (hu : Tendsto (fun i ↦ toWeakSpace ℝ E (u i)) l (nhds (toWeakSpace ℝ E x))) :
    Tendsto (fun i ↦ toWeakSpace ℝ F (T (u i))) l (nhds (toWeakSpace ℝ F (T x))) := by
  exact (WeakSpace.map T).continuous.continuousAt.tendsto.comp hu

end SandronesLibrary.FunctionalAnalysis
