/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.FunctionalAnalysis.WeakTopology

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 对偶空间的弱星拓扑

`WeakDual ℝ E` 与连续对偶 `StrongDual ℝ E` 具有相同的底层线性对象，但携带使每个
向量求值映射 `f ↦ f x` 连续的最弱拓扑。这是弱星拓扑，它与把对偶空间自身视为原空间所得的
弱拓扑不同。
-/

namespace SandronesLibrary.FunctionalAnalysis

open Filter

variable {E α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- 弱星拓扑下，在每个原空间向量上的求值映射都连续。

> **Entry**: functional-analysis.weak-star.definition
@isnad1 id=continuo.0h2v.s7.bd2e4133c079 from=translated src=- shape=0e76539d vocab=ce34e177
-/
theorem weakStar_evaluation_continuous (x : E) :
    Continuous fun f : WeakDual ℝ E ↦ f x := by
  exact WeakDual.eval_continuous x

/-- 弱星收敛当且仅当在原空间的每个向量上逐点收敛。
@isnad1 id=iff.0h5v.s11.5f74cc880843 from=translated src=- shape=e135af50 vocab=043d5757
-/
theorem weakStar_tendsto_iff_forall {l : Filter α} {u : α → StrongDual ℝ E}
    {f : StrongDual ℝ E} :
    Tendsto (fun i ↦ StrongDual.toWeakDual (u i)) l
        (nhds (StrongDual.toWeakDual f)) ↔
      ∀ x : E, Tendsto (fun i ↦ u i x) l (nhds (f x)) := by
  rw [tendsto_iff_forall_eval_tendsto_topDualPairing]
  constructor
  · intro h x
    have hx := h x
    change Tendsto (fun i ↦ u i x) l (nhds (f x)) at hx
    exact hx
  · intro h x
    change Tendsto (fun i ↦ u i x) l (nhds (f x))
    exact h x

/-- 对偶范数收敛蕴含弱星收敛。
@isnad1 id=tendsto.1h5v.s11.029faa455d9a from=translated src=- shape=6f179af5 vocab=043d5757
-/
theorem dual_norm_tendsto_implies_weakStar {l : Filter α} {u : α → StrongDual ℝ E}
    {f : StrongDual ℝ E} (hu : Tendsto u l (nhds f)) :
    Tendsto (fun i ↦ StrongDual.toWeakDual (u i)) l
      (nhds (StrongDual.toWeakDual f)) := by
  rw [weakStar_tendsto_iff_forall]
  intro x
  exact (ContinuousLinearMap.lipschitzWith_apply x).continuous.continuousAt.tendsto.comp hu

/-- 对偶空间上的弱收敛蕴含弱星收敛。
@isnad1 id=tendsto.1h5v.s13.88a4617c9f4d from=translated src=- shape=24223b71 vocab=6e93f97d
-/
theorem dual_weak_tendsto_implies_weakStar {l : Filter α} {u : α → StrongDual ℝ E}
    {f : StrongDual ℝ E}
    (hu : Tendsto (fun i ↦ toWeakSpace ℝ (StrongDual ℝ E) (u i)) l
      (nhds (toWeakSpace ℝ (StrongDual ℝ E) f))) :
    Tendsto (fun i ↦ StrongDual.toWeakDual (u i)) l
      (nhds (StrongDual.toWeakDual f)) := by
  rw [weakStar_tendsto_iff_forall]
  intro x
  exact (weak_tendsto_iff_forall_dual.mp hu) (NormedSpace.inclusionInDoubleDual ℝ E x)

end SandronesLibrary.FunctionalAnalysis
