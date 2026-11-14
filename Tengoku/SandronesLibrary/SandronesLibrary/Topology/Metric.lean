/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Topology / Metric —— 度量空间与完备性（点集拓扑第一学期 T3）

本文件当前条目（引理清单，§0 铁律4：一次一条，逐条编译）：

* **topology.metric.def**（度量公理：对称/三角/自反/零距/非负；开球：成员/开集/自含/单调）✅。
* **topology.metric.uniform**（一致连续 ε-δ 判据；一致连续 ⟹ 连续；恒等一致连续）✅。
* **topology.metric.cauchy-complete**（Cauchy ε-N 判据；完备 ⟹ Cauchy 收敛）✅。
* **topology.metric.completion**（完备化：嵌入一致连续/嵌入单射）✅。

> **语言说明**：点集拓扑阶段（§Phase4）mathlib 的 `MetricSpace`/`Metric.ball`/
> `UniformContinuous`/`CompleteSpace`/`UniformSpace.Completion` 等**教材结构可直接出现在签名**。
-/

namespace SandronesLibrary

namespace Topology.Metric

/-- **度量对称性**（公理）：dist x y = dist y x。 
> **Entry**: topology.metric.def
@isnad1 id=eq.0h3v.s4.a0b585cbc9ff from=translated src=- shape=3ad41523 vocab=4e1b5a7e
-/
theorem metric_dist_comm {X : Type*} [PseudoMetricSpace X] (x y : X) : dist x y = dist y x := by
  exact dist_comm x y

/-- **度量三角不等式**（公理）：dist x z ≤ dist x y + dist y z。 
> **Entry**: topology.metric.def
@isnad1 id=le.0h4v.s5.8a87c95c714b from=translated src=- shape=cd139c56 vocab=9c7c2813
-/
theorem metric_dist_triangle {X : Type*} [PseudoMetricSpace X] (x y z : X) :
    dist x z ≤ dist x y + dist y z := by
  exact dist_triangle x y z

/-- **度量自反性**（公理）：dist x x = 0。 
> **Entry**: topology.metric.def
@isnad1 id=eq.0h2v.s4.ffa6ca946d1a from=translated src=- shape=980d5fe1 vocab=4e1b5a7e
-/
theorem metric_dist_self {X : Type*} [PseudoMetricSpace X] (x : X) : dist x x = 0 := by
  exact dist_self x

/-- **度量零距判等**（公理）：dist x y = 0 ⟺ x = y。 
> **Entry**: topology.metric.def
@isnad1 id=iff.0h3v.s4.f95a8f546940 from=translated src=- shape=a33337ff vocab=5c51227e
-/
theorem metric_dist_eq_zero_iff {X : Type*} [MetricSpace X] {x y : X} : dist x y = 0 ↔ x = y := by
  exact dist_eq_zero

/-- **度量非负**：dist x y ≥ 0。 
> **Entry**: topology.metric.def
@isnad1 id=le.0h3v.s4.11aa4b001b36 from=translated src=- shape=7bcc0503 vocab=e96d98f8
-/
theorem metric_dist_nonneg {X : Type*} [PseudoMetricSpace X] {x y : X} : 0 ≤ dist x y := by
  exact dist_nonneg

/-- **开球成员刻画**：y ∈ B(x,ε) ⟺ dist y x < ε。 
> **Entry**: topology.metric.def
@isnad1 id=iff.0h4v.s5.3638efdd1124 from=translated src=- shape=7ae8e2de vocab=d39c9415
-/
theorem metric_mem_ball_iff {X : Type*} [PseudoMetricSpace X] {x y : X} {ε : ℝ} :
    y ∈ Metric.ball x ε ↔ dist y x < ε := by
  exact Metric.mem_ball

/-- **开球是开集**：B(x,ε) 在度量拓扑中是开集。 
> **Entry**: topology.metric.def
@isnad1 id=isopen.0h3v.s4.c0a0d6ce1645 from=translated src=- shape=4a5c8032 vocab=24299a98
-/
theorem metric_isOpen_ball {X : Type*} [PseudoMetricSpace X] (x : X) (ε : ℝ) :
    IsOpen (Metric.ball x ε) := by
  exact Metric.isOpen_ball

/-- **球心在球内**：ε > 0 时 x ∈ B(x,ε)。 
> **Entry**: topology.metric.def
@isnad1 id=mem.1h3v.s5.2f6725f5b16f from=translated src=- shape=968e0ff0 vocab=f9f025fe
-/
theorem metric_mem_ball_self {X : Type*} [PseudoMetricSpace X] {x : X} {ε : ℝ} (h : 0 < ε) :
    x ∈ Metric.ball x ε := by
  exact Metric.mem_ball_self h

/-- **球单调**：ε₁ ≤ ε₂ 时 B(x,ε₁) ⊆ B(x,ε₂)。 
> **Entry**: topology.metric.def
@isnad1 id=le.1h4v.s5.f10c3cc80e17 from=translated src=- shape=1fc8ea8e vocab=bec85440
-/
theorem metric_ball_subset_ball {X : Type*} [PseudoMetricSpace X] {x : X} {ε₁ ε₂ : ℝ}
    (h : ε₁ ≤ ε₂) : Metric.ball x ε₁ ⊆ Metric.ball x ε₂ := by
  exact Metric.ball_subset_ball h

/-- **一致连续的 ε-δ 判据**：f 一致连续 ⟺ ∀ ε > 0, ∃ δ > 0, dist 小 ⟹ dist 小。 
> **Entry**: topology.metric.uniform
@isnad1 id=iff.0h3v.s6.517995293305 from=translated src=- shape=ef973599 vocab=1ebde80a
-/
theorem metric_uniformContinuous_iff_eps_delta {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {f : X → Y} : UniformContinuous f ↔
      ∀ ε > 0, ∃ δ > 0, ∀ {a b : X}, dist a b < δ → dist (f a) (f b) < ε := by
  exact Metric.uniformContinuous_iff

/-- **一致连续 ⟹ 连续**：一致连续的函数必连续。 
> **Entry**: topology.metric.uniform
@isnad1 id=continuo.1h3v.s5.a098b6abc9d6 from=translated src=- shape=65287ac1 vocab=bd8f5ab7
-/
theorem metric_uniformContinuous_of_continuous {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {f : X → Y} (hf : UniformContinuous f) : Continuous f := by
  exact hf.continuous

/-- **恒等映射一致连续**。 
> **Entry**: topology.metric.uniform
@isnad1 id=uniformc.0h1v.s4.56416b11209d from=translated src=- shape=746c6e19 vocab=1bab46e4
-/
theorem metric_uniformContinuous_id {X : Type*} [PseudoMetricSpace X] :
    UniformContinuous (id : X → X) := by
  exact uniformContinuous_id

/-- **Cauchy 列的 ε-N 判据**：u 是 Cauchy 列 ⟺ 任意 ε > 0 存在 N 使 m,n ≥ N 时 dist < ε。 
> **Entry**: topology.metric.cauchy-complete
@isnad1 id=iff.0h2v.s6.2d075aefd8a4 from=translated src=- shape=b50db95a vocab=3fba14ee
-/
theorem metric_cauchySeq_iff_eps_N {X : Type*} [PseudoMetricSpace X] {u : ℕ → X} :
    CauchySeq u ↔ ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, dist (u m) (u n) < ε := by
  exact Metric.cauchySeq_iff

/-- **完备空间中 Cauchy 列收敛**：完备 ⟹ 每个 Cauchy 列有极限。 
> **Entry**: topology.metric.cauchy-complete
@isnad1 id=ex.1h2v.s5.e3f352136bd8 from=translated src=- shape=92742c2c vocab=2367dd4d
-/
theorem metric_cauchySeq_tendsto_of_complete {X : Type*} [PseudoMetricSpace X] [CompleteSpace X]
    {u : ℕ → X} (hu : CauchySeq u) : ∃ x : X, Filter.Tendsto u Filter.atTop (nhds x) := by
  exact cauchySeq_tendsto_of_complete hu

/-- **完备化的嵌入一致连续**：完备化的自然嵌入 `α → Completion α` 一致连续。
  完备化是"把 X 嵌进一个完备空间"。 
> **Entry**: topology.metric.completion
@isnad1 id=uniformc.0h1v.s4.4afa7dc0d766 from=translated src=- shape=a638af76 vocab=b4877184
-/
theorem completion_coe_uniformContinuous (X : Type*) [UniformSpace X] :
    UniformContinuous (UniformSpace.Completion.coe' : X → UniformSpace.Completion X) := by
  exact UniformSpace.Completion.uniformContinuous_coe X

/-- **完备化嵌入单射**：T0 空间中完备化嵌入是单射（X 看作 Completion 的子空间）。 
> **Entry**: topology.metric.completion
@isnad1 id=injectiv.0h1v.s4.ad29c70ac31c from=translated src=- shape=5b894d8a vocab=17e975b5
-/
theorem completion_coe_injective (X : Type*) [UniformSpace X] [T0Space X] :
    Function.Injective (UniformSpace.Completion.coe' : X → UniformSpace.Completion X) := by
  exact UniformSpace.Completion.coe_injective X

end Topology.Metric

end SandronesLibrary
