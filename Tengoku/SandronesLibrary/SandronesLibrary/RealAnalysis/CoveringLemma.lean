/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# RealAnalysis / CoveringLemma —— 一维 Vitali 覆盖引理（Folland RA-F3 前置）

本文件当前条目（引理清单，§0 铁律4：一次一条，逐条编译）：

* **real-analysis.covering-lemma**（一维 Vitali 覆盖引理：区间族的 τ-放大不交子族、
  其测度形式，以及 Mathlib `VitaliFamily` 抽象覆盖接口的桥）✅。

> **教材定位**：Gerald B. Folland, *Real Analysis: Modern Techniques and Their Applications*,
> Second Edition, §3.4（Differentiation on Euclidean Space）中的 "simple Vitali lemma"／
> 覆盖论证。Folland 在 ℝⁿ 上用球陈述、放大常数取 `3ⁿ`；本文件在 ℝ 上用开区间陈述，
> 放大常数取任意 `τ > 3`（`τ = 4` 是下文使用的具体取值），这是 Mathlib
> `Vitali.exists_disjoint_subfamily_covering_enlargement_ball` 给出的常数口径。
> **常数差异已披露**：本库不声称复刻 Folland 的 `3ⁿ`，只声称同样的覆盖结论形状。

### 本文件的接口契约（RA-F3 冻结签名，`real-analysis.maximal-function` 依赖）

覆盖引理这一 Entry 的作用是**为 Hardy–Littlewood 极大函数的弱型 `(1,1)` 估计提供前置**。
下游只需要下面这条接口（签名已冻结，改动即升级）：

* `SandronesLibrary.RealAnalysis.Covering.OpenInterval`：开区间载体 `(l, u)`，带 `l < u`；
* `OpenInterval.toSet / center / radius`：区间、中点、半长；
* `OpenInterval.ball_center_radius`：区间 = 以中点为心、半长为半径的开球（交给 Mathlib 球族
  覆盖定理的桥）；
* `exists_disjoint_interval_subfamily_covering_enlargement`：**主引理**——半径一致有界的
  区间族中可抽出不交子族 `u`，使原族每个区间都落在 `u` 中某个区间的 `τ`-放大之内；
* `volume_iUnion_le_mul_tsum`：**测度形式**——原并集的测度被 `τ` 倍的不交子族总测度控制。

### Mathlib 角色（本文件）

* `Vitali.exists_disjoint_subfamily_covering_enlargement_ball`：**私有证明后端**（本文件主引理
  的证明引擎；它是 Mathlib 已证的 Zorn 式覆盖定理，本库不重证）。
* `Set.PairwiseDisjoint.countable_of_nonempty_interior`：不交开区间族至多可数的**私有后端**
  （可分空间中的不交非空开集族至多可数）。
* `MeasureTheory.measure_iUnion_le`、`MeasureTheory.measure_biUnion`：测度形式的**私有后端**。
* `MeasureTheory.VitaliFamily` 及其 `FineSubfamilyOn`／`measure_le_of_frequently_le`：**桥侧接口**，
  是本库将来（RA-F4，Lebesgue 点与微分定理）把覆盖引理接到 "a.e. 不交覆盖" 的通道；
  本窗**不**交付 Lebesgue 微分定理，只暴露接口。
* `IsUnifLocDoublingMeasure.vitaliFamily`：`volume` 上 Vitali 族的**构造后端**。
-/

namespace SandronesLibrary

namespace RealAnalysis.Covering

open MeasureTheory Set Metric
open scoped ENNReal Topology

/-! ## 1. 开区间载体与几何接口 -/

/-- **开区间**：实数对 `(l, u)` 连同 `l < u` 的证明。教材中极大函数与覆盖引理都按
"含某点的开区间" 量化，本结构就是这个量词域的具体承载；`toSet` 给出对应的集合。
> **Entry**: real-analysis.covering-lemma-/
structure OpenInterval where
  /-- 左端点。-/
  l : ℝ
  /-- 右端点。-/
  u : ℝ
  /-- 端点严格有序。-/
  lt : l < u

namespace OpenInterval

/-- 开区间对应的集合 `(l, u)`。
> **Entry**: real-analysis.covering-lemma-/
def toSet (I : OpenInterval) : Set ℝ := Ioo I.l I.u

/-- 区间中点 `(l + u) / 2`。
> **Entry**: real-analysis.covering-lemma-/
noncomputable def center (I : OpenInterval) : ℝ := (I.l + I.u) / 2

/-- 区间半长（半径）`(u - l) / 2`。
> **Entry**: real-analysis.covering-lemma-/
noncomputable def radius (I : OpenInterval) : ℝ := (I.u - I.l) / 2

/--
@isnad1 id=eq.0h1v.s4.fed1fe7de043 from=translated src=- shape=93a81373 vocab=aaad34f4
-/
@[simp]
theorem center_sub_radius (I : OpenInterval) : I.center - I.radius = I.l := by
  simp only [center, radius]; ring

/--
@isnad1 id=eq.0h1v.s4.8f461f0d2cb8 from=translated src=- shape=93a81373 vocab=eb440142
-/
@[simp]
theorem center_add_radius (I : OpenInterval) : I.center + I.radius = I.u := by
  simp only [center, radius]; ring

/-- 半径严格为正（因为端点严格有序）。测度形式中用它把区间识别为非空开集。
> **Entry**: real-analysis.covering-lemma
@isnad1 id=lt.0h1v.s3.3f577afffa65 from=translated src=- shape=b9369acb vocab=79b61da5
-/
theorem radius_pos (I : OpenInterval) : 0 < I.radius := by
  simp only [radius]; linarith [I.lt]

/-- **区间 = 开球**：`(l, u)` 恰是以中点为心、半长为半径的开球。这是本文件把 "区间族"
交给 Mathlib 球族覆盖定理（`Vitali.exists_disjoint_subfamily_covering_enlargement_ball`）
的桥，也是下游把极大函数写成球平均时的换算。
> **Entry**: real-analysis.covering-lemma
@isnad1 id=eq.0h1v.s3.41bdf32ebe80 from=translated src=- shape=9bb5979c vocab=694f900f
-/
theorem ball_center_radius (I : OpenInterval) : ball I.center I.radius = I.toSet := by
  rw [Real.ball_eq_Ioo, center_sub_radius, center_add_radius, toSet]

/--
@isnad1 id=iff.0h2v.s4.6f4becb9c14c from=translated src=- shape=5bb38095 vocab=b99d3954
-/
theorem mem_toSet_iff {I : OpenInterval} {x : ℝ} :
    x ∈ I.toSet ↔ I.l < x ∧ x < I.u := Iff.rfl

/-- 中点属于区间（区间非空）。
> **Entry**: real-analysis.covering-lemma
@isnad1 id=mem.0h1v.s3.5bf47a05fe12 from=translated src=- shape=b5ca9b95 vocab=baae203d
-/
theorem center_mem_toSet (I : OpenInterval) : I.center ∈ I.toSet := by
  rw [mem_toSet_iff, center]
  constructor <;> linarith [I.lt]

/-- 区间是开集。
> **Entry**: real-analysis.covering-lemma
@isnad1 id=isopen.0h1v.s3.98a968b72dba from=translated src=- shape=1a6c1393 vocab=f48afe29
-/
theorem isOpen_toSet (I : OpenInterval) : IsOpen I.toSet := isOpen_Ioo

/-- 区间可测。
> **Entry**: real-analysis.covering-lemma
@isnad1 id=measurab.0h1v.s2.19e2a727729e from=translated src=- shape=1a6c1393 vocab=d6e39a34
-/
theorem measurableSet_toSet (I : OpenInterval) : MeasurableSet I.toSet :=
  measurableSet_Ioo

end OpenInterval

/-! ## 2. 覆盖引理（主引理） -/

variable {ι : Type*}

/-- **一维 Vitali 覆盖引理（区间族，`τ`-放大形式）**。

设 `t` 是一族开区间 `I a`，其半径一致有界（`radius (I a) ≤ R`）。则存在不交子族
`u ⊆ t`，使得 `t` 中每个区间都包含在 `u` 中某个区间的 `τ`-放大
`ball (center) (τ * radius)` 之内，其中 `τ > 3` 任意。

这是 Folland §3.4 "simple Vitali lemma" 的一维形式；放大常数口径为 Mathlib 的 `τ > 3`
（下游取 `τ = 4`）。**证明后端**是 Mathlib 的
`Vitali.exists_disjoint_subfamily_covering_enlargement_ball`（Zorn 式抽象覆盖定理），
本库只做"区间 ↔ 球"的换算，不重证组合核心。
> **Entry**: real-analysis.covering-lemma
@isnad1 id=ex.2h5v.s7.cacf946194f9 from=translated src=- shape=568c24ff vocab=b7b09a2c
-/
theorem exists_disjoint_interval_subfamily_covering_enlargement
    (t : Set ι) (I : ι → OpenInterval) (R : ℝ) (hR : ∀ a ∈ t, (I a).radius ≤ R)
    {τ : ℝ} (hτ : 3 < τ) :
    ∃ u ⊆ t, u.PairwiseDisjoint (fun a => (I a).toSet) ∧
      ∀ a ∈ t, ∃ b ∈ u, (I a).toSet ⊆ ball (I b).center (τ * (I b).radius) := by
  obtain ⟨u, hut, hdisj, hcov⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_ball t
      (fun a => (I a).center) (fun a => (I a).radius) R hR τ hτ
  refine ⟨u, hut, ?_, ?_⟩
  · simpa only [OpenInterval.ball_center_radius] using hdisj
  · intro a ha
    obtain ⟨b, hb, hsub⟩ := hcov a ha
    exact ⟨b, hb, by simpa only [OpenInterval.ball_center_radius] using hsub⟩

/-! ## 3. 覆盖引理的测度形式 -/

/-- **覆盖引理的测度形式**。

设 `u ⊆ t` 是覆盖引理抽出的不交子族，且 `t` 中每个区间落在 `u` 中某个区间的 `τ`-放大内。
则原族并集的 Lebesgue 测度被 `τ` 倍的不交子族总测度控制：

`volume (⋃ a ∈ t, I a) ≤ τ * ∑' b : u, volume (I b)`。

这正是弱型 `(1,1)` 估计中 "坏集测度控制" 那一步：把坏集塞进不交区间族，再用每个区间的
测度换积分。`u` 的至多可数性来自 "可分空间中不交非空开集族至多可数"。
> **Entry**: real-analysis.covering-lemma
@isnad1 id=le.4h5v.s7.c3254cb898ad from=translated src=- shape=770ee5a7 vocab=43af45f0
-/
theorem volume_iUnion_le_mul_tsum
    (t : Set ι) (I : ι → OpenInterval) (u : Set ι) (_hut : u ⊆ t)
    (hdisj : u.PairwiseDisjoint fun a => (I a).toSet)
    (hcov : ∀ a ∈ t, ∃ b ∈ u, (I a).toSet ⊆ ball (I b).center (τ * (I b).radius))
    (hτ : 0 ≤ τ) :
    volume (⋃ a ∈ t, (I a).toSet) ≤ ENNReal.ofReal τ * ∑' b : u, volume ((I b).toSet) := by
  have hcount : u.Countable :=
    hdisj.countable_of_nonempty_interior fun i _ => by
      rw [(OpenInterval.isOpen_toSet (I i)).interior_eq]
      exact ⟨(I i).center, OpenInterval.center_mem_toSet (I i)⟩
  have hcount' : Countable u := hcount.to_subtype
  calc
    volume (⋃ a ∈ t, (I a).toSet)
        ≤ volume (⋃ b ∈ u, ball (I b).center (τ * (I b).radius)) := by
          apply measure_mono
          intro x hx
          obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.1 hx
          obtain ⟨b, hb, hsub⟩ := hcov a ha
          exact mem_iUnion₂.2 ⟨b, hb, hsub hxa⟩
    _ = volume (⋃ b : u, ball (I b).center (τ * (I b).radius)) := by
          rw [Set.iUnion_subtype]
    _ ≤ ∑' b : u, volume (ball (I b).center (τ * (I b).radius)) :=
          measure_iUnion_le _
    _ = ENNReal.ofReal τ * ∑' b : u, volume ((I b).toSet) := by
          rw [← ENNReal.tsum_mul_left]
          apply tsum_congr
          intro b
          rw [Real.volume_ball, ← OpenInterval.ball_center_radius, Real.volume_ball,
            ← ENNReal.ofReal_mul hτ]
          congr 1
          ring

/-! ## 4. 抽象覆盖接口的桥（供 RA-F4，不在本窗交付） -/

/-- **`volume` 上的 Vitali 族**：`ℝ` 上 Lebesgue 测度是局部一致加倍测度，故
`IsUnifLocDoublingMeasure.vitaliFamily` 给出 `volume` 的 Vitali 族。它是覆盖引理
"a.e. 不交覆盖" 一面的入口：`VitaliFamily.covering` 说的正是 "细族可抽出几乎处处不交覆盖"。

本库**本窗不交付** Lebesgue 微分定理（RA-F4），此声明只是把接口暴露出来，供 RA-F4 使用。
> **Entry**: real-analysis.covering-lemma-/
noncomputable def vitaliFamilyVolume : VitaliFamily (volume : Measure ℝ) :=
  IsUnifLocDoublingMeasure.vitaliFamily (volume : Measure ℝ) 1

/-- **a.e. 不交覆盖 ⇒ 测度控制**（抽象覆盖引擎）：在 Vitali 族 `v` 中，若集合 `s` 上每点都
"频繁" 落在满足 `ρ a ≤ ν a` 的集合里，且 `ρ ≪ μ`，则 `ρ s ≤ ν s`。这是 Folland §3.4
覆盖论证的抽象形式，也是弱型估计里 "坏集测度控制" 的可复用接口。

本库**本窗不交付** Lebesgue 微分定理（RA-F4），此声明只是把接口暴露出来。
> **Entry**: real-analysis.covering-lemma
@isnad1 id=le.2h5v.s7.c4224d593e3e from=translated src=- shape=5af347cd vocab=6b9f1565
-/
theorem measure_le_of_frequently_le_vitali
    {μ : Measure ℝ} (v : VitaliFamily μ) {ρ : Measure ℝ}
    (ν : Measure ℝ) [IsLocallyFiniteMeasure ν] (hρ : ρ ≪ μ) (s : Set ℝ)
    (hs : ∀ x ∈ s, ∃ᶠ a in v.filterAt x, ρ a ≤ ν a) : ρ s ≤ ν s :=
  v.measure_le_of_frequently_le ν hρ s hs

/-- **细族的不交覆盖控制自身测度**：`v.FineSubfamilyOn f s` 时，`s` 的 `μ`-测度被抽出的
不交覆盖 `h.covering` 的测度级数控制。这是覆盖引理在 "a.e. 覆盖" 一面的直接测度形式。
> **Entry**: real-analysis.covering-lemma
@isnad1 id=le.1h4v.s7.780f865552b0 from=translated src=- shape=dfde7923 vocab=9beb9103
-/
theorem fineSubfamilyOn_measure_le_tsum
    {μ : Measure ℝ} {v : VitaliFamily μ} {f : ℝ → Set (Set ℝ)} {s : Set ℝ}
    (h : v.FineSubfamilyOn f s) : μ s ≤ ∑' x : h.index, μ (h.covering x) :=
  h.measure_le_tsum

end RealAnalysis.Covering

end SandronesLibrary
