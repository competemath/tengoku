/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# RealAnalysis / SignedMeasureDefinition —— 有符号测度与正／负／零集（Folland RA-F1）

本文件当前条目（引理清单）：

* **real-analysis.signed-measure.definition**（有符号测度：载体、空集零测、非可测集零、
  有限可加、可数可加、上连续；由有限正测度构造；正集／负集／零集及与
  `0 ≤[i] s` / `s ≤[i] 0` 的桥）✅。

> **语言说明**：实分析阶段（§Phase5）mathlib 的 `MeasureTheory.VectorMeasure` /
> `MeasureTheory.SignedMeasure` 等**教材结构可直接出现在签名**（测度积分是 mathlib 的核心库）。
> 教材中有符号测度定义为“取实值（有限）的 σ-可加集函数，空集取零”，与
> `MeasureTheory.SignedMeasure α = VectorMeasure α ℝ` 语义一致，故本库直接复用该载体，
> 不另造同构结构。

### Mathlib 角色（本文件）

* `MeasureTheory.SignedMeasure`（= `VectorMeasure α ℝ`）：**正式公开承载**（正式教材载体）。
* `VectorMeasure.of_union` / `m_iUnion` / `of_biUnion_finset` /
  `tendsto_vectorMeasure_iUnion_atTop_nat`：**语义一致的展开后端**。
* `Measure.toSignedMeasure` 及其等式：**正测度 → 有符号测度的桥**。
* `0 ≤[i] s` / `s ≤[i] 0`（`VectorMeasure.restrict` 上的序）：正集／负集的 **Mathlib 侧刻画**，
  本库用课程量词定义 `IsPositiveSet` 等并给出具名桥。
-/

namespace SandronesLibrary

namespace RealAnalysis.SignedMeasure

open MeasureTheory Filter
open scoped ENNReal Function Topology

variable {α : Type*} [MeasurableSpace α]

/-! ## 1. 有符号测度载体及其展开性质 -/

/-- **有符号测度：空集零测**。教材定义的第一条：`s ∅ = 0`。
> **Entry**: real-analysis.signed-measure.definition
@isnad1 id=eq.0h2v.s5.58e21ae7d418 from=translated src=- shape=9eba1161 vocab=bbf0e374
-/
theorem signedMeasure_empty (s : SignedMeasure α) : s ∅ = 0 :=
  s.empty

/-- **有符号测度：非可测集取零**。Mathlib 的载体规定非可测集取零，使外延性只比较可测集。
> **Entry**: real-analysis.signed-measure.definition
@isnad1 id=eq.1h3v.s5.018d66601d94 from=translated src=- shape=b2a213cd vocab=7fbdffdd
-/
theorem signedMeasure_not_measurable (s : SignedMeasure α) {i : Set α}
    (hi : ¬ MeasurableSet i) : s i = 0 :=
  s.not_measurable hi

/-- **有符号测度：有限可加**。两两不交可测集 `A`、`B` 满足 `s (A ∪ B) = s A + s B`。
教材记号下的“有限可加性”。
> **Entry**: real-analysis.signed-measure.definition
@isnad1 id=eq.3h4v.s7.da53598a1502 from=translated src=- shape=5c0dd840 vocab=34dd647d
-/
theorem signedMeasure_union (s : SignedMeasure α) {A B : Set α} (h : Disjoint A B)
    (hA : MeasurableSet A) (hB : MeasurableSet B) : s (A ∪ B) = s A + s B :=
  VectorMeasure.of_union (v := s) h hA hB

/-- **有符号测度：差集公式**。若 `A ⊆ B` 均可测，则 `s (B \ A) = s B - s A`。
> **Entry**: real-analysis.signed-measure.definition
@isnad1 id=eq.3h4v.s6.61c889657817 from=translated src=- shape=bcf38a1a vocab=9fd7c039
-/
theorem signedMeasure_sdiff (s : SignedMeasure α) {A B : Set α} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (h : A ⊆ B) : s (B \ A) = s B - s A :=
  VectorMeasure.of_sdiff (v := s) hA hB h

/-- **有符号测度：补集公式**。`s Aᶜ = s univ - s A`（`A` 可测）。
> **Entry**: real-analysis.signed-measure.definition
@isnad1 id=eq.1h3v.s6.cf4c77a1886e from=translated src=- shape=6326800b vocab=1a073aa2
-/
theorem signedMeasure_compl (s : SignedMeasure α) {A : Set α} (hA : MeasurableSet A) :
    s Aᶜ = s Set.univ - s A :=
  VectorMeasure.of_compl (v := s) hA

/-- **有符号测度：可数可加**。两两不交可测集列 `f` 满足
`HasSum (fun n ↦ s (f n)) (s (⋃ n, f n))`（实数的无条件级数）。
> **Entry**: real-analysis.signed-measure.definition
@isnad1 id=hassum.2h3v.s7.9b0e5bd2b6b6 from=translated src=- shape=4cc45441 vocab=f15130ae
-/
theorem signedMeasure_iUnion (s : SignedMeasure α) {f : ℕ → Set α}
    (hf : ∀ n, MeasurableSet (f n)) (hd : Pairwise (Disjoint on f)) :
    HasSum (fun n ↦ s (f n)) (s (⋃ n, f n)) :=
  s.m_iUnion hf hd

/-- **有符号测度：有限并公式**。有限个两两不交可测集的并取值为和。
> **Entry**: real-analysis.signed-measure.definition
@isnad1 id=eq.2h5v.s7.588861a04535 from=translated src=- shape=bf6766e2 vocab=8224c8a9
-/
theorem signedMeasure_iUnion_finset (s : SignedMeasure α) {ι : Type*} {t : Finset ι}
    {f : ι → Set α} (hd : (t : Set ι).PairwiseDisjoint f)
    (hm : ∀ b ∈ t, MeasurableSet (f b)) :
    s (⋃ b ∈ t, f b) = ∑ b ∈ t, s (f b) :=
  VectorMeasure.of_biUnion_finset (v := s) hd hm

/-- **有符号测度：下连续**。单调可测集列 `f n ↑` 满足 `s (f n) → s (⋃ n, f n)`。
教材记号的“测度下连续性”（有符号测度保持不交可加，故下连续成立）。
> **Entry**: real-analysis.signed-measure.definition
@isnad1 id=tendsto.2h3v.s6.3558360af67f from=translated src=- shape=e6730596 vocab=decc2fab
-/
theorem signedMeasure_tendsto_iUnion (s : SignedMeasure α) {f : ℕ → Set α} (hm : Monotone f)
    (hf : ∀ n, MeasurableSet (f n)) :
    Tendsto (fun n ↦ s (f n)) atTop (𝓝 (s (⋃ n, f n))) :=
  VectorMeasure.tendsto_vectorMeasure_iUnion_atTop_nat (v := s) hm hf

/-! ## 2. 正测度 → 有符号测度的桥 -/

/-- **由有限正测度构造有符号测度（可测形式）**：`(μ.toSignedMeasure) i = μ.real i`（`i` 可测）。
> **Entry**: real-analysis.signed-measure.definition
@isnad1 id=eq.1h3v.s5.d2647ab01fff from=translated src=- shape=a68d0310 vocab=ad5723fc
-/
theorem measure_toSignedMeasure_apply_measurable (μ : Measure α) [IsFiniteMeasure μ]
    {i : Set α} (hi : MeasurableSet i) : μ.toSignedMeasure i = μ.real i :=
  Measure.toSignedMeasure_apply_measurable hi

/-- **正测度加法与有符号测度加法相容**：`(μ + ν).toSignedMeasure = μ.toSignedMeasure + ν.toSignedMeasure`。
> **Entry**: real-analysis.signed-measure.definition
@isnad1 id=eq.0h3v.s6.4b5fd87bdb16 from=translated src=- shape=563f7827 vocab=0fd188be
-/
theorem measure_toSignedMeasure_add (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (μ + ν).toSignedMeasure = μ.toSignedMeasure + ν.toSignedMeasure :=
  Measure.toSignedMeasure_add μ ν

/-- **零测度对应零有符号测度**：`(0 : Measure α).toSignedMeasure = 0`。
> **Entry**: real-analysis.signed-measure.definition
@isnad1 id=eq.0h1v.s5.62c8c641ec93 from=translated src=- shape=ce6ce14d vocab=3a1b1750
-/
theorem measure_toSignedMeasure_zero : (Measure.toSignedMeasure (0 : Measure α)) = 0 :=
  Measure.toSignedMeasure_zero

/-! ## 3. 正集、负集、零集（课程量词定义与桥） -/

/-- **正集**（Folland 3.1）：可测集 `i`，且任意可测子集 `j ⊆ i` 满足 `0 ≤ s j`。
课程用显式 `∀` 量词陈述；Mathlib 侧的对应物是限制序 `0 ≤[i] s`，桥见
`isPositiveSet_iff_zero_le_restrict`。
> **Entry**: real-analysis.signed-measure.definition-/
def IsPositiveSet (s : SignedMeasure α) (i : Set α) : Prop :=
  MeasurableSet i ∧ ∀ ⦃j : Set α⦄, MeasurableSet j → j ⊆ i → 0 ≤ s j

/-- **负集**（Folland 3.1）：可测集 `i`，且任意可测子集 `j ⊆ i` 满足 `s j ≤ 0`。
> **Entry**: real-analysis.signed-measure.definition-/
def IsNegativeSet (s : SignedMeasure α) (i : Set α) : Prop :=
  MeasurableSet i ∧ ∀ ⦃j : Set α⦄, MeasurableSet j → j ⊆ i → s j ≤ 0

/-- **零集**（Folland 3.1）：可测集 `i`，且任意可测子集 `j ⊆ i` 满足 `s j = 0`。
> **Entry**: real-analysis.signed-measure.definition-/
def IsNullSet (s : SignedMeasure α) (i : Set α) : Prop :=
  MeasurableSet i ∧ ∀ ⦃j : Set α⦄, MeasurableSet j → j ⊆ i → s j = 0

/-- **正集的 Mathlib 桥**：对可测集 `i`，课程量词定义 `IsPositiveSet s i` 与限制序
`0 ≤[i] s`（即 `VectorMeasure.restrict` 意义下 `s` 在 `i` 上非负）等价。
这是本库课程定义与 Mathlib 接口之间的双向具名桥。
> **Entry**: real-analysis.signed-measure.definition
@isnad1 id=iff.1h3v.s6.3160807ef9c0 from=translated src=- shape=4fc953fb vocab=a636fb77
-/
theorem isPositiveSet_iff_zero_le_restrict {s : SignedMeasure α} {i : Set α}
    (hi : MeasurableSet i) : IsPositiveSet s i ↔ 0 ≤[i] s := by
  rw [VectorMeasure.restrict_le_restrict_iff (0 : SignedMeasure α) s hi]
  constructor
  · rintro ⟨-, h⟩ j hj hji; simpa using h hj hji
  · intro h; refine ⟨hi, ?_⟩; intro j hj hji; simpa using h hj hji

/-- **负集的 Mathlib 桥**：对可测集 `i`，`IsNegativeSet s i` 与 `s ≤[i] 0` 等价。
> **Entry**: real-analysis.signed-measure.definition
@isnad1 id=iff.1h3v.s6.ad3b3ae16f8d from=translated src=- shape=9447b226 vocab=4fb9c887
-/
theorem isNegativeSet_iff_restrict_le_zero {s : SignedMeasure α} {i : Set α}
    (hi : MeasurableSet i) : IsNegativeSet s i ↔ s ≤[i] 0 := by
  rw [VectorMeasure.restrict_le_restrict_iff s (0 : SignedMeasure α) hi]
  constructor
  · rintro ⟨-, h⟩ j hj hji; simpa using h hj hji
  · intro h; refine ⟨hi, ?_⟩; intro j hj hji; simpa using h hj hji

/-- **零集 = 正集 ∧ 负集**：课程量词下零集恰为同时是正集与负集的集。
> **Entry**: real-analysis.signed-measure.definition
@isnad1 id=iff.0h3v.s4.08eb9e9c0b57 from=translated src=- shape=26a5e60e vocab=559f37e6
-/
theorem isNullSet_iff_isPositiveSet_and_isNegativeSet {s : SignedMeasure α} {i : Set α} :
    IsNullSet s i ↔ IsPositiveSet s i ∧ IsNegativeSet s i := by
  constructor
  · intro h
    exact ⟨⟨h.1, fun _ hj hji => le_of_eq (h.2 hj hji).symm⟩,
      ⟨h.1, fun _ hj hji => le_of_eq (h.2 hj hji)⟩⟩
  · rintro ⟨⟨hi, hp⟩, -, hn⟩
    exact ⟨hi, fun _ hj hji => le_antisymm (hn hj hji) (hp hj hji)⟩

/-- **正集的单调性**：正集的可测子集仍是正集。
> **Entry**: real-analysis.signed-measure.definition
@isnad1 id=ispositi.3h4v.s5.d59e99e34190 from=translated src=- shape=abb575aa vocab=5c0d92cd
-/
theorem IsPositiveSet.mono {s : SignedMeasure α} {i j : Set α} (hi : IsPositiveSet s i)
    (hj : MeasurableSet j) (hji : j ⊆ i) : IsPositiveSet s j :=
  ⟨hj, fun _ hk hkj => hi.2 hk (hkj.trans hji)⟩

/-- **负集的单调性**：负集的可测子集仍是负集。
> **Entry**: real-analysis.signed-measure.definition
@isnad1 id=isnegati.3h4v.s5.0b83b78f610a from=translated src=- shape=abb575aa vocab=1087cdc8
-/
theorem IsNegativeSet.mono {s : SignedMeasure α} {i j : Set α} (hi : IsNegativeSet s i)
    (hj : MeasurableSet j) (hji : j ⊆ i) : IsNegativeSet s j :=
  ⟨hj, fun _ hk hkj => hi.2 hk (hkj.trans hji)⟩

/-- **零集的单调性**：零集的可测子集仍是零集。
> **Entry**: real-analysis.signed-measure.definition
@isnad1 id=isnullse.3h4v.s5.f483f6fc82a6 from=translated src=- shape=abb575aa vocab=804097d7
-/
theorem IsNullSet.mono {s : SignedMeasure α} {i j : Set α} (hi : IsNullSet s i)
    (hj : MeasurableSet j) (hji : j ⊆ i) : IsNullSet s j :=
  ⟨hj, fun _ hk hkj => hi.2 hk (hkj.trans hji)⟩

/-- **可数个正集之并仍为正集**（Folland 引理 3.2 的要素）。这里用 `ℕ` 索引陈述；
证明先把 `k ∩ f n` 不交化（`disjointed`），再用有符号测度的可数可加性与级数非负性。
这是 `IsPositiveSet` 课程定义的真实使用者，不是装饰别名。
> **Entry**: real-analysis.signed-measure.definition
@isnad1 id=ispositi.1h3v.s5.68865ce8675a from=translated src=- shape=509c6882 vocab=548f9721
-/
theorem IsPositiveSet.iUnion {s : SignedMeasure α} {f : ℕ → Set α}
    (hf : ∀ n, IsPositiveSet s (f n)) : IsPositiveSet s (⋃ n, f n) := by
  refine ⟨MeasurableSet.iUnion fun n => (hf n).1, ?_⟩
  intro k hk hkU
  have hbase : ∀ n, MeasurableSet (k ∩ f n) := fun n => hk.inter (hf n).1
  have hkUnion : (⋃ n, (k ∩ f n)) = k := by
    rw [← Set.inter_iUnion, Set.inter_eq_left.mpr hkU]
  set g : ℕ → Set α := disjointed (fun n => k ∩ f n) with hg_def
  have hgmeas : ∀ n, MeasurableSet (g n) := fun n => MeasurableSet.disjointed hbase n
  have hgdisj : Pairwise (Disjoint on g) := disjoint_disjointed _
  have hgunion : (⋃ n, g n) = k := by
    rw [hg_def, iUnion_disjointed]; exact hkUnion
  have hsum : HasSum (fun n => s (g n)) (s k) := by
    have := s.hasSum_of_disjoint_iUnion hgmeas hgdisj
    rwa [hgunion] at this
  rw [← hsum.tsum_eq]
  exact tsum_nonneg (fun n => (hf n).2 (hgmeas n)
    ((disjointed_subset (fun n => k ∩ f n) n).trans Set.inter_subset_right))

/-- **可数个负集之并仍为负集**。对偶于 `IsPositiveSet.iUnion`，用级数非正性。
> **Entry**: real-analysis.signed-measure.definition
@isnad1 id=isnegati.1h3v.s5.ed2d888b0267 from=translated src=- shape=509c6882 vocab=f8ea5f03
-/
theorem IsNegativeSet.iUnion {s : SignedMeasure α} {f : ℕ → Set α}
    (hf : ∀ n, IsNegativeSet s (f n)) : IsNegativeSet s (⋃ n, f n) := by
  refine ⟨MeasurableSet.iUnion fun n => (hf n).1, ?_⟩
  intro k hk hkU
  have hbase : ∀ n, MeasurableSet (k ∩ f n) := fun n => hk.inter (hf n).1
  have hkUnion : (⋃ n, (k ∩ f n)) = k := by
    rw [← Set.inter_iUnion, Set.inter_eq_left.mpr hkU]
  set g : ℕ → Set α := disjointed (fun n => k ∩ f n) with hg_def
  have hgmeas : ∀ n, MeasurableSet (g n) := fun n => MeasurableSet.disjointed hbase n
  have hgdisj : Pairwise (Disjoint on g) := disjoint_disjointed _
  have hgunion : (⋃ n, g n) = k := by
    rw [hg_def, iUnion_disjointed]; exact hkUnion
  have hsum : HasSum (fun n => s (g n)) (s k) := by
    have := s.hasSum_of_disjoint_iUnion hgmeas hgdisj
    rwa [hgunion] at this
  rw [← hsum.tsum_eq]
  exact tsum_nonpos (fun n => (hf n).2 (hgmeas n)
    ((disjointed_subset (fun n => k ∩ f n) n).trans Set.inter_subset_right))

/-- **Hahn 分解（存在性）**：任意有符号测度都存在可测正集 `P`，其补集 `Pᶜ` 为负集。
由 Mathlib 的 `SignedMeasure.exists_compl_positive_negative` 经本库正／负集桥得到，
是 Jordan 分解与正／负变差构造的教材入口。
> **Entry**: real-analysis.signed-measure.definition
@isnad1 id=ex.0h2v.s4.b0dbf0506b6e from=translated src=- shape=8e1f0ca5 vocab=75912f59
-/
theorem exists_hahnDecomposition (s : SignedMeasure α) :
    ∃ P : Set α, IsPositiveSet s P ∧ IsNegativeSet s Pᶜ := by
  obtain ⟨P, hP, hpos, hneg⟩ := s.exists_compl_positive_negative
  exact ⟨P, (isPositiveSet_iff_zero_le_restrict hP).2 hpos,
    (isNegativeSet_iff_restrict_le_zero hP.compl).2 hneg⟩

end RealAnalysis.SignedMeasure

end SandronesLibrary
