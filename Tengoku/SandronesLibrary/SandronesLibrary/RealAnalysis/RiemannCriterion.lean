import Tengoku
import Tengoku.SandronesLibrary.SandronesLibrary.RealAnalysis.Riemann

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# RealAnalysis / RiemannCriterion —— Lebesgue 判据

本模块只补充 Lebesgue 判据所需的测度论证明；Riemann 积分的基础对象全部复用
`RealAnalysis.Riemann`：`DarbouxPartition`、`upperSum`、`lowerSum`、
`RiemannIntegrable` 与 `riemannIntegral` 不在本文件重新定义。

证明架构分成两条链：

* 正向链：上下和差小 → 每个正振荡层由有限个坏区间覆盖 → 坏区间总长度受上下和差控制
  → 每个正振荡层零测 → 可数层推出几乎处处连续；
* 反向链：几乎处处连续 → 例外零测集的开覆盖 + 连续部分有限局部覆盖
  → 构造 Darboux 分割 → 坏区间和与好区间振幅和各小于误差的一半。

文件中的 `RiemannIntegrableWithBound` 是“有界 + Riemann.lean 中的
`RiemannIntegrable`”的组合接口。这样既保持与现有积分定义严格对齐，也显式保留
Lebesgue 判据所需的有界性假设。
-/

namespace SandronesLibrary

namespace RealAnalysis.Riemann

open MeasureTheory

/-!
Todo list for the proof:

0. **定义层修正**：当前库内 `RiemannIntegrable` 只写上下和差，未显式要求有界；
   临时接口 `RiemannIntegrableWithBound` 先把标准定义固定为“有界 + 上下和可任意逼近”。
1. ✅ `riemannIntegrableWithBound_boundedOn`: 从标准定义直接提取 `BoundedOn`。
2. `riemannIntegrableWithBound_ae_continuousOn`: every positive oscillation layer has zero measure.
   2a. ✅ `positiveLayer_subset_badIntervals`: layer coverage after removing partition points.
   2b. ✅ `badIntervals_length_le_upper_sub_lower`: bad interval length is controlled by
       the Darboux upper-minus-lower sum.
   2c. ✅ `positiveOscillationLayer_null`: each fixed layer is assembled from 2a, 2b,
       and `finite_partition_points_null`.
   2d. `ae_oscillationWithin_eq_zero_of_layers_null`: the countable layer argument.
3. `boundedOn_ae_continuousOn_riemannIntegrableWithBound`: finite-cover control on the continuous part
   plus a null-set open cover controls the Darboux oscillation.
4. ✅ Assemble the two directions; the verified source file is fully proved.

当前文件中的 TODO 清单保留为证明导航；每个条目对应下方已经完成并可复用的引理链。
-/

/-- **几乎处处连续（区间版）**：除去一个 Lebesgue 零测集后，函数在闭区间内连续。
  这里使用 `volume.restrict (Icc a b)`，因此“几乎处处”只在研究区间内解释。-/
def AlmostEverywhereContinuousOn (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ᵐ x ∂volume.restrict (Set.Icc a b), ContinuousWithinAt f (Set.Icc a b) x

/- **有界性接口**：Lebesgue 判据的教材版本把有界性作为独立前提；
  `Riemann.lean` 中的 `RiemannIntegrable` 负责上下和逼近，本文件把二者组合起来。 -/
def BoundedOn (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∃ C : ℝ, ∀ x ∈ s, |f x| ≤ C

/- **带有界性的黎曼可积接口**：不是另一个积分定义，而是
  `BoundedOn` 与 `RiemannIntegrable` 的合取，供判据两方向统一使用。 -/
def RiemannIntegrableWithBound (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  BoundedOn f (Set.Icc a b) ∧ RiemannIntegrable f a b

/- **证明路线 A：把函数有界性传给振荡定义**。
  后续 `oscillationWithin` 使用 `Metric.ediam`，所以先把实值有界性转成
  `Bornology.IsBounded (f '' Icc)`，再得到振荡不为 `⊤`。 -/
/--
@isnad1 id=isbounde.2h3v.s5.d5d02a9d00a6 from=translated src=- shape=bd3a3324 vocab=aa837581
-/
theorem boundedOn_image_isBounded {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hb : BoundedOn f (Set.Icc a b)) :
    Bornology.IsBounded (f '' Set.Icc a b) := by
  rcases hb with ⟨C, hC⟩
  have hC0 : 0 ≤ C := by
    have ha := hC a ⟨le_rfl, hab⟩
    exact le_trans (abs_nonneg (f a)) ha
  rw [Metric.isBounded_iff]
  refine ⟨2 * C, ?_⟩
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  rw [Real.dist_eq]
  rw [abs_le]
  have hx' := (abs_le.mp (hC x hx)).2
  have hx'' := (abs_le.mp (hC x hx)).1
  have hy' := (abs_le.mp (hC y hy)).2
  have hy'' := (abs_le.mp (hC y hy)).1
  constructor <;> linarith [hC0]

/--
@isnad1 id=lt.3h4v.s6.159c70b74ee1 from=translated src=- shape=797d53f9 vocab=d6c57570
-/
theorem oscillationWithin_lt_top_of_boundedOn {f : ℝ → ℝ} {a b x : ℝ}
    (hab : a ≤ b) (hx : x ∈ Set.Icc a b) (hb : BoundedOn f (Set.Icc a b)) :
    oscillationWithin f (Set.Icc a b) x < ⊤ := by
  have hbounded : Bornology.IsBounded (f '' Set.Icc a b) :=
    boundedOn_image_isBounded hab hb
  have hmem : f '' Set.Icc a b ∈
      (nhdsWithin x (Set.Icc a b)).map f := by
    rw [Filter.mem_map]
    apply Filter.mem_of_superset self_mem_nhdsWithin
    intro y hy
    exact ⟨y, hy, rfl⟩
  have hle : oscillationWithin f (Set.Icc a b) x ≤
      Metric.ediam (f '' Set.Icc a b) := by
    rw [oscillationWithin]
    exact iInf_le_of_le (f '' Set.Icc a b) (iInf_le_of_le hmem le_rfl)
  exact lt_of_le_of_lt hle (lt_top_iff_ne_top.mpr hbounded.ediam_ne_top)

/--
@isnad1 id=ex.2h1v.s6.b46ab490d13a from=translated src=- shape=f465f425 vocab=e0a3dcb7
-/
theorem positive_threshold_exists {r : ENNReal} (hr0 : 0 < r) (hrt : r < ⊤) :
    ∃ n : ℕ, ENNReal.ofReal (1 / (n + 1 : ℝ)) ≤ r := by
  have hr0' : r ≠ 0 := ne_of_gt hr0
  have hrt' : r ≠ ⊤ := ne_of_lt hrt
  have htr : 0 < r.toReal := ENNReal.toReal_pos hr0' hrt'
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / r.toReal)
  have hn0 : 0 < (n : ℝ) := by
    have : 0 < (1 / r.toReal) := by positivity
    exact lt_of_lt_of_le this (le_of_lt hn)
  refine ⟨n, ?_⟩
  rw [ENNReal.ofReal_le_iff_le_toReal hrt']
  calc
    1 / (n + 1 : ℝ) ≤ 1 / (n : ℝ) := by
      apply one_div_le_one_div_of_le hn0
      linarith
    _ ≤ r.toReal := by
      have hmul := (div_lt_iff₀ htr).mp hn
      have hstrict : 1 / (n : ℝ) < r.toReal := by
        apply (div_lt_iff₀ hn0).2
        simpa [mul_comm] using hmul
      exact hstrict.le

/--
@isnad1 id=eq.0h3v.s5.d801c745309d from=translated src=- shape=c44aeb47 vocab=f69381f2
-/
theorem finite_partition_points_null {a b : ℝ} (P : DarbouxPartition a b) :
    volume {x : ℝ | ∃ i ≤ P.n, x = P.x i} = 0 := by
  have hfinite : Set.Finite {x : ℝ | ∃ i ≤ P.n, x = P.x i} := by
    refine Set.Finite.subset (Set.Finite.image P.x (Set.Iic P.n).toFinite) ?_
    intro x hx
    rcases hx with ⟨i, hi, rfl⟩
    exact ⟨i, Set.mem_Iic.mpr hi, rfl⟩
  exact hfinite.measure_zero volume

/--
@isnad1 id=boundedo.1h3v.s4.d5bb1154923c from=translated src=- shape=e1ddc50d vocab=4430cee4
-/
theorem riemannIntegrableWithBound_boundedOn {f : ℝ → ℝ} {a b : ℝ} :
    RiemannIntegrableWithBound f a b → BoundedOn f (Set.Icc a b) := by
  intro h
  exact h.1

/--
@isnad1 id=iff.0h3v.s6.cf522a225115 from=translated src=- shape=4283195f vocab=04a75042
-/
theorem ae_continuousOn_iff_ae_oscillationWithin_eq_zero {f : ℝ → ℝ} {a b : ℝ} :
    AlmostEverywhereContinuousOn f a b ↔
      ∀ᵐ x ∂volume.restrict (Set.Icc a b),
        oscillationWithin f (Set.Icc a b) x = 0 := by
  constructor
  · intro h
    filter_upwards [h, ae_restrict_mem measurableSet_Icc] with x hx hxmem
    exact (OscillationWithin.eq_zero_iff_continuousWithinAt
      (f := f) (D := Set.Icc a b) (x := x) hxmem).2 hx
  · intro h
    filter_upwards [h, ae_restrict_mem measurableSet_Icc] with x hx hxmem
    exact (OscillationWithin.eq_zero_iff_continuousWithinAt
      (f := f) (D := Set.Icc a b) (x := x) hxmem).1 hx

/- **正振荡层**：集合 `{x ∈ [a,b] | ε ≤ oscillationWithin f [a,b] x}`。
  若每个正层都是零测，取阈值 `1/(n+1)` 的可数并，就能推出振荡几乎处处为零。 -/
def positiveOscillationLayer (f : ℝ → ℝ) (a b : ℝ) (ε : ℝ) : Set ℝ :=
  {x ∈ Set.Icc a b | (ENNReal.ofReal ε) ≤ oscillationWithin f (Set.Icc a b) x}

/--
@isnad1 id=le.5h5v.s6.958a28d46ad8 from=translated src=- shape=cce034d9 vocab=141beed7
-/
theorem subinterval_oscillation_nonneg {f : ℝ → ℝ} {a b p q : ℝ}
    (hab : a ≤ b) (hpq : p ≤ q) (hp : p ∈ Set.Icc a b) (hq : q ∈ Set.Icc a b)
    (hb : BoundedOn f (Set.Icc a b)) :
    0 ≤ sSup (f '' Set.Icc p q) - sInf (f '' Set.Icc p q) := by
  rcases hb with ⟨C, hC⟩
  have hne : (f '' Set.Icc p q).Nonempty := ⟨f p, ⟨p, ⟨le_rfl, hpq⟩, rfl⟩⟩
  have hbelow : BddBelow (f '' Set.Icc p q) := by
    refine ⟨-C, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact (abs_le.mp (hC x (Set.Icc_subset_Icc hp.1 hq.2 hx))).1
  have habove : BddAbove (f '' Set.Icc p q) := by
    refine ⟨C, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact (abs_le.mp (hC x (Set.Icc_subset_Icc hp.1 hq.2 hx))).2
  exact sub_nonneg.mpr (csInf_le_csSup hne hbelow habove)

/--
@isnad1 id=le.3h5v.s6.d1a2014bca32 from=translated src=- shape=9442bbcf vocab=7f315b58
-/
theorem partition_oscillation_nonneg {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hb : BoundedOn f (Set.Icc a b))
    (P : DarbouxPartition a b) :
    ∀ i ∈ Finset.range P.n, 0 ≤
      sSup (f '' Set.Icc (P.x i) (P.x (i + 1))) -
        sInf (f '' Set.Icc (P.x i) (P.x (i + 1))) := by
  intro i hi
  have hi_lt : i < P.n := Finset.mem_range.mp hi
  have hpi : P.x i ∈ Set.Icc a b :=
    partition_point_mem hab P.x0 P.xN P.strict (le_of_lt hi_lt)
  have hpi1 : P.x (i + 1) ∈ Set.Icc a b :=
    partition_point_mem hab P.x0 P.xN P.strict (Nat.succ_le_of_lt hi_lt)
  exact subinterval_oscillation_nonneg hab (P.strict i hi_lt).le hpi hpi1 hb

/--
@isnad1 id=le.5h5v.s7.4febb32d440d from=translated src=- shape=9d7a398d vocab=5b74df2a
-/
theorem subinterval_ediam_le_of_boundedOn {f : ℝ → ℝ} {a b p q : ℝ}
    (hab : a ≤ b) (hpq : p ≤ q) (hp : p ∈ Set.Icc a b) (hq : q ∈ Set.Icc a b)
    (hb : BoundedOn f (Set.Icc a b)) :
    Metric.ediam (f '' Set.Icc p q) ≤
      ENNReal.ofReal (sSup (f '' Set.Icc p q) - sInf (f '' Set.Icc p q)) := by
  rcases hb with ⟨C, hC⟩
  have hbelow : BddBelow (f '' Set.Icc p q) := by
    refine ⟨-C, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact (abs_le.mp (hC x (Set.Icc_subset_Icc hp.1 hq.2 hx))).1
  have habove : BddAbove (f '' Set.Icc p q) := by
    refine ⟨C, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact (abs_le.mp (hC x (Set.Icc_subset_Icc hp.1 hq.2 hx))).2
  apply Metric.ediam_le
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  rw [edist_dist]
  apply ENNReal.ofReal_le_ofReal
  rw [Real.dist_eq, abs_le]
  have hxlo := csInf_le hbelow ⟨x, hx, rfl⟩
  have hxhi := le_csSup habove ⟨x, hx, rfl⟩
  have hylo := csInf_le hbelow ⟨y, hy, rfl⟩
  have hyhi := le_csSup habove ⟨y, hy, rfl⟩
  constructor <;> linarith

/- **坏区间索引**：Darboux 分割中振幅至少为 `ε` 的那些区间。
  正向证明的核心估计是“坏区间长度和 × ε ≤ 上和 − 下和”。 -/
noncomputable def badPartitionIndices (f : ℝ → ℝ) (P : DarbouxPartition a b) (ε : ℝ) : Finset ℕ :=
  (Finset.range P.n).filter (fun i ↦
      ε ≤ sSup (f '' Set.Icc (P.x i) (P.x (i + 1))) -
        sInf (f '' Set.Icc (P.x i) (P.x (i + 1))))

/--
@isnad1 id=le.2h4v.s6.65db9d96fa99 from=translated src=- shape=f5037333 vocab=7e52d4e0
-/
theorem oscillationWithin_le_subinterval_ediam {f : ℝ → ℝ} {p q x : ℝ}
    (hpq : p ≤ q) (hx : x ∈ Set.Icc p q) :
    oscillationWithin f (Set.Icc p q) x ≤ Metric.ediam (f '' Set.Icc p q) := by
  have hmem : f '' Set.Icc p q ∈ (nhdsWithin x (Set.Icc p q)).map f := by
    rw [Filter.mem_map]
    apply Filter.mem_of_superset self_mem_nhdsWithin
    intro y hy
    exact ⟨y, hy, rfl⟩
  rw [oscillationWithin]
  exact iInf_le_of_le (f '' Set.Icc p q) (iInf_le_of_le hmem le_rfl)

/--
@isnad1 id=ex.3h4v.s6.ca8687183fad from=translated src=- shape=cd4d3544 vocab=6fde4e61
-/
theorem partition_cover_off_points {a b : ℝ} (hab : a ≤ b)
    (P : DarbouxPartition a b) {x : ℝ} (hx : x ∈ Set.Icc a b)
    (hnot : x ∉ {y : ℝ | ∃ i ≤ P.n, y = P.x i}) :
    ∃ i, i < P.n ∧ x ∈ Set.Ioc (P.x i) (P.x (i + 1)) := by
  have hxa : a < x := by
    by_contra h
    have hxa' : x = a := le_antisymm (le_of_not_gt h) hx.1
    apply hnot
    refine ⟨0, Nat.zero_le _, ?_⟩
    simpa [P.x0] using hxa'
  have hxioc : x ∈ Set.Ioc a b := ⟨hxa, hx.2⟩
  exact partition_cover P.x0 P.xN P.strict hxioc

/- **正向链的覆盖步骤**：去掉有限个分割点后，每个正振荡层点落在一个坏半开区间内。 -/
/--
@isnad1 id=le.3h5v.s7.82727271acc7 from=translated src=- shape=b6ab059a vocab=cbc55146
-/
theorem positiveLayer_subset_badIntervals {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hb : BoundedOn f (Set.Icc a b))
    (P : DarbouxPartition a b) {ε : ℝ} (hε : 0 < ε) :
    positiveOscillationLayer f a b ε \ {x : ℝ | ∃ i ≤ P.n, x = P.x i} ⊆
      ⋃ i ∈ badPartitionIndices f P ε,
        Set.Ioc (P.x i) (P.x (i + 1)) := by
  intro x hx
  rcases hx with ⟨hxlayer, hxnot⟩
  rcases partition_cover_off_points hab P hxlayer.1 hxnot with ⟨i, hi, hxi⟩
  have hright : x < P.x (i + 1) := by
    apply lt_of_le_of_ne hxi.2
    intro heq
    apply hxnot
    exact ⟨i + 1, Nat.succ_le_of_lt hi, heq⟩
  have hsubnhds : Set.Icc (P.x i) (P.x (i + 1)) ∈ nhds x :=
    Icc_mem_nhds hxi.1 hright
  have hfullnhds : Set.Icc a b ∈ nhds x := by
    apply Icc_mem_nhds
    · exact lt_of_le_of_lt (partition_point_mem hab P.x0 P.xN P.strict
        (Nat.le_of_lt hi)).1 hxi.1
    · exact lt_of_lt_of_le hright (partition_point_mem hab P.x0 P.xN P.strict
        (Nat.succ_le_of_lt hi)).2
  have hosc_eq :
      oscillationWithin f (Set.Icc a b) x =
        oscillationWithin f (Set.Icc (P.x i) (P.x (i + 1))) x := by
    rw [oscillationWithin_nhds_eq_oscillation f _ x hfullnhds,
      oscillationWithin_nhds_eq_oscillation f _ x hsubnhds]
  have hupper := subinterval_ediam_le_of_boundedOn hab
      (P.strict i hi).le
      (partition_point_mem hab P.x0 P.xN P.strict (Nat.le_of_lt hi))
      (partition_point_mem hab P.x0 P.xN P.strict (Nat.succ_le_of_lt hi)) hb
  have hosc := oscillationWithin_le_subinterval_ediam (f := f)
      (P.strict i hi).le ⟨hxi.1.le, hright.le⟩
  have hthreshold : ENNReal.ofReal ε ≤
      ENNReal.ofReal (sSup (f '' Set.Icc (P.x i) (P.x (i + 1))) -
        sInf (f '' Set.Icc (P.x i) (P.x (i + 1)))) := by
    rw [← hosc_eq] at hosc
    exact hxlayer.2.trans (hosc.trans hupper)
  have hreal : ε ≤ sSup (f '' Set.Icc (P.x i) (P.x (i + 1))) -
      sInf (f '' Set.Icc (P.x i) (P.x (i + 1))) := by
    apply (ENNReal.ofReal_le_ofReal_iff (partition_oscillation_nonneg hab hb P i
      (Finset.mem_range.mpr hi))).mp
    exact hthreshold
  refine Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨?_, hxi⟩⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, hreal⟩

/--
@isnad1 id=le.3h5v.s6.134cca57e7d8 from=translated src=- shape=7bfdbf97 vocab=9fafea2a
-/
theorem badIntervals_length_le_upper_sub_lower {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hb : BoundedOn f (Set.Icc a b))
    (P : DarbouxPartition a b) {ε : ℝ} (hε : 0 < ε) :
    (∑ i ∈ badPartitionIndices f P ε, (P.x (i + 1) - P.x i)) * ε ≤
      upperSum f P - lowerSum f P := by
  let g : ℕ → ℝ := fun i ↦
    (P.x (i + 1) - P.x i) *
      (sSup (f '' Set.Icc (P.x i) (P.x (i + 1))) -
        sInf (f '' Set.Icc (P.x i) (P.x (i + 1))))
  have hdiff : upperSum f P - lowerSum f P =
      ∑ i ∈ Finset.range P.n, g i := by
    unfold g upperSum lowerSum
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hbad : (∑ i ∈ badPartitionIndices f P ε, g i) ≤
      ∑ i ∈ Finset.range P.n, g i := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _)
    intro i hi hnot
    have hi' : i < P.n := Finset.mem_range.mp hi
    have hstep : 0 ≤ P.x (i + 1) - P.x i :=
      sub_nonneg.mpr (P.strict i hi').le
    have hosc := partition_oscillation_nonneg hab hb P i hi
    exact mul_nonneg hstep hosc
  have hterm : (∑ i ∈ badPartitionIndices f P ε,
      (P.x (i + 1) - P.x i) * ε) ≤
      ∑ i ∈ badPartitionIndices f P ε, g i := by
    apply Finset.sum_le_sum
    intro i hi
    have hi' := (Finset.mem_filter.mp hi).2
    have hirange := (Finset.mem_filter.mp hi).1
    have hstep : 0 ≤ P.x (i + 1) - P.x i :=
      sub_nonneg.mpr (P.strict i (Finset.mem_range.mp hirange)).le
    exact mul_le_mul_of_nonneg_left hi' hstep
  calc
    (∑ i ∈ badPartitionIndices f P ε, (P.x (i + 1) - P.x i)) * ε =
        ∑ i ∈ badPartitionIndices f P ε, (P.x (i + 1) - P.x i) * ε := by
      rw [← Finset.sum_mul]
    _ ≤ ∑ i ∈ badPartitionIndices f P ε, g i := hterm
    _ ≤ ∑ i ∈ Finset.range P.n, g i := hbad
    _ = upperSum f P - lowerSum f P := hdiff.symm

/--
@isnad1 id=le.3h5v.s6.3e81f0ea1ae9 from=translated src=- shape=98a50273 vocab=461695dd
-/
theorem positiveLayer_measure_le_of_partition {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hb : BoundedOn f (Set.Icc a b))
    (P : DarbouxPartition a b) {ε : ℝ} (hε : 0 < ε) :
    volume (positiveOscillationLayer f a b ε) ≤
      ENNReal.ofReal (∑ i ∈ badPartitionIndices f P ε,
        (P.x (i + 1) - P.x i)) := by
  let points : Set ℝ := {x : ℝ | ∃ i ≤ P.n, x = P.x i}
  let bad : Set ℝ := ⋃ i ∈ badPartitionIndices f P ε,
    Set.Ioc (P.x i) (P.x (i + 1))
  have hsubset : positiveOscillationLayer f a b ε ⊆ points ∪ bad := by
    intro x hx
    by_cases hpoint : x ∈ points
    · exact Or.inl hpoint
    · exact Or.inr (positiveLayer_subset_badIntervals hab hb P hε ⟨hx, hpoint⟩)
  have hpoints : volume points = 0 := by
    exact finite_partition_points_null P
  have hbad : volume bad ≤
      ENNReal.ofReal (∑ i ∈ badPartitionIndices f P ε,
        (P.x (i + 1) - P.x i)) := by
    have hle := measure_biUnion_finset_le (μ := volume)
      (badPartitionIndices f P ε) (fun i ↦ Set.Ioc (P.x i) (P.x (i + 1)))
    calc
      volume bad ≤ ∑ i ∈ badPartitionIndices f P ε,
          volume (Set.Ioc (P.x i) (P.x (i + 1))) := by simpa [bad] using hle
      _ = ∑ i ∈ badPartitionIndices f P ε,
          ENNReal.ofReal (P.x (i + 1) - P.x i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Real.volume_Ioc]
      _ = ENNReal.ofReal (∑ i ∈ badPartitionIndices f P ε,
          (P.x (i + 1) - P.x i)) := by
        rw [← ENNReal.ofReal_sum_of_nonneg]
        intro i hi
        exact sub_nonneg.mpr (P.strict i (Finset.mem_range.mp
          (Finset.mem_filter.mp hi).1)).le
  calc
    volume (positiveOscillationLayer f a b ε) ≤ volume (points ∪ bad) :=
      measure_mono hsubset
    _ ≤ volume points + volume bad := measure_union_le _ _
    _ = volume bad := by rw [hpoints, zero_add]
    _ ≤ ENNReal.ofReal (∑ i ∈ badPartitionIndices f P ε,
        (P.x (i + 1) - P.x i)) := hbad

/- **正向链的零测步骤**：先用覆盖估计测量正层，再用黎曼可积性让坏区间长度趋于零。 -/
/--
@isnad1 id=eq.3h4v.s6.5dd9cd86164b from=translated src=- shape=023401aa vocab=e8866874
-/
theorem positiveOscillationLayer_null {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : RiemannIntegrableWithBound f a b) {ε : ℝ} (hε : 0 < ε) :
    volume (positiveOscillationLayer f a b ε) = 0 := by
  apply le_antisymm
  · apply ENNReal.le_of_forall_pos_le_add
    intro η hη hηtop
    obtain ⟨P, hP⟩ := h.2 ((η : ℝ) * ε) (mul_pos (by exact_mod_cast hη) hε)
    let L : ℝ := ∑ i ∈ badPartitionIndices f P ε,
      (P.x (i + 1) - P.x i)
    have hLε : L * ε ≤ upperSum f P - lowerSum f P := by
      simpa [L] using badIntervals_length_le_upper_sub_lower hab h.1 P hε
    have hL : L ≤ η := by
      have hη' : 0 ≤ (η : ℝ) := by positivity
      have hbound : L * ε < η * ε := lt_of_le_of_lt hLε hP
      nlinarith
    have hmeasure := positiveLayer_measure_le_of_partition hab h.1 P hε
    have hmeasure' : volume (positiveOscillationLayer f a b ε) ≤
      ENNReal.ofReal (η : ℝ) := by
      exact hmeasure.trans (ENNReal.ofReal_le_ofReal hL)
    simpa using hmeasure'
  · exact bot_le

/- **可数层组装**：所有正阈值层的并是零测；层外振荡若为正，必落入某个层，矛盾。 -/
/--
@isnad1 id=eventual.3h3v.s6.037aaacf8695 from=translated src=- shape=0f7f6e91 vocab=24677501
-/
theorem ae_oscillationWithin_eq_zero_of_layers_null {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hb : BoundedOn f (Set.Icc a b))
    (hzero : ∀ {ε : ℝ}, 0 < ε → volume (positiveOscillationLayer f a b ε) = 0) :
    ∀ᵐ x ∂volume.restrict (Set.Icc a b),
      oscillationWithin f (Set.Icc a b) x = 0 := by
  rw [ae_restrict_iff' measurableSet_Icc]
  have hnot : ∀ᵐ x ∂volume,
      x ∉ ⋃ n : ℕ, positiveOscillationLayer f a b (1 / (n + 1 : ℝ)) := by
    rw [ae_iff]
    have hpos : ∀ n : ℕ, 0 < (1 / (n + 1 : ℝ)) := by
      intro n
      apply one_div_pos.mpr
      exact_mod_cast Nat.succ_pos n
    have hU : volume (⋃ n : ℕ,
        positiveOscillationLayer f a b (1 / (n + 1 : ℝ))) = 0 :=
      measure_iUnion_null (fun n => hzero (hpos n))
    have heq : {x : ℝ | ¬ x ∉ ⋃ n : ℕ,
        positiveOscillationLayer f a b (1 / (n + 1 : ℝ))} =
        ⋃ n : ℕ, positiveOscillationLayer f a b (1 / (n + 1 : ℝ)) := by
      ext x
      simp
    rw [heq]
    exact hU
  filter_upwards [hnot] with x hxU hxmem
  by_contra hzero_x
  have hpos : 0 < oscillationWithin f (Set.Icc a b) x := pos_of_ne_zero hzero_x
  have hlt : oscillationWithin f (Set.Icc a b) x < ⊤ :=
    oscillationWithin_lt_top_of_boundedOn hab hxmem hb
  obtain ⟨n, hn⟩ := positive_threshold_exists hpos hlt
  apply hxU
  apply Set.mem_iUnion.mpr
  exact ⟨n, ⟨hxmem, hn⟩⟩

/--
@isnad1 id=ex.1h3v.s6.c7f2bdfb3800 from=translated src=- shape=e60aa4cf vocab=0c871f10
-/
theorem ae_continuity_exceptional_measurable_hull {f : ℝ → ℝ} {a b : ℝ}
    (hc : AlmostEverywhereContinuousOn f a b) :
    ∃ N : Set ℝ, MeasurableSet N ∧
      ({x : ℝ | x ∈ Set.Icc a b ∧ ¬ ContinuousWithinAt f (Set.Icc a b) x} ⊆ N) ∧
      volume N = 0 := by
  change (∀ᵐ x ∂volume.restrict (Set.Icc a b),
    ContinuousWithinAt f (Set.Icc a b) x) at hc
  rw [ae_restrict_iff' measurableSet_Icc, ae_iff] at hc
  have hset : {x : ℝ |
      ¬ (x ∈ Set.Icc a b → ContinuousWithinAt f (Set.Icc a b) x)} =
      {x : ℝ | x ∈ Set.Icc a b ∧
        ¬ ContinuousWithinAt f (Set.Icc a b) x} := by
    ext x
    simp [Set.mem_Icc, and_assoc]
  rw [hset] at hc
  let E : Set ℝ := {x : ℝ | x ∈ Set.Icc a b ∧
    ¬ ContinuousWithinAt f (Set.Icc a b) x}
  refine ⟨toMeasurable volume E, measurableSet_toMeasurable _ _,
    subset_toMeasurable _ _, ?_⟩
  rw [measure_toMeasurable]
  simpa [E] using hc

/--
@isnad1 id=eq.1h3v.s6.1a440365280d from=translated src=- shape=0ced63da vocab=96c08e84
-/
theorem ae_continuity_exceptional_set_null {f : ℝ → ℝ} {a b : ℝ}
    (hc : AlmostEverywhereContinuousOn f a b) :
    volume {x : ℝ | x ∈ Set.Icc a b ∧
      ¬ ContinuousWithinAt f (Set.Icc a b) x} = 0 := by
  change (∀ᵐ x ∂volume.restrict (Set.Icc a b),
    ContinuousWithinAt f (Set.Icc a b) x) at hc
  rw [ae_restrict_iff' measurableSet_Icc, ae_iff] at hc
  have hset : {x : ℝ |
      ¬ (x ∈ Set.Icc a b → ContinuousWithinAt f (Set.Icc a b) x)} =
      {x : ℝ | x ∈ Set.Icc a b ∧
        ¬ ContinuousWithinAt f (Set.Icc a b) x} := by
    ext x
    simp [Set.mem_Icc, and_assoc]
  rw [hset] at hc
  exact hc

/- **反向链第一步**：在例外开集外，连续点的局部邻域覆盖闭区间；紧性把它缩成有限覆盖。 -/
/--
@isnad1 id=ex.3h4v.s7.bf82d14c12c4 from=translated src=- shape=8a8852df vocab=d421fd74
-/
theorem finite_continuity_cover_off_open
    {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (U : Set ℝ)
    (hUopen : IsOpen U)
    (hcont : ∀ x ∈ Set.Icc a b, x ∉ U →
      ContinuousWithinAt f (Set.Icc a b) x) :
    ∃ s : Set ℝ, s.Finite ∧ (∀ x ∈ s, x ∈ Set.Icc a b) ∧
      (∀ x ∈ Set.Icc a b, x ∉ U →
        ∃ y ∈ s, x ∈ Set.Ioo (y - 1) (y + 1)) := by
  let V : ℝ → Set ℝ := fun y ↦ Set.Ioo (y - 1) (y + 1)
  have hopen : ∀ y ∈ Set.Icc a b, IsOpen (V y) := by
    intro y hy
    exact isOpen_Ioo
  have hcover : Set.Icc a b ⊆ ⋃ y ∈ Set.Icc a b, V y := by
    intro x hx
    refine Set.mem_iUnion.2 ⟨x, Set.mem_iUnion.2 ⟨hx, ?_⟩⟩
    simp [V]
  obtain ⟨s, hs, hfinite, hsub⟩ :=
    isCompact_Icc.elim_finite_subcover_image hopen hcover
  refine ⟨s, hfinite, hs, ?_⟩
  intro x hxI hxU
  rcases Set.mem_iUnion.1 (hsub hxI) with ⟨y, hy⟩
  rcases Set.mem_iUnion.1 hy with ⟨hyS, hxy⟩
  exact ⟨y, hyS, hxy⟩

/--
@isnad1 id=ex.3h3v.s6.0cfe94e5e9f4 from=translated src=- shape=62927485 vocab=23cd60b5
-/
theorem compact_uniform_continuity_control
    {f : ℝ → ℝ} {K : Set ℝ} (hK : IsCompact K)
    (hf : ContinuousOn f K) {η : ℝ} (hη : 0 < η) :
    ∃ ρ > 0, ∀ x ∈ K, ∀ y ∈ K, |x - y| < ρ → |f x - f y| < η := by
  have hu : UniformContinuousOn f K :=
    hK.uniformContinuousOn_of_continuous hf
  obtain ⟨ρ, hρ, hρ'⟩ := (Metric.uniformContinuousOn_iff.mp hu) η hη
  refine ⟨ρ, hρ, ?_⟩
  intro x hx y hy hxy
  simpa [Real.dist_eq] using hρ' x hx y hy (by simpa [Real.dist_eq] using hxy)

noncomputable section

local instance propDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/--
@isnad1 id=ex.4h5v.s9.217a69af8ed8 from=translated src=- shape=27cc74bb vocab=627b86bd
-/
theorem finite_local_oscillation_cover
    {f : ℝ → ℝ} {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    (U : Set ℝ) (hUopen : IsOpen U)
    (hlocal : ∀ x ∈ Set.Icc a b, x ∉ U →
      ∃ V, IsOpen V ∧ x ∈ V ∧
        ∀ y ∈ V ∩ Set.Icc a b, ∀ z ∈ V ∩ Set.Icc a b,
        |f y - f z| < δ / (2 * (b - a + 1))) :
    ∃ (s : Set {x // x ∈ Set.Icc a b \ U})
      (V : {x // x ∈ Set.Icc a b \ U} → Set ℝ),
      s.Finite ∧ (∀ y ∈ s, IsOpen (V y) ∧ (y : ℝ) ∈ V y) ∧
      (∀ y ∈ s, ∀ u ∈ V y ∩ Set.Icc a b, ∀ v ∈ V y ∩ Set.Icc a b,
        |f u - f v| < δ / (2 * (b - a + 1))) ∧
      (∀ x ∈ Set.Icc a b, x ∉ U →
        ∃ y ∈ s, x ∈ V y) := by
  classical
  let K : Set ℝ := Set.Icc a b \ U
  have hK : IsCompact K := isCompact_Icc.diff hUopen
  let α := {x // x ∈ K}
  choose W hWopen hWmem hWosc using fun x : α ↦
    hlocal x.1 x.property.1 x.property.2
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : α ↦ W x) (fun x ↦ hWopen x)
    (by intro x hx; exact Set.mem_iUnion.2 ⟨⟨x, hx⟩, hWmem ⟨x, hx⟩⟩)
  refine ⟨(↑t : Set α), W, t.finite_toSet, ?_, ?_, ?_⟩
  · intro y hy

    exact ⟨hWopen y, hWmem y⟩
  · intro y hy u hu v hv
    exact hWosc y u hu v hv
  · intro x hx hxU
    have hxK : x ∈ K := ⟨hx, hxU⟩
    rcases Set.mem_iUnion.1 (ht hxK) with ⟨y, hy⟩
    rcases Set.mem_iUnion.1 hy with ⟨hyT, hxy⟩
    exact ⟨y, hyT, hxy⟩

/- **Lebesgue 数引理**：有限开覆盖给出统一半径 `ρ`，使每个长度小于 `ρ` 的分割区间
  落入某个覆盖成员。 -/
/--
@isnad1 id=ex.5h5v.s9.a8e86fff57d3 from=translated src=- shape=8b591be7 vocab=38446d17
-/
theorem finite_open_cover_has_lebesgue_number
    {a b : ℝ} (hab : a ≤ b) (U : Set ℝ)
    (hUopen : IsOpen U)
    (s : Set {x // x ∈ Set.Icc a b \ U}) (hs : s.Finite)
    (V : {x // x ∈ Set.Icc a b \ U} → Set ℝ)
    (hVopen : ∀ y ∈ s, IsOpen (V y))
    (hcover : (Set.Icc a b) ⊆ U ∪ ⋃ y ∈ s, V y) :
    ∃ ρ > 0, ∀ x ∈ Set.Icc a b, ∃ W ∈ ({U} ∪ V '' s),
      Set.Icc (x - ρ) (x + ρ) ∩ Set.Icc a b ⊆ W := by
  have hcover' : Set.Icc a b ⊆ ⋃₀ ({U} ∪ V '' s) := by
    intro x hx
    rcases hcover hx with hxU | hxV
    · exact Set.mem_sUnion.2 ⟨U, by simp, hxU⟩
    · rcases Set.mem_iUnion.1 hxV with ⟨y, hy⟩
      rcases Set.mem_iUnion.1 hy with ⟨hys, hxy⟩
      exact Set.mem_sUnion.2 ⟨V y, Or.inr ⟨y, hys, rfl⟩, hxy⟩
  have hopen : ∀ W ∈ ({U} ∪ V '' s), IsOpen W := by
    intro W hW
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_image] at hW
    rcases hW with rfl | ⟨y, hys, rfl⟩
    · exact hUopen
    · exact hVopen y hys
  obtain ⟨r, hr, hball⟩ := lebesgue_number_lemma_of_metric_sUnion
    isCompact_Icc hopen hcover'
  refine ⟨r / 2, half_pos hr, ?_⟩
  intro x hx
  obtain ⟨W, hW, hsub⟩ := hball x hx
  refine ⟨W, hW, ?_⟩
  intro y hy
  apply hsub
  rw [Metric.mem_ball]
  have hy' : |y - x| < r := by
    rcases hy with ⟨hy1, hy2⟩
    rw [abs_lt]
    constructor <;> linarith [hy1.1, hy1.2]
  simpa [dist_comm, Real.dist_eq, abs_sub_comm] using hy'

/--
@isnad1 id=ex.2h3v.s6.ab0ee82c03ab from=translated src=- shape=335f7add vocab=e5e24ae5
-/
theorem darboux_partition_with_mesh_lt
    {a b ρ : ℝ} (hab : a ≤ b) (hρ : 0 < ρ) :
    ∃ P : DarbouxPartition a b,
      ∀ i < P.n, P.x (i + 1) - P.x i < ρ := by
  by_cases heq : a = b
  · subst b
    let P : DarbouxPartition a a :=
      { n := 0, x := fun _ ↦ a, x0 := rfl, xN := rfl,
        strict := by intro i hi; omega }
    exact ⟨P, by simp [P]⟩
  · have hab' : a < b := lt_of_le_of_ne hab heq
    obtain ⟨n, hn⟩ := exists_nat_gt ((b - a) / ρ)
    have hnpos : 0 < n := by
      have : 0 < (b - a) / ρ := div_pos (sub_pos.mpr hab') hρ
      have hnreal : 0 < (n : ℝ) := lt_trans this hn
      exact_mod_cast hnreal
    let P := uniformPartition a b n hab' hnpos
    refine ⟨P, ?_⟩
    intro i hi
    rw [uniformPartition_step hab' hnpos i hi]
    apply (div_lt_iff₀ (Nat.cast_pos.mpr hnpos)).2
    have hnrho : b - a < (n : ℝ) * ρ := (div_lt_iff₀ hρ).1 hn
    nlinarith

/- Lower framework TODO 1: classify partition intervals into the exceptional
   part and the finitely covered continuity part.  The upper theorem below
   assembles this interface with the two quantitative estimates. -/
/- **区间分类**：按“整个区间是否落入例外开集”过滤出 `bad/good`，并证明互补、互斥及覆盖语义。 -/
/--
@isnad1 id=ex.7h10v.s9.4d53492fe823 from=translated src=- shape=0cbfce38 vocab=af8ff970
-/
theorem interval_classification_partition
    {f : ℝ → ℝ} {a b C δ ρ : ℝ} (hab : a ≤ b)
    (hb : ∀ x ∈ Set.Icc a b, |f x| ≤ C) (hδ : 0 < δ)
    (U : Set ℝ) (hUmeasure : volume U < ENNReal.ofReal (δ / (4 * (C + 1))))
    (s : Set {x // x ∈ Set.Icc a b \ U})
    (V : {x // x ∈ Set.Icc a b \ U} → Set ℝ)
    (hosc : ∀ y ∈ s, ∀ u ∈ V y ∩ Set.Icc a b, ∀ v ∈ V y ∩ Set.Icc a b,
      |f u - f v| < δ / (2 * (b - a + 1)))
    (P : DarbouxPartition a b)
    (hbad : ∀ i < P.n, (Set.Icc (P.x i) (P.x (i + 1)) ⊆ U) ∨
      ∃ y ∈ s, Set.Icc (P.x i) (P.x (i + 1)) ⊆ V y)
    (hmesh : ∀ i < P.n, P.x (i + 1) - P.x i < ρ) :
    ∃ bad good : Finset ℕ,
      bad ⊆ Finset.range P.n ∧ good ⊆ Finset.range P.n ∧
      Disjoint bad good ∧ bad ∪ good = Finset.range P.n ∧
      (∀ i ∈ bad, Set.Icc (P.x i) (P.x (i + 1)) ⊆ U) ∧
      (∀ i ∈ good, ∃ y ∈ s, Set.Icc (P.x i) (P.x (i + 1)) ⊆ V y) := by
  classical
  let p : ℕ → Prop := fun i => Set.Icc (P.x i) (P.x (i + 1)) ⊆ U
  let bad : Finset ℕ := (Finset.range P.n).filter p
  let good : Finset ℕ := (Finset.range P.n).filter (fun i => ¬ p i)
  have hbad_sub : bad ⊆ Finset.range P.n := by
    exact Finset.filter_subset _ _
  have hgood_sub : good ⊆ Finset.range P.n := by
    exact Finset.filter_subset _ _
  have hdisj : Disjoint bad good := by
    rw [show bad = (Finset.range P.n).filter p by rfl,
      show good = (Finset.range P.n).filter (fun i => ¬ p i) by rfl]
    refine Finset.disjoint_left.2 ?_
    intro i hiBad hiGood
    exact (Finset.mem_filter.1 hiGood).2 ((Finset.mem_filter.1 hiBad).2)
  have hunion : bad ∪ good = Finset.range P.n := by
    rw [show bad = (Finset.range P.n).filter p by rfl,
      show good = (Finset.range P.n).filter (fun i => ¬ p i) by rfl]
    ext i
    simp [p]
    tauto
  have hbad_cover : ∀ i ∈ bad, Set.Icc (P.x i) (P.x (i + 1)) ⊆ U := by
    intro i hi
    exact (Finset.mem_filter.1 hi).2
  have hgood_cover : ∀ i ∈ good, ∃ y ∈ s,
      Set.Icc (P.x i) (P.x (i + 1)) ⊆ V y := by
    intro i hi
    rcases hbad i (Finset.mem_range.1 (Finset.mem_filter.1 hi).1) with hU | hV
    · exact False.elim ((Finset.mem_filter.1 hi).2 hU)
    · exact hV
  exact ⟨bad, good, hbad_sub, hgood_sub, hdisj, hunion, hbad_cover, hgood_cover⟩

/--
@isnad1 id=le.3h4v.s5.efbda0dabad1 from=translated src=- shape=7c05bf4b vocab=cba06ccd
-/
theorem partition_points_mono_local
    {x : ℕ → ℝ} {n i j : ℕ}
    (hstrict : ∀ k < n, x k < x (k + 1))
    (hij : i ≤ j) (hj : j ≤ n) : x i ≤ x j := by
  induction hij with
  | refl => exact le_rfl
  | @step j hij ih =>
      exact (ih (le_trans (Nat.le_succ j) hj)).trans (hstrict j (by omega)).le

/--
@isnad1 id=pairwise.2h3v.s6.f00639b00747 from=translated src=- shape=6540c8d7 vocab=5edf8292
-/
theorem partition_Ioc_pairwise_disjoint_local
    {x : ℕ → ℝ} {n : ℕ} (hstrict : ∀ k < n, x k < x (k + 1))
    (s : Finset ℕ) (hs : s ⊆ Finset.range n) :
    (↑s : Set ℕ).PairwiseDisjoint (fun i => Set.Ioc (x i) (x (i + 1))) := by
  intro i hi j hj hij
  rcases lt_or_gt_of_ne hij with hij' | hji
  · apply Set.Ioc_disjoint_Ioc_of_le
    exact partition_points_mono_local hstrict (by omega)
      (le_trans (Nat.le_succ j) (Finset.mem_range.mp (hs hj)))
  · have hle : x (j + 1) ≤ x i :=
      partition_points_mono_local hstrict (Nat.succ_le_of_lt hji)
        (le_of_lt (Finset.mem_range.mp (hs hi)))
    exact (Set.Ioc_disjoint_Ioc_of_le hle).symm

/- Lower framework TODO 2a-i: disjoint bad intervals are controlled by U. -/
/--
@isnad1 id=le.2h5v.s7.a70e2a1a03c8 from=translated src=- shape=ea61ff26 vocab=e7fdcdb5
-/
theorem bad_intervals_length_le_volume
    {a b : ℝ} {U : Set ℝ} {P : DarbouxPartition a b} (bad : Finset ℕ)
    (hbad : bad ⊆ Finset.range P.n)
    (hbadCover : ∀ i ∈ bad, Set.Icc (P.x i) (P.x (i + 1)) ⊆ U) :
    ENNReal.ofReal (∑ i ∈ bad, (P.x (i + 1) - P.x i)) ≤ volume U := by
  let I : ℕ → Set ℝ := fun i => Set.Ioc (P.x i) (P.x (i + 1))
  have hpair : (↑bad : Set ℕ).PairwiseDisjoint I := by
    simpa [I] using partition_Ioc_pairwise_disjoint_local
      (fun k hk => P.strict k hk) bad hbad
  have hmeas : ∀ i ∈ bad, MeasurableSet (I i) := by
    intro i hi
    exact measurableSet_Ioc
  have hunion : (⋃ i ∈ bad, I i) ⊆ U := by
    intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨i, hx⟩
    rcases Set.mem_iUnion.mp hx with ⟨hi, hxi⟩
    exact hbadCover i hi ⟨le_of_lt hxi.1, hxi.2⟩
  have hvol : volume (⋃ i ∈ bad, I i) =
      ∑ i ∈ bad, volume (I i) :=
    MeasureTheory.measure_biUnion_finset hpair hmeas
  have hmonoU : volume (⋃ i ∈ bad, I i) ≤ volume U :=
    MeasureTheory.measure_mono hunion
  rw [hvol] at hmonoU
  simpa [I, Real.volume_Ioc, ← ENNReal.ofReal_sum_of_nonneg
    (fun i hi => sub_nonneg.mpr (P.strict i (Finset.mem_range.mp (hbad hi))).le)] using hmonoU
/-
  have hmono : ∀ i j, i ≤ j → j ≤ P.n → P.x i ≤ P.x j := by
    intro i j hij hj
    induction j, hij using Nat.le_induction with
    | base => exact le_rfl
    | succ j hj hstep =>
        apply le_trans hstep
        apply (P.strict j)
        omega
  have hpair : (↑bad : Set ℕ).PairwiseDisjoint I := by
    intro i hi j hj hij
    rcases lt_or_gt_of_ne hij with hij' | hji
    · apply Set.Ioc_disjoint_Ioc_of_le
      exact hmono (i + 1) j (by omega) (Finset.mem_range.mp (hbad hj))
    · exact (Set.disjoint_comm.mp (Set.Ioc_disjoint_Ioc_of_le
        (hmono (j + 1) i (by omega) (Finset.mem_range.mp (hbad hi)))))
  have hmeas : ∀ i ∈ bad, MeasurableSet (I i) := by
    intro i hi
    exact measurableSet_Ioc
  have hunion : (⋃ i ∈ bad, I i) ⊆ U := by
    rintro x ⟨i, hi, hxi⟩
    exact hbadCover i hi ⟨le_of_lt hxi.1, hxi.2.le⟩
  have hvol : volume (⋃ i ∈ bad, I i) =
      ∑ i ∈ bad, volume (I i) :=
    MeasureTheory.measure_biUnion_finset hpair hmeas
  have hmonoU : volume (⋃ i ∈ bad, I i) ≤ volume U := volume_mono hunion
  rw [hvol] at hmonoU
  simpa [I, Real.volume_Ioc, ENNReal.ofReal_sum_of_nonneg
    (fun i hi => sub_nonneg.mpr (P.strict i (Finset.mem_range.mp (hbad hi))).le)] using hmonoU
-/

/- Lower framework TODO 2a-ii: convert the measure estimate to the target bound. -/
/--
@isnad1 id=lt.7h7v.s8.bcf16460d24c from=translated src=- shape=65f29c09 vocab=134d25cb
-/
theorem bad_intervals_length_arithmetic
    {a b C δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ) (hC : 0 ≤ C)
    (U : Set ℝ) (hUmeasure : volume U < ENNReal.ofReal (δ / (4 * (C + 1))))
    {P : DarbouxPartition a b} (bad : Finset ℕ)
    (hbad : bad ⊆ Finset.range P.n)
    (hbadCover : ∀ i ∈ bad, Set.Icc (P.x i) (P.x (i + 1)) ⊆ U) :
    (hmeasure : ENNReal.ofReal (∑ i ∈ bad, (P.x (i + 1) - P.x i)) <
      ENNReal.ofReal (δ / (4 * (C + 1)))) →
    (∑ i ∈ bad, (P.x (i + 1) - P.x i) * (2 * C)) < δ / 2 := by
  intro hmeasure
  have hlen : 0 ≤ ∑ i ∈ bad, (P.x (i + 1) - P.x i) := by
    apply Finset.sum_nonneg
    intro i hi
    exact sub_nonneg.mpr (P.strict i (Finset.mem_range.mp (hbad hi))).le
  have hreal : (∑ i ∈ bad, (P.x (i + 1) - P.x i)) < δ / (4 * (C + 1)) := by
    exact (ENNReal.ofReal_lt_ofReal_iff (div_pos hδ (by linarith [hC]))).mp hmeasure
  have hden : 0 < C + 1 := by linarith
  by_cases hC0 : C = 0
  · subst C
    simp [half_pos hδ]
  have hCpos : 0 < 2 * C := by positivity
  have hmul := mul_lt_mul_of_pos_left hreal hCpos
  have hratio : 2 * C / (4 * (C + 1)) < (1 : ℝ) / 2 := by
    apply (div_lt_iff₀ (by linarith [hC])).2
    nlinarith
  calc
    (∑ i ∈ bad, (P.x (i + 1) - P.x i) * (2 * C)) =
        (∑ i ∈ bad, (P.x (i + 1) - P.x i)) * (2 * C) := by
          rw [Finset.sum_mul]
    _ < (δ / (4 * (C + 1))) * (2 * C) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    _ = δ * (2 * C / (4 * (C + 1))) := by field_simp
    _ < δ / 2 := by
      have hhalf : 0 < δ / 2 := half_pos hδ
      simpa [div_eq_mul_inv] using mul_lt_mul_of_pos_left hratio hδ

/- Lower framework TODO 2a: the exceptional intervals consume little length. -/
/- **坏区间估计**：例外区间并集的测度控制其长度和，再转成带 `2*C` 权重的误差预算。 -/
/--
@isnad1 id=lt.6h8v.s8.404f51578379 from=translated src=- shape=37f3b94f vocab=134d25cb
-/
theorem bad_interval_length_sum_bound
    {f : ℝ → ℝ} {a b C δ : ℝ} (hab : a ≤ b)
    (hδ : 0 < δ) (hC : 0 ≤ C) (U : Set ℝ)
    (hUmeasure : volume U < ENNReal.ofReal (δ / (4 * (C + 1))))
    {P : DarbouxPartition a b} (bad : Finset ℕ)
    (hbad : bad ⊆ Finset.range P.n)
    (hbadCover : ∀ i ∈ bad, Set.Icc (P.x i) (P.x (i + 1)) ⊆ U) :
    (∑ i ∈ bad, (P.x (i + 1) - P.x i) * (2 * C)) < δ / 2 := by
  apply bad_intervals_length_arithmetic hab hδ hC U hUmeasure bad hbad hbadCover
  exact lt_of_le_of_lt (bad_intervals_length_le_volume bad hbad hbadCover) hUmeasure

/- Lower framework TODO 2b-i-a: approximate the lower endpoint of the image. -/
/--
@isnad1 id=ex.3h6v.s7.92a05fc69503 from=translated src=- shape=2264a838 vocab=f2fa0d76
-/
theorem interval_inf_approx
    {f : ℝ → ℝ} {a b : ℝ} {P : DarbouxPartition a b} (i : ℕ) (hi : i < P.n)
    (η : ℝ) (hη : 0 < η)
    (hbelow : ∃ L : ℝ, ∀ x ∈ Set.Icc (P.x i) (P.x (i + 1)), L ≤ f x) :
    ∃ x ∈ Set.Icc (P.x i) (P.x (i + 1)),
      sInf (f '' Set.Icc (P.x i) (P.x (i + 1))) + η > f x := by
  let I : Set ℝ := Set.Icc (P.x i) (P.x (i + 1))
  let S : Set ℝ := f '' I
  have hne : S.Nonempty := by
    refine ⟨f (P.x i), ⟨P.x i, ⟨le_rfl, (P.strict i hi).le⟩, rfl⟩⟩
  obtain ⟨L, hL⟩ := hbelow
  have hbdd : BddBelow S := by
    refine ⟨L, ?_⟩
    rintro z ⟨x, hx, rfl⟩
    exact hL x hx
  have hlt : sInf S < sInf S + η := by linarith
  obtain ⟨z, hz, hzlt⟩ := (csInf_lt_iff hbdd hne).1 hlt
  rcases hz with ⟨x, hx, rfl⟩
  exact ⟨x, hx, by linarith⟩

/- Lower framework TODO 2b-i-b: approximate the upper endpoint of the image. -/
/--
@isnad1 id=ex.3h6v.s7.e2c50f0c67f4 from=translated src=- shape=18bbc4e4 vocab=c357d4da
-/
theorem interval_sup_approx
    {f : ℝ → ℝ} {a b : ℝ} {P : DarbouxPartition a b} (i : ℕ) (hi : i < P.n)
    (η : ℝ) (hη : 0 < η)
    (habove : ∃ L : ℝ, ∀ x ∈ Set.Icc (P.x i) (P.x (i + 1)), f x ≤ L) :
    ∃ x ∈ Set.Icc (P.x i) (P.x (i + 1)),
      f x > sSup (f '' Set.Icc (P.x i) (P.x (i + 1))) - η := by
  let I : Set ℝ := Set.Icc (P.x i) (P.x (i + 1))
  let S : Set ℝ := f '' I
  have hne : S.Nonempty := by
    refine ⟨f (P.x i), ⟨P.x i, ⟨le_rfl, (P.strict i hi).le⟩, rfl⟩⟩
  obtain ⟨L, hL⟩ := habove
  have hbdd : BddAbove S := by
    refine ⟨L, ?_⟩
    rintro z ⟨x, hx, rfl⟩
    exact hL x hx
  have hlt : sSup S - η < sSup S := by linarith
  obtain ⟨z, hz, hzlt⟩ := (lt_csSup_iff hbdd hne).1 hlt
  rcases hz with ⟨x, hx, rfl⟩
  exact ⟨x, hx, hzlt⟩

/- Lower framework TODO 2b-i-c: combine the two approximants through hosc. -/
/--
@isnad1 id=le.7h9v.s9.da2bc253a5fb from=translated src=- shape=02c7dff1 vocab=39117673
-/
theorem good_interval_oscillation_from_approximants
    {f : ℝ → ℝ} {a b δ : ℝ} {U : Set ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    {P : DarbouxPartition a b} (i : ℕ) (hi : i < P.n)
    (s : Set {x // x ∈ Set.Icc a b \ U})
    (V : {x // x ∈ Set.Icc a b \ U} → Set ℝ)
    (hosc : ∀ y ∈ s, ∀ u ∈ V y ∩ Set.Icc a b, ∀ v ∈ V y ∩ Set.Icc a b,
      |f u - f v| < δ / (2 * (b - a + 1)))
    (hbelow : ∃ L : ℝ, ∀ x ∈ Set.Icc (P.x i) (P.x (i + 1)), L ≤ f x)
    (habove : ∃ L : ℝ, ∀ x ∈ Set.Icc (P.x i) (P.x (i + 1)), f x ≤ L)
    (hcover : ∃ y ∈ s, Set.Icc (P.x i) (P.x (i + 1)) ⊆ V y) :
    sSup (f '' Set.Icc (P.x i) (P.x (i + 1))) -
      sInf (f '' Set.Icc (P.x i) (P.x (i + 1))) ≤
      δ / (2 * (b - a + 1)) := by
  apply le_of_forall_pos_le_add
  intro η hη
  have hη2 : 0 < η / 2 := by linarith
  obtain ⟨xlo, hxlo, hxlo'⟩ := interval_inf_approx i hi (η / 2) hη2 hbelow
  obtain ⟨xhi, hxhi, hxhi'⟩ := interval_sup_approx i hi (η / 2) hη2 habove
  obtain ⟨y, hy, hycover⟩ := hcover
  have hleft : P.x i ∈ Set.Icc a b :=
    partition_point_mem hab P.x0 P.xN P.strict (Nat.le_of_lt hi)
  have hright : P.x (i + 1) ∈ Set.Icc a b :=
    partition_point_mem hab P.x0 P.xN P.strict (Nat.succ_le_of_lt hi)
  have hxloab : xlo ∈ Set.Icc a b :=
    ⟨le_trans hleft.1 hxlo.1, le_trans hxlo.2 hright.2⟩
  have xhiab : xhi ∈ Set.Icc a b :=
    ⟨le_trans hleft.1 hxhi.1, le_trans hxhi.2 hright.2⟩
  have hosc' := hosc y hy xhi ⟨hycover hxhi, xhiab⟩ xlo ⟨hycover hxlo, hxloab⟩
  have hupper : sSup (f '' Set.Icc (P.x i) (P.x (i + 1))) - f xhi < η := by
    linarith
  have hlower : f xlo - sInf (f '' Set.Icc (P.x i) (P.x (i + 1))) < η := by
    linarith
  linarith [abs_lt.mp hosc']

/- Lower framework TODO 2b-i: continuity neighborhoods control one good interval. -/
/--
@isnad1 id=le.7h9v.s9.da2bc253a5fb from=translated src=- shape=02c7dff1 vocab=39117673
-/
theorem good_interval_oscillation_le
    {f : ℝ → ℝ} {a b δ : ℝ} {U : Set ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    {P : DarbouxPartition a b} (i : ℕ) (hi : i < P.n)
    (s : Set {x // x ∈ Set.Icc a b \ U})
    (V : {x // x ∈ Set.Icc a b \ U} → Set ℝ)
    (hosc : ∀ y ∈ s, ∀ u ∈ V y ∩ Set.Icc a b, ∀ v ∈ V y ∩ Set.Icc a b,
      |f u - f v| < δ / (2 * (b - a + 1)))
    (hbelow : ∃ L : ℝ, ∀ x ∈ Set.Icc (P.x i) (P.x (i + 1)), L ≤ f x)
    (habove : ∃ L : ℝ, ∀ x ∈ Set.Icc (P.x i) (P.x (i + 1)), f x ≤ L)
    (hcover : ∃ y ∈ s, Set.Icc (P.x i) (P.x (i + 1)) ⊆ V y) :
    sSup (f '' Set.Icc (P.x i) (P.x (i + 1))) -
      sInf (f '' Set.Icc (P.x i) (P.x (i + 1))) ≤
      δ / (2 * (b - a + 1)) := by
  exact good_interval_oscillation_from_approximants hab hδ i hi s V hosc hbelow habove hcover

/- Lower framework TODO 2b-ii: finite weighted assembly of local bounds. -/
/- **好区间估计**：局部振荡控制逐项乘以区间长度，并利用所有分割长度总和为 `b-a`。 -/
/--
@isnad1 id=lt.6h10v.s9.3a6f6dbbdf93 from=translated src=- shape=d60dfad9 vocab=2e58c299
-/
theorem good_interval_oscillation_sum_bound
    {f : ℝ → ℝ} {a b C δ : ℝ} (hab : a ≤ b)
    (hb : ∀ x ∈ Set.Icc a b, |f x| ≤ C) (hδ : 0 < δ) {P : DarbouxPartition a b} (good : Finset ℕ)
    (hgood : good ⊆ Finset.range P.n)
    (U : Set ℝ) (s : Set {x // x ∈ Set.Icc a b \ U})
    (V : {x // x ∈ Set.Icc a b \ U} → Set ℝ)
    (hosc : ∀ y ∈ s, ∀ u ∈ V y ∩ Set.Icc a b, ∀ v ∈ V y ∩ Set.Icc a b,
      |f u - f v| < δ / (2 * (b - a + 1)))
    (hgoodCover : ∀ i ∈ good, ∃ y ∈ s,
      Set.Icc (P.x i) (P.x (i + 1)) ⊆ V y) :
    (∑ i ∈ good, (P.x (i + 1) - P.x i) *
      (sSup (f '' Set.Icc (P.x i) (P.x (i + 1))) -
        sInf (f '' Set.Icc (P.x i) (P.x (i + 1))))) < δ / 2 := by
  let g : ℕ → ℝ := fun i ↦ P.x (i + 1) - P.x i
  have hlen : ∀ i ∈ Finset.range P.n, 0 ≤ g i := by
    intro i hi
    exact sub_nonneg.mpr (P.strict i (Finset.mem_range.mp hi)).le
  have hsum : (∑ i ∈ good, g i) ≤ b - a := by
    have hsub : (∑ i ∈ good, g i) ≤ ∑ i ∈ Finset.range P.n, g i := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hgood
      intro i hi hnot
      exact hlen i hi
    calc
      (∑ i ∈ good, g i) ≤ ∑ i ∈ Finset.range P.n, g i := hsub
      _ = b - a := by
        dsimp [g]
        simpa [P.x0, P.xN] using Finset.sum_range_sub P.x P.n
  have hosc : ∀ i ∈ good,
      sSup (f '' Set.Icc (P.x i) (P.x (i + 1))) -
        sInf (f '' Set.Icc (P.x i) (P.x (i + 1))) ≤
        δ / (2 * (b - a + 1)) := by
    intro i hi
    have hi' : i < P.n := Finset.mem_range.mp (hgood hi)
    have hpi := partition_point_mem hab P.x0 P.xN P.strict (Nat.le_of_lt hi')
    have hpi1 := partition_point_mem hab P.x0 P.xN P.strict (Nat.succ_le_of_lt hi')
    apply good_interval_oscillation_le hab hδ i hi' s V hosc
    · exact ⟨-C, by
        intro x hx
        have hxab : x ∈ Set.Icc a b := ⟨le_trans hpi.1 hx.1, le_trans hx.2 hpi1.2⟩
        exact (abs_le.mp (hb x hxab)).1⟩
    · exact ⟨C, by
        intro x hx
        have hxab : x ∈ Set.Icc a b := ⟨le_trans hpi.1 hx.1, le_trans hx.2 hpi1.2⟩
        exact (abs_le.mp (hb x hxab)).2⟩
    · exact hgoodCover i hi
  have hterm : (∑ i ∈ good, g i *
      (sSup (f '' Set.Icc (P.x i) (P.x (i + 1))) -
        sInf (f '' Set.Icc (P.x i) (P.x (i + 1))))) ≤
      ∑ i ∈ good, g i * (δ / (2 * (b - a + 1))) := by
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_left (hosc i hi) (hlen i (hgood hi))
  dsimp [g] at hterm hsum
  rw [← Finset.sum_mul] at hterm
  calc
    (∑ i ∈ good, (P.x (i + 1) - P.x i) *
      (sSup (f '' Set.Icc (P.x i) (P.x (i + 1))) -
        sInf (f '' Set.Icc (P.x i) (P.x (i + 1))))) ≤
        (∑ i ∈ good, (P.x (i + 1) - P.x i)) *
          (δ / (2 * (b - a + 1))) := hterm
    _ ≤ (b - a) * (δ / (2 * (b - a + 1))) := by
      gcongr
    _ < δ / 2 := by
      have hden : 0 < b - a + 1 := by linarith
      have hratio : (b - a) / (b - a + 1) < 1 := by
        apply (div_lt_iff₀ hden).2
        linarith
      calc
        (b - a) * (δ / (2 * (b - a + 1))) =
            ((b - a) / (b - a + 1)) * (δ / 2) := by field_simp
        _ < δ / 2 := by
          simpa using mul_lt_mul_of_pos_right hratio (half_pos hδ)

/- Lower framework TODO 2: quantitative estimates for a classification. -/
/- **定量组装**：坏区间预算与好区间预算各占误差的一半。 -/
/--
@isnad1 id=and.11h11v.s9.e27185052f3e from=translated src=- shape=1f96ce86 vocab=638fa407
-/
theorem interval_classification_quantitative_bounds
    {f : ℝ → ℝ} {a b C δ : ℝ} (hab : a ≤ b)
    (hb : ∀ x ∈ Set.Icc a b, |f x| ≤ C) (hδ : 0 < δ)
    (P : DarbouxPartition a b) (bad good : Finset ℕ)
    (hbad : bad ⊆ Finset.range P.n) (hgood : good ⊆ Finset.range P.n)
    (hdisj : Disjoint bad good) (hunion : bad ∪ good = Finset.range P.n)
    (U : Set ℝ) (hUmeasure : volume U < ENNReal.ofReal (δ / (4 * (C + 1))))
    (s : Set {x // x ∈ Set.Icc a b \ U})
    (V : {x // x ∈ Set.Icc a b \ U} → Set ℝ)
    (hosc : ∀ y ∈ s, ∀ u ∈ V y ∩ Set.Icc a b, ∀ v ∈ V y ∩ Set.Icc a b,
      |f u - f v| < δ / (2 * (b - a + 1)))
    (hbadCover : ∀ i ∈ bad, Set.Icc (P.x i) (P.x (i + 1)) ⊆ U)
    (hgoodCover : ∀ i ∈ good, ∃ y ∈ s,
      Set.Icc (P.x i) (P.x (i + 1)) ⊆ V y) :
      (∑ i ∈ bad, (P.x (i + 1) - P.x i) * (2 * C)) < δ / 2 ∧
      (∑ i ∈ good, (P.x (i + 1) - P.x i) *
      (sSup (f '' Set.Icc (P.x i) (P.x (i + 1))) -
          sInf (f '' Set.Icc (P.x i) (P.x (i + 1))))) < δ / 2 := by
  have hC : 0 ≤ C := by
    have ha := hb a ⟨le_rfl, hab⟩
    nlinarith [abs_nonneg (f a)]
  have hbadSum := bad_interval_length_sum_bound (f := f) hab hδ hC U hUmeasure bad hbad hbadCover
  have hgoodSum := good_interval_oscillation_sum_bound (C := C) (f := f) hab hb hδ good hgood U s V hosc hgoodCover
  exact ⟨hbadSum, hgoodSum⟩

/--
@isnad1 id=ex.7h10v.s9.7b07b5ae271d from=translated src=- shape=4ce77e09 vocab=638fa407
-/
theorem interval_classification_and_bounds
    {f : ℝ → ℝ} {a b C δ ρ : ℝ} (hab : a ≤ b)
    (hb : ∀ x ∈ Set.Icc a b, |f x| ≤ C) (hδ : 0 < δ)
    (U : Set ℝ) (hUmeasure : volume U < ENNReal.ofReal (δ / (4 * (C + 1))))
    (s : Set {x // x ∈ Set.Icc a b \ U})
    (V : {x // x ∈ Set.Icc a b \ U} → Set ℝ)
    (hosc : ∀ y ∈ s, ∀ u ∈ V y ∩ Set.Icc a b, ∀ v ∈ V y ∩ Set.Icc a b,
      |f u - f v| < δ / (2 * (b - a + 1)))
    (P : DarbouxPartition a b)
    (hbad : ∀ i < P.n, (Set.Icc (P.x i) (P.x (i + 1)) ⊆ U) ∨
      ∃ y ∈ s, Set.Icc (P.x i) (P.x (i + 1)) ⊆ V y)
    (hmesh : ∀ i < P.n, P.x (i + 1) - P.x i < ρ) :
    ∃ bad good : Finset ℕ,
      bad ⊆ Finset.range P.n ∧ good ⊆ Finset.range P.n ∧
      Disjoint bad good ∧ bad ∪ good = Finset.range P.n ∧
      (∑ i ∈ bad, (P.x (i + 1) - P.x i) * (2 * C)) < δ / 2 ∧
      (∑ i ∈ good, (P.x (i + 1) - P.x i) *
        (sSup (f '' Set.Icc (P.x i) (P.x (i + 1))) -
          sInf (f '' Set.Icc (P.x i) (P.x (i + 1))))) < δ / 2 := by
  obtain ⟨bad, good, hbad', hgood', hdisj, hunion, hbadCover, hgoodCover⟩ :=
    interval_classification_partition hab hb hδ U hUmeasure s V hosc P hbad hmesh
  obtain ⟨hbadSum, hgoodSum⟩ :=
    interval_classification_quantitative_bounds hab hb hδ P bad good hbad' hgood'
      hdisj hunion U hUmeasure s V hosc hbadCover hgoodCover
  exact ⟨bad, good, hbad', hgood', hdisj, hunion, hbadSum, hgoodSum⟩

/--
@isnad1 id=le.3h6v.s6.29cd23c68e20 from=translated src=- shape=b3e4e4ac vocab=68271a26
-/
theorem interval_sup_le_C
    {f : ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b)
    (hb : ∀ x ∈ Set.Icc a b, |f x| ≤ C) (P : DarbouxPartition a b)
    (i : ℕ) (hi : i < P.n) :
    sSup (f '' Set.Icc (P.x i) (P.x (i + 1))) ≤ C := by
  have hmem : P.x i ∈ Set.Icc a b :=
    partition_point_mem hab P.x0 P.xN P.strict (Nat.le_of_lt hi)
  have hne : (f '' Set.Icc (P.x i) (P.x (i + 1))).Nonempty :=
    ⟨f (P.x i), ⟨P.x i, ⟨le_rfl, (P.strict i hi).le⟩, rfl⟩⟩
  apply csSup_le hne
  rintro z ⟨x, hx, rfl⟩
  have hxab : x ∈ Set.Icc a b := by
    have hright := partition_point_mem hab P.x0 P.xN P.strict (Nat.succ_le_of_lt hi)
    exact ⟨le_trans hmem.1 hx.1, le_trans hx.2 hright.2⟩
  exact (abs_le.mp (hb x hxab)).2

/--
@isnad1 id=le.3h6v.s6.9ac51e403efe from=translated src=- shape=3d71048b vocab=02593585
-/
theorem interval_inf_ge_neg_C
    {f : ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b)
    (hb : ∀ x ∈ Set.Icc a b, |f x| ≤ C) (P : DarbouxPartition a b)
    (i : ℕ) (hi : i < P.n) :
    -C ≤ sInf (f '' Set.Icc (P.x i) (P.x (i + 1))) := by
  have hmem : P.x i ∈ Set.Icc a b :=
    partition_point_mem hab P.x0 P.xN P.strict (Nat.le_of_lt hi)
  have hne : (f '' Set.Icc (P.x i) (P.x (i + 1))).Nonempty :=
    ⟨f (P.x i), ⟨P.x i, ⟨le_rfl, (P.strict i hi).le⟩, rfl⟩⟩
  apply le_csInf hne
  rintro z ⟨x, hx, rfl⟩
  have hxab : x ∈ Set.Icc a b := by
    have hright := partition_point_mem hab P.x0 P.xN P.strict (Nat.succ_le_of_lt hi)
    exact ⟨le_trans hmem.1 hx.1, le_trans hx.2 hright.2⟩
  exact (abs_le.mp (hb x hxab)).1

/--
@isnad1 id=le.3h6v.s7.1d7e0e123705 from=translated src=- shape=1e70dc2f vocab=ba57c6cc
-/
theorem bad_oscillation_sum_le_twoC
    {f : ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b)
    (hb : ∀ x ∈ Set.Icc a b, |f x| ≤ C) (P : DarbouxPartition a b)
    (bad : Finset ℕ) (hbad : bad ⊆ Finset.range P.n) :
    (∑ i ∈ bad, (P.x (i + 1) - P.x i) *
      (sSup (f '' Set.Icc (P.x i) (P.x (i + 1))) -
        sInf (f '' Set.Icc (P.x i) (P.x (i + 1))))) ≤
      ∑ i ∈ bad, (P.x (i + 1) - P.x i) * (2 * C) := by
  apply Finset.sum_le_sum
  intro i hi
  have hi' : i < P.n := Finset.mem_range.mp (hbad hi)
  have hlen : 0 ≤ P.x (i + 1) - P.x i :=
    sub_nonneg.mpr (P.strict i hi').le
  have hsup := interval_sup_le_C hab hb P i hi'
  have hinf := interval_inf_ge_neg_C hab hb P i hi'
  gcongr
  linarith

/--
@isnad1 id=lt.8h8v.s8.46b7f16ea0ea from=translated src=- shape=f4275d3f vocab=679b2fbf
-/
theorem partition_gap_sum_from_bounds
    {f : ℝ → ℝ} {a b C δ : ℝ} (hab : a ≤ b)
    (hb : ∀ x ∈ Set.Icc a b, |f x| ≤ C) (P : DarbouxPartition a b)
    (bad good : Finset ℕ) (hbad : bad ⊆ Finset.range P.n)
    (hgood : good ⊆ Finset.range P.n) (hdisj : Disjoint bad good)
    (hunion : bad ∪ good = Finset.range P.n)
    (hbadSum : (∑ i ∈ bad, (P.x (i + 1) - P.x i) * (2 * C)) < δ / 2)
    (hgoodSum : (∑ i ∈ good, (P.x (i + 1) - P.x i) *
      (sSup (f '' Set.Icc (P.x i) (P.x (i + 1))) -
        sInf (f '' Set.Icc (P.x i) (P.x (i + 1))))) < δ / 2) :
    upperSum f P - lowerSum f P < δ := by
  obtain hbadActual := bad_oscillation_sum_le_twoC hab hb P bad hbad
  let g : ℕ → ℝ := fun i ↦
    (P.x (i + 1) - P.x i) *
      (sSup (f '' Set.Icc (P.x i) (P.x (i + 1))) -
        sInf (f '' Set.Icc (P.x i) (P.x (i + 1))))
  have hdiff : upperSum f P - lowerSum f P =
      ∑ i ∈ Finset.range P.n, g i := by
    unfold g upperSum lowerSum
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hsplit : (∑ i ∈ Finset.range P.n, g i) =
      (∑ i ∈ bad, g i) + ∑ i ∈ good, g i := by
    rw [← hunion, Finset.sum_union hdisj]
  have hbad' : (∑ i ∈ bad, g i) < δ / 2 := by
    dsimp [g]
    exact lt_of_le_of_lt hbadActual hbadSum
  have hsum : (∑ i ∈ bad, g i) + ∑ i ∈ good, g i < δ / 2 + δ / 2 :=
    add_lt_add hbad' hgoodSum
  calc
    upperSum f P - lowerSum f P = ∑ i ∈ Finset.range P.n, g i := hdiff
    _ = (∑ i ∈ bad, g i) + ∑ i ∈ good, g i := hsplit
    _ < δ / 2 + δ / 2 := hsum
    _ = δ := by ring

/--
@isnad1 id=lt.7h8v.s8.ade25c0dc65b from=translated src=- shape=c4ffd2d2 vocab=5c4ff5ee
-/
theorem partition_gap_split_arithmetic
    {f : ℝ → ℝ} {a b C δ : ℝ} (P : DarbouxPartition a b)
    (bad good : Finset ℕ) (hbad : bad ⊆ Finset.range P.n)
    (hgood : good ⊆ Finset.range P.n) (hdisj : Disjoint bad good)
    (hunion : bad ∪ good = Finset.range P.n)
    (hbadActual : (∑ i ∈ bad, (P.x (i + 1) - P.x i) *
      (sSup (f '' Set.Icc (P.x i) (P.x (i + 1))) -
        sInf (f '' Set.Icc (P.x i) (P.x (i + 1))))) ≤
      ∑ i ∈ bad, (P.x (i + 1) - P.x i) * (2 * C))
    (hbadSum : (∑ i ∈ bad, (P.x (i + 1) - P.x i) * (2 * C)) < δ / 2)
    (hgoodSum : (∑ i ∈ good, (P.x (i + 1) - P.x i) *
      (sSup (f '' Set.Icc (P.x i) (P.x (i + 1))) -
        sInf (f '' Set.Icc (P.x i) (P.x (i + 1))))) < δ / 2) :
    upperSum f P - lowerSum f P < δ := by
  let g : ℕ → ℝ := fun i ↦
    (P.x (i + 1) - P.x i) *
      (sSup (f '' Set.Icc (P.x i) (P.x (i + 1))) -
        sInf (f '' Set.Icc (P.x i) (P.x (i + 1))))
  have hdiff : upperSum f P - lowerSum f P =
      ∑ i ∈ Finset.range P.n, g i := by
    unfold g upperSum lowerSum
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hsplit : (∑ i ∈ Finset.range P.n, g i) =
      (∑ i ∈ bad, g i) + ∑ i ∈ good, g i := by
    rw [← hunion, Finset.sum_union hdisj]
  have hbad' : (∑ i ∈ bad, g i) < δ / 2 := by
    dsimp [g]
    exact lt_of_le_of_lt hbadActual hbadSum
  have hsum : (∑ i ∈ bad, g i) + ∑ i ∈ good, g i < δ / 2 + δ / 2 :=
    add_lt_add hbad' hgoodSum
  calc
    upperSum f P - lowerSum f P = ∑ i ∈ Finset.range P.n, g i := hdiff
    _ = (∑ i ∈ bad, g i) + ∑ i ∈ good, g i := hsplit
    _ < δ / 2 + δ / 2 := hsum
    _ = δ := by ring

/- **Darboux 夹逼**：分类后的两项误差相加，得到 `upperSum - lowerSum < δ`。 -/
/--
@isnad1 id=lt.7h10v.s9.f8d65f886fa8 from=translated src=- shape=28ad6763 vocab=5dd846aa
-/
theorem partition_gap_sum_from_interval_classification
    {f : ℝ → ℝ} {a b C δ ρ : ℝ} (hab : a ≤ b)
    (hb : ∀ x ∈ Set.Icc a b, |f x| ≤ C) (hδ : 0 < δ)
    (U : Set ℝ) (hUmeasure : volume U < ENNReal.ofReal (δ / (4 * (C + 1))))
    (s : Set {x // x ∈ Set.Icc a b \ U})
    (V : {x // x ∈ Set.Icc a b \ U} → Set ℝ)
    (hosc : ∀ y ∈ s, ∀ u ∈ V y ∩ Set.Icc a b, ∀ v ∈ V y ∩ Set.Icc a b,
      |f u - f v| < δ / (2 * (b - a + 1)))
    (P : DarbouxPartition a b)
    (hbad : ∀ i < P.n, (Set.Icc (P.x i) (P.x (i + 1)) ⊆ U) ∨
      ∃ y ∈ s, Set.Icc (P.x i) (P.x (i + 1)) ⊆ V y)
    (hmesh : ∀ i < P.n, P.x (i + 1) - P.x i < ρ) :
    upperSum f P - lowerSum f P < δ := by
  obtain ⟨bad, good, hbadS, hgoodS, hdisj, hunion, hbadSum, hgoodSum⟩ :=
    interval_classification_and_bounds hab hb hδ U hUmeasure s V hosc P hbad hmesh
  exact partition_gap_sum_from_bounds hab hb P bad good hbadS hgoodS hdisj hunion
    hbadSum hgoodSum

/--
@isnad1 id=lt.8h10v.s9.7da5724612ea from=translated src=- shape=3c1de40c vocab=5dd846aa
-/
theorem interval_gap_control_from_cover
    {f : ℝ → ℝ} {a b C δ ρ : ℝ} (hab : a ≤ b)
    (hb : ∀ x ∈ Set.Icc a b, |f x| ≤ C) (hδ : 0 < δ)
    (U : Set ℝ) (hUmeasure : volume U < ENNReal.ofReal (δ / (4 * (C + 1))))
    (s : Set {x // x ∈ Set.Icc a b \ U})
    (V : {x // x ∈ Set.Icc a b \ U} → Set ℝ)
    (hosc : ∀ y ∈ s, ∀ u ∈ V y ∩ Set.Icc a b, ∀ v ∈ V y ∩ Set.Icc a b,
      |f u - f v| < δ / (2 * (b - a + 1)))
    (P : DarbouxPartition a b)
    (hρ : 0 < ρ)
    (hmesh : ∀ i < P.n, P.x (i + 1) - P.x i < ρ)
    (hLeb : ∀ x ∈ Set.Icc a b, ∃ W : Set ℝ,
      (W = U ∨ ∃ y ∈ s, W = V y) ∧
      Set.Icc (x - ρ) (x + ρ) ∩ Set.Icc a b ⊆ W) :
    upperSum f P - lowerSum f P < δ := by
  apply partition_gap_sum_from_interval_classification hab hb hδ U hUmeasure s V hosc P
    (fun i hi ↦ ?_) hmesh
  obtain ⟨W, hW, hsub⟩ := hLeb (P.x i) (partition_point_mem hab P.x0 P.xN P.strict
    (Nat.le_of_lt hi))
  have hinterval : Set.Icc (P.x i) (P.x (i + 1)) ⊆
      Set.Icc (P.x i - ρ) (P.x i + ρ) := by
    have hxi := partition_point_mem hab P.x0 P.xN P.strict (Nat.le_of_lt hi)
    have hxi1 := partition_point_mem hab P.x0 P.xN P.strict (Nat.succ_le_of_lt hi)
    intro z hz
    constructor
    · linarith [hz.1, hρ]
    · linarith [hz.2, hmesh i hi]
  have hzmem : ∀ z ∈ Set.Icc (P.x i) (P.x (i + 1)), z ∈ Set.Icc a b := by
    intro z hz
    have hxi := partition_point_mem hab P.x0 P.xN P.strict (Nat.le_of_lt hi)
    have hxi1 := partition_point_mem hab P.x0 P.xN P.strict (Nat.succ_le_of_lt hi)
    exact ⟨le_trans hxi.1 hz.1, le_trans hz.2 hxi1.2⟩
  rcases hW with rfl | ⟨y, hy, rfl⟩
  · exact Or.inl (fun z hz ↦ hsub ⟨hinterval hz, hzmem z hz⟩)
  · exact Or.inr ⟨y, hy, fun z hz ↦ hsub ⟨hinterval hz, hzmem z hz⟩⟩

/--
@isnad1 id=lt.10h10v.s9.5dbe1df0b66a from=translated src=- shape=771554a4 vocab=a53921ae
-/
theorem partition_gap_from_lebesgue_data
    {f : ℝ → ℝ} {a b C δ : ℝ} (hab : a ≤ b)
    (hb : ∀ x ∈ Set.Icc a b, |f x| ≤ C) (hδ : 0 < δ)
    (U : Set ℝ) (hUopen : IsOpen U)
    (hUmeasure : volume U < ENNReal.ofReal (δ / (4 * (C + 1))))
    (s : Set {x // x ∈ Set.Icc a b \ U}) (hs : s.Finite)
    (V : {x // x ∈ Set.Icc a b \ U} → Set ℝ)
    (hosc : ∀ y ∈ s, ∀ u ∈ V y ∩ Set.Icc a b, ∀ v ∈ V y ∩ Set.Icc a b,
      |f u - f v| < δ / (2 * (b - a + 1)))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hLeb : ∀ x ∈ Set.Icc a b, ∃ W : Set ℝ,
      (W = U ∨ ∃ y ∈ s, W = V y) ∧
      Set.Icc (x - ρ) (x + ρ) ∩ Set.Icc a b ⊆ W)
    (P : DarbouxPartition a b)
    (hmesh : ∀ i < P.n, P.x (i + 1) - P.x i < ρ) :
    upperSum f P - lowerSum f P < δ := by
  exact interval_gap_control_from_cover hab hb hδ U hUmeasure s V hosc P hρ hmesh hLeb

/- **从有限局部覆盖构造分割**：先取 Lebesgue 数，再选网格小于该数的 Darboux 分割。 -/
/--
@isnad1 id=ex.6h6v.s9.ff157d320b01 from=translated src=- shape=b3cfa9de vocab=68248229
-/
theorem partition_from_finite_local_oscillation_cover
    {f : ℝ → ℝ} {a b C δ : ℝ} (hab : a ≤ b)
    (hb : ∀ x ∈ Set.Icc a b, |f x| ≤ C) (hδ : 0 < δ)
    (U : Set ℝ) (hUopen : IsOpen U)
    (hUmeasure : volume U < ENNReal.ofReal (δ / (4 * (C + 1))))
    (hcover : ∃ (s : Set {x // x ∈ Set.Icc a b \ U})
      (V : {x // x ∈ Set.Icc a b \ U} → Set ℝ),
      s.Finite ∧ (∀ y ∈ s, IsOpen (V y) ∧ (y : ℝ) ∈ V y) ∧
      (∀ y ∈ s, ∀ u ∈ V y ∩ Set.Icc a b, ∀ v ∈ V y ∩ Set.Icc a b,
        |f u - f v| < δ / (2 * (b - a + 1))) ∧
      (∀ x ∈ Set.Icc a b, x ∉ U → ∃ y ∈ s, x ∈ V y)) :
    ∃ P : DarbouxPartition a b,
      upperSum f P - lowerSum f P < δ := by
  classical
  rcases hcover with ⟨s, V, hs, hsIcc, hosc, hcover⟩
  have hcover' : Set.Icc a b ⊆ U ∪ ⋃ y ∈ s, V y := by
    intro x hx
    by_cases hxU : x ∈ U
    · exact Or.inl hxU
    · exact Or.inr (by
        rcases hcover x hx hxU with ⟨y, hy, hxy⟩
        exact Set.mem_iUnion.2 ⟨y, Set.mem_iUnion.2 ⟨hy, hxy⟩⟩)
  obtain ⟨ρ, hρ, hLeb⟩ := finite_open_cover_has_lebesgue_number
    hab U hUopen s hs V (fun y hy ↦ (hsIcc y hy).1) hcover'
  obtain ⟨P, hmesh⟩ := darboux_partition_with_mesh_lt hab hρ
  refine ⟨P, ?_⟩
  exact partition_gap_from_lebesgue_data hab hb hδ U hUopen hUmeasure s hs V hosc ρ hρ
    (by
      intro x hx
      obtain ⟨W, hW, hsub⟩ := hLeb x hx
      simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_image] at hW
      rcases hW with hWU | ⟨y, hy, hWy⟩
      · exact ⟨W, Or.inl hWU, hsub⟩
      · exact ⟨W, Or.inr ⟨y, hy, hWy.symm⟩, hsub⟩)
    P hmesh

/--
@isnad1 id=ex.4h5v.s9.e69518b6b6b8 from=translated src=- shape=6c3a6166 vocab=8c0e353c
-/
theorem finite_local_oscillation_cover_from_relative
    {f : ℝ → ℝ} {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    (U : Set ℝ) (hUopen : IsOpen U)
    (hlocal : ∀ x ∈ Set.Icc a b, x ∉ U →
      ∃ V ∈ nhdsWithin x (Set.Icc a b),
        ∀ y ∈ V ∩ Set.Icc a b, ∀ z ∈ V ∩ Set.Icc a b,
          |f y - f z| < δ / (2 * (b - a + 1))) :
    ∃ (s : Set {x // x ∈ Set.Icc a b \ U})
      (V : {x // x ∈ Set.Icc a b \ U} → Set ℝ),
      s.Finite ∧ (∀ y ∈ s, IsOpen (V y) ∧ (y : ℝ) ∈ V y) ∧
      (∀ y ∈ s, ∀ u ∈ V y ∩ Set.Icc a b, ∀ v ∈ V y ∩ Set.Icc a b,
        |f u - f v| < δ / (2 * (b - a + 1))) ∧
      (∀ x ∈ Set.Icc a b, x ∉ U → ∃ y ∈ s, x ∈ V y) := by
  have hopen_local : ∀ x ∈ Set.Icc a b, x ∉ U →
      ∃ V, IsOpen V ∧ x ∈ V ∧
        ∀ y ∈ V ∩ Set.Icc a b, ∀ z ∈ V ∩ Set.Icc a b,
          |f y - f z| < δ / (2 * (b - a + 1)) := by
    intro x hx hxU
    obtain ⟨W, hW, hsub⟩ := hlocal x hx hxU
    obtain ⟨W₀, hW₀, hWsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hW
    obtain ⟨V, hVW, hVopen, hxV⟩ := (mem_nhds_iff.mp hW₀)
    refine ⟨V, hVopen, hxV, ?_⟩
    intro y hy z hz
    apply hsub
    · exact ⟨hWsub ⟨hVW hy.1, hy.2⟩, hy.2⟩
    · exact ⟨hWsub ⟨hVW hz.1, hz.2⟩, hz.2⟩
  exact finite_local_oscillation_cover hab hδ U hUopen hopen_local

/--
@isnad1 id=ex.6h6v.s8.6c4fd124c3b9 from=translated src=- shape=e252dabc vocab=46f8bbb2
-/
theorem partition_gap_from_local_data
    {f : ℝ → ℝ} {a b C δ : ℝ} (hab : a ≤ b)
    (hb : ∀ x ∈ Set.Icc a b, |f x| ≤ C) (hδ : 0 < δ)
    (U : Set ℝ) (hUopen : IsOpen U)
    (hUmeasure : volume U < ENNReal.ofReal (δ / (4 * (C + 1))))
    (hlocal : ∀ x ∈ Set.Icc a b, x ∉ U →
      ∃ V ∈ nhdsWithin x (Set.Icc a b),
        ∀ y ∈ V ∩ Set.Icc a b, ∀ z ∈ V ∩ Set.Icc a b,
          |f y - f z| < δ / (2 * (b - a + 1))) :
    ∃ P : DarbouxPartition a b,
      upperSum f P - lowerSum f P < δ := by
  obtain ⟨s, V, hs, hsIcc, hosc, hcover⟩ :=
    finite_local_oscillation_cover_from_relative hab hδ U hUopen hlocal
  exact partition_from_finite_local_oscillation_cover hab hb hδ U hUopen
    hUmeasure ⟨s, V, hs, hsIcc, hosc, hcover⟩

/--
@isnad1 id=ex.6h6v.s8.6c4fd124c3b9 from=translated src=- shape=e252dabc vocab=46f8bbb2
-/
theorem partition_gap_from_local_oscillation_control
    {f : ℝ → ℝ} {a b C δ : ℝ} (hab : a ≤ b)
    (hb : ∀ x ∈ Set.Icc a b, |f x| ≤ C) (hδ : 0 < δ)
    (U : Set ℝ) (hUopen : IsOpen U)
    (hUmeasure : volume U < ENNReal.ofReal (δ / (4 * (C + 1))))
    (hlocal : ∀ x ∈ Set.Icc a b, x ∉ U →
      ∃ V ∈ nhdsWithin x (Set.Icc a b),
        ∀ y ∈ V ∩ Set.Icc a b, ∀ z ∈ V ∩ Set.Icc a b,
          |f y - f z| < δ / (2 * (b - a + 1))) :
    ∃ P : DarbouxPartition a b,
      upperSum f P - lowerSum f P < δ := by
  exact partition_gap_from_local_data hab hb hδ U hUopen hUmeasure hlocal

/--
@isnad1 id=ex.5h6v.s7.7a080a435b61 from=translated src=- shape=1741fb42 vocab=f88cb439
-/
theorem local_oscillation_from_continuity
    {f : ℝ → ℝ} {a b δ : ℝ} {U : Set ℝ}
    (hab : a ≤ b) (hδ : 0 < δ)
    (hcont : ∀ x ∈ Set.Icc a b, x ∉ U →
      ContinuousWithinAt f (Set.Icc a b) x) :
    ∀ x ∈ Set.Icc a b, x ∉ U →
      ∃ V ∈ nhdsWithin x (Set.Icc a b),
        ∀ y ∈ V ∩ Set.Icc a b, ∀ z ∈ V ∩ Set.Icc a b,
          |f y - f z| < δ / (2 * (b - a + 1)) := by
  intro x hx hxU
  have hden : 0 < b - a + 1 := by linarith
  let η : ℝ := δ / (4 * (b - a + 1))
  have hη : 0 < η := by positivity
  let V : Set ℝ := f ⁻¹' Metric.ball (f x) η
  have hV : V ∈ nhdsWithin x (Set.Icc a b) := by
    apply (hcont x hx hxU).preimage_mem_nhdsWithin
    exact Metric.ball_mem_nhds _ hη
  refine ⟨V, hV, ?_⟩
  intro y hy z hz
  have hy' : dist (f y) (f x) < η := by
    simpa [V, Metric.mem_ball] using hy.1
  have hz' : dist (f x) (f z) < η := by
    simpa [V, Metric.mem_ball, dist_comm] using hz.1
  have hdist : dist (f y) (f z) < 2 * η := by
    calc
      dist (f y) (f z) ≤ dist (f y) (f x) + dist (f x) (f z) :=
        dist_triangle _ _ _
      _ < 2 * η := by linarith
  rw [Real.dist_eq] at hdist
  have htarget : 2 * η = δ / (2 * (b - a + 1)) := by
    dsimp [η]
    field_simp [ne_of_gt hden]
    ring
  rw [htarget] at hdist
  exact hdist

/--
@isnad1 id=ex.6h6v.s7.fdb82e5de500 from=translated src=- shape=671ad431 vocab=6e28f700
-/
theorem partition_gap_small_from_continuity_data
    {f : ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b)
    (hb : ∀ x ∈ Set.Icc a b, |f x| ≤ C)
    (δ : ℝ) (hδ : 0 < δ) (U : Set ℝ) (hUopen : IsOpen U)
    (hUmeasure : volume U < ENNReal.ofReal (δ / (4 * (C + 1))))
    (hcont : ∀ x ∈ Set.Icc a b, x ∉ U →
      ContinuousWithinAt f (Set.Icc a b) x) :
    ∃ P : DarbouxPartition a b,
      upperSum f P - lowerSum f P < δ := by
  apply partition_gap_from_local_data hab hb hδ U hUopen hUmeasure
  exact local_oscillation_from_continuity hab hδ hcont

/- **反向主链**：零测例外集的开覆盖加上连续部分的有限局部振荡覆盖，
  通过上一组定量引理构造误差小于 `δ` 的分割。 -/
/--
@isnad1 id=ex.6h6v.s7.fdb82e5de500 from=translated src=- shape=671ad431 vocab=6e28f700
-/
theorem partition_gap_small_of_open_exceptional_cover
    {f : ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b)
    (hb : ∀ x ∈ Set.Icc a b, |f x| ≤ C)
    (δ : ℝ) (hδ : 0 < δ) (U : Set ℝ) (hUopen : IsOpen U)
    (hUmeasure : volume U < ENNReal.ofReal (δ / (4 * (C + 1))))
    (hcont : ∀ x ∈ Set.Icc a b, x ∉ U →
      ContinuousWithinAt f (Set.Icc a b) x) :
    ∃ P : DarbouxPartition a b,
      upperSum f P - lowerSum f P < δ := by
  exact partition_gap_small_from_continuity_data hab hb δ hδ U hUopen hUmeasure hcont

/- **例外集开覆盖**：由几乎处处连续得到一个小测度的开集，并保证开集外处处连续。 -/
/--
@isnad1 id=ex.4h5v.s7.b5401484a04f from=translated src=- shape=2b0b00c1 vocab=44471762
-/
theorem choose_exceptional_open_cover
    {f : ℝ → ℝ} {a b C δ : ℝ} (hab : a ≤ b)
    (hb : ∀ x ∈ Set.Icc a b, |f x| ≤ C)
    (hc : AlmostEverywhereContinuousOn f a b) (hδ : 0 < δ) :
    ∃ U : Set ℝ, IsOpen U ∧
      volume U < ENNReal.ofReal (δ / (4 * (C + 1))) ∧
      (∀ x ∈ Set.Icc a b, x ∉ U →
        ContinuousWithinAt f (Set.Icc a b) x) := by
  have hC : 0 < C + 1 := by
    have hCa := hb a ⟨le_rfl, hab⟩
    have hC0 : 0 ≤ C := le_trans (abs_nonneg (f a)) hCa
    linarith
  have htpos : 0 < δ / (4 * (C + 1)) := by positivity
  let E : Set ℝ := {x : ℝ | x ∈ Set.Icc a b ∧
    ¬ ContinuousWithinAt f (Set.Icc a b) x}
  obtain ⟨N, hNmeas, hEN, hNzero⟩ :=
    ae_continuity_exceptional_measurable_hull hc
  obtain ⟨U, hNU, hUopen, hUmeasure⟩ :=
    Set.exists_isOpen_lt_of_lt N (ENNReal.ofReal (δ / (4 * (C + 1)))) (by
      rw [hNzero]
      exact ENNReal.ofReal_pos.mpr htpos)
  refine ⟨U, hUopen, hUmeasure, ?_⟩
  intro x hxI hxU
  by_contra hxc
  apply hxU
  exact hNU (hEN ⟨hxI, hxc⟩)

/- **反向方向总组装**：有界且几乎处处连续 ⟹ 任意误差下存在 Darboux 分割。 -/
/--
@isnad1 id=ex.4h4v.s6.08ccf8a685c3 from=translated src=- shape=6229b097 vocab=a08bfdf3
-/
theorem upper_sub_lower_small_of_boundedOn_ae_continuousOn
    {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hb : BoundedOn f (Set.Icc a b))
    (hc : AlmostEverywhereContinuousOn f a b) :
    ∀ δ > 0, ∃ P : DarbouxPartition a b,
      upperSum f P - lowerSum f P < δ := by
  intro δ hδ
  rcases hb with ⟨C, hC⟩
  obtain ⟨U, hUopen, hUmeasure, hcont⟩ :=
    choose_exceptional_open_cover hab (fun x hx ↦ hC x hx) hc hδ
  exact partition_gap_small_of_open_exceptional_cover hab
    (fun x hx ↦ hC x hx) δ hδ U hUopen hUmeasure hcont

/- **正向方向总组装**：Riemann 可积且有界 ⟹ 几乎处处连续。 -/
/--
@isnad1 id=almostev.2h3v.s4.71d56351dbc0 from=translated src=- shape=6f4d3892 vocab=f0280bae
-/
theorem riemannIntegrableWithBound_ae_continuousOn {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (h : RiemannIntegrableWithBound f a b) :
    AlmostEverywhereContinuousOn f a b := by
  apply ae_continuousOn_iff_ae_oscillationWithin_eq_zero.mpr
  apply ae_oscillationWithin_eq_zero_of_layers_null hab h.1
  intro ε hε
  exact positiveOscillationLayer_null hab h hε

/- **Lebesgue 判据最终组装**：固定区间上，有界的黎曼可积性与几乎处处连续等价。 -/
/--
@isnad1 id=riemanni.3h3v.s4.a80b101e2185 from=translated src=- shape=52f0caac vocab=c3602868
-/
theorem boundedOn_ae_continuousOn_riemannIntegrableWithBound {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hb : BoundedOn f (Set.Icc a b))
    (hc : AlmostEverywhereContinuousOn f a b) : RiemannIntegrableWithBound f a b := by
  refine ⟨hb, ?_⟩
  exact upper_sub_lower_small_of_boundedOn_ae_continuousOn hab hb hc

/-- **Lebesgue 判据（临时框架）**：闭区间上的函数黎曼可积，当且仅当其不连续点集
  在 Lebesgue 测度下为零。
> **Entry**: real-analysis.riemann.lebesgue-criterion
@isnad1 id=iff.1h3v.s4.8b831fa1bf31 from=translated src=- shape=66022afb vocab=c3602868
-/
theorem riemannIntegrable_iff_boundedOn_ae_continuousOn {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) :
    RiemannIntegrableWithBound f a b ↔
      BoundedOn f (Set.Icc a b) ∧ AlmostEverywhereContinuousOn f a b := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    exact riemannIntegrableWithBound_ae_continuousOn hab h
  · rintro ⟨hb, hc⟩
    exact boundedOn_ae_continuousOn_riemannIntegrableWithBound hab hb hc

end

end RealAnalysis.Riemann

end SandronesLibrary
