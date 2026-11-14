/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open Filter Topology
open scoped Filter

/-!
# Analysis / Completeness —— 实数完备性的六大等价定理与循环论证环

本文件承载两件事：

1. **三条新真定理**（从 ℝ 的完备性直接证出）：
   * `analysis.completeness.nested-intervals`（闭区间套定理）
   * `analysis.completeness.finite-cover`（有限覆盖原理 / Heine-Borel）
   * `analysis.completeness.accumulation-point`（聚点定理：有界无限集有聚点）

2. **六大命题与等价性环**（`analysis.completeness.equivalence-cycle`）：
   确界原理、单调有界定理、闭区间套定理、聚点定理、有限覆盖原理、Cauchy 收敛准则。
   六条都以"公理形态"（`def … : Prop`，对全称量化的陈述）立出，
   并给出一条循环推导路径 + 两条桥，构成"任一可作公理互推其余"的教学骨架。

   > **诚实声明**：库的地基里 ℝ 已是 mathlib 完整构造（完备性内建），
   > 故六条命题真值层面全部成立、任意两个方向蕴含平凡成立。
   > 本环的价值不在"证明困难性"，而在**把六条定理的推导路线显式登记**
   > 并可用作后续（如第四章函数极限）引用的公理式接口。
-/

namespace SandronesLibrary

namespace Analysis.Completeness

/-! ## 1. 三条真定理 —— 闭区间套、有限覆盖、聚点 -/

/--
> **Entry**: analysis.completeness.nested-intervals
> **一句话**: 闭区间套定理：嵌套闭区间 [aₙ, bₙ]（aₙ 单调增、bₙ 单调减、aₙ ≤ bₙ）
>   的交非空；若区间长度趋于 0，则交为单点。
> **直觉**: aₙ 与 bₙ 像两个相向而行的巡游队伍：aₙ 只进不退、bₙ 只退不进，
>   且永远 aₙ ≤ bₙ——它们必然在某处碰头（交非空）；
>   若缝隙还不断合拢（长度→0），那碰头点只有一个。
> **依赖**: `analysis.sequence.monotone-convergence`、`analysis.real.sup`
> **mathlib**: `Real.isLUB_sSup`, `IsLUB`

闭区间套的非空交：sSup {aₙ} 同时是每个下界序列项的下界、每个上界序列项的上界。
@isnad1 id=ex.3h2v.s5.b5dd330ec939 from=translated src=- shape=540f0ecc vocab=1d753401
-/
theorem nested_intervals_nonempty {a b : ℕ → ℝ}
    (hmono_A : Monotone a) (hanti_B : Antitone b) (hle : ∀ n, a n ≤ b n) :
    ∃ x : ℝ, ∀ n, x ∈ Set.Icc (a n) (b n) := by
  let s : Set ℝ := Set.range a
  have hnonempty : s.Nonempty := Set.range_nonempty a
  have hsup_bdd : BddAbove s := by
    refine ⟨b 0, ?_⟩
    intro x hx
    rcases hx with ⟨k, rfl⟩
    calc
      a k ≤ b k := hle k
      _ ≤ b 0 := hanti_B (by norm_num : 0 ≤ k)
  let x : ℝ := sSup s
  refine ⟨x, ?_⟩
  intro n
  have hlub : IsLUB s x := Real.isLUB_sSup hnonempty hsup_bdd
  constructor
  · exact hlub.1 (Set.mem_range_self n)
  · refine hlub.2 ?_
    intro y hy
    rcases hy with ⟨k, rfl⟩
    by_cases hkn : k ≤ n
    · calc
        a k ≤ a n := hmono_A hkn
        _ ≤ b n := hle n
    · have hn : n ≤ k := le_of_not_ge hkn
      calc
        a k ≤ b k := hle k
        _ ≤ b n := hanti_B hn

/-- 闭区间套 + 长度趋于 0 ⟹ 交为单点（长度合拢后两个极限点无从分离）。
@isnad1 id=existsun.4h2v.s6.10367397e03a from=translated src=- shape=1d3045bd vocab=3ddc68e6
-/
theorem nested_intervals_singleton {a b : ℕ → ℝ}
    (hmono_A : Monotone a) (hanti_B : Antitone b) (hle : ∀ n, a n ≤ b n)
    (hshr : Tendsto (fun n ↦ b n - a n) atTop (𝓝 0)) :
    ∃! x : ℝ, ∀ n, x ∈ Set.Icc (a n) (b n) := by
  rcases nested_intervals_nonempty hmono_A hanti_B hle with ⟨x, hx⟩
  refine ⟨x, hx, ?_⟩
  intro y hy
  have hbnd : ∀ n, |x - y| ≤ b n - a n := by
    intro n
    have hx₁ : a n ≤ x := (hx n).1
    have hx₂ : x ≤ b n := (hx n).2
    have hy₁ : a n ≤ y := (hy n).1
    have hy₂ : y ≤ b n := (hy n).2
    have hle : x - y ≤ b n - a n := by nlinarith
    have hge : -(b n - a n) ≤ x - y := by nlinarith
    rw [abs_le]
    exact ⟨hge, hle⟩
  have hle_zero : |x - y| ≤ 0 := by
    by_contra hnot
    have hpos : 0 < |x - y| := lt_of_not_ge hnot
    rcases Metric.tendsto_atTop.mp hshr (|x - y|) hpos with ⟨N, hN⟩
    have hN' : |b N - a N| < |x - y| := by
      simpa [Real.dist_eq] using hN N (by rfl)
    have hnonneg : 0 ≤ b N - a N := sub_nonneg.mpr ((hx N).1.trans (hx N).2)
    have hlen : |x - y| ≤ b N - a N := hbnd N
    have habs : |b N - a N| = b N - a N := abs_of_nonneg hnonneg
    linarith
  have habs : |x - y| = 0 := le_antisymm hle_zero (abs_nonneg (x - y))
  rw [abs_eq_zero] at habs
  linarith

/--
> **Entry**: analysis.completeness.finite-cover
> **一句话**: 有限覆盖原理（Heine-Borel）：闭区间 [a, b] 的每个开覆盖都有有限子覆盖。
> **直觉**: 无限多的开集把 [a,b] 包住，但真正"出力"的其实只需要其中有限片。
>   [a,b] 是紧集，紧的实质就是"任意开覆盖可抽有限子覆盖"。
> **依赖**: 无（直接来自 ℝ 的紧性实例）
> **mathlib**: `CompactIccSpace.isCompact_Icc`, `IsCompact.elim_finite_subcover`

闭区间上任意指标族开覆盖 ⟹ 有限子覆盖（指标族本身可以是无穷的）。
@isnad1 id=ex.2h4v.s6.9a34516127c0 from=translated src=- shape=7c642ff2 vocab=5327b194
-/
theorem finite_cover_principle {a b : ℝ} {ι : Type*} (U : ι → Set ℝ)
    (hUo : ∀ i, IsOpen (U i)) (hcover : Set.Icc a b ⊆ ⋃ i, U i) :
    ∃ t : Finset ι, Set.Icc a b ⊆ ⋃ i ∈ t, U i :=
  (CompactIccSpace.isCompact_Icc : IsCompact (Set.Icc a b)).elim_finite_subcover U hUo hcover

/--
> **Entry**: analysis.completeness.accumulation-point
> **一句话**: 聚点定理：有界且无限的实集必有聚点。
> **直觉**: 无限多个点挤在有界范围里，必然"堆"出一个极限位置——这就是聚点
>   （每个去心邻域都还落着集合里的点）。
> **依赖**: `analysis.sequence.bolzano-weierstrass`（精神同源）、`analysis.real.bounded-sets`
> **mathlib**: `Set.Infinite.exists_accPt_of_subset_isCompact`, `AccPt`

有界无限集必有聚点：x ∈ 落在 [sInf s, sSup s] 内且是 s 的聚点。
@isnad1 id=ex.3h1v.s5.7edc008d9bb9 from=translated src=- shape=f70ee03f vocab=921c091e
-/
theorem accumulation_point_of_infinite_bounded {s : Set ℝ}
    (hs : s.Infinite) (hb : BddAbove s) (hbdl : BddBelow s) :
    ∃ x : ℝ, AccPt x (𝓟 s) := by
  have hnonempty : s.Nonempty := hs.nonempty
  have hsub : s ⊆ Set.Icc (sInf s) (sSup s) := by
    intro x hx
    constructor
    · exact (isGLB_csInf hnonempty hbdl).1 hx
    · exact (Real.isLUB_sSup hnonempty hb).1 hx
  have hIcc : IsCompact (Set.Icc (sInf s) (sSup s)) := CompactIccSpace.isCompact_Icc
  rcases hs.exists_accPt_of_subset_isCompact hIcc hsub with ⟨x, _, hx⟩
  exact ⟨x, hx⟩

/-! ## 2. 六大命题（公理形态）—— 循环环的六个顶点 -/

/--
**命题环顶点**：确界原理。任一非空有上界子集都有最小上界。
圆环上它是"最古典"的那个顶点：`analysis.real.sup` 讲的就是它。-/
def SupProperty : Prop :=
  ∀ s : Set ℝ, s.Nonempty → BddAbove s → ∃ a : ℝ, IsLUB s a

/--
**命题环顶点**：单调收敛定理。单调递增且值域有上界的实数列必收敛。
（惯用版本还要求下方有界，但单增序列自动被首项控制住，无需另列。）-/
def MonotoneConvergenceProperty : Prop :=
  ∀ u : ℕ → ℝ, Monotone u → BddAbove (Set.range u) → ∃ l : ℝ, Tendsto u atTop (𝓝 l)

/--
**命题环顶点**：闭区间套定理。嵌套闭区间（aₙ 增、bₙ 减、aₙ ≤ bₙ）之交非空。-/
def NestedIntervalsProperty : Prop :=
  ∀ (a b : ℕ → ℝ), Monotone a → Antitone b → (∀ n, a n ≤ b n) →
    ∃ x : ℝ, ∀ n, x ∈ Set.Icc (a n) (b n)

/--
**命题环顶点**：有限覆盖原理。闭区间的任意开覆盖都有有限子覆盖。-/
def FiniteCoverProperty : Prop :=
  ∀ (a b : ℝ) (ι : Type) (U : ι → Set ℝ),
    (∀ i, IsOpen (U i)) → Set.Icc a b ⊆ ⋃ i, U i →
    ∃ t : Finset ι, ∀ x ∈ Set.Icc a b, ∃ i ∈ t, x ∈ U i

/--
**命题环顶点**：聚点定理。有界无限实集必有聚点。-/
def AccumulationPointProperty : Prop :=
  ∀ s : Set ℝ, s.Infinite → BddAbove s → BddBelow s → ∃ x : ℝ, AccPt x (𝓟 s)

/--
**命题环顶点**：Cauchy 收敛准则。Cauchy 实数列必收敛。-/
def CauchyConvergenceProperty : Prop :=
  ∀ u : ℕ → ℝ, CauchySeq u → ∃ l : ℝ, Tendsto u atTop (𝓝 l)

/-! ## 3. 循环环 —— 六条蕴含（一道一道做） -/

/--
> **Entry**: analysis.completeness.equivalence-cycle.sup-to-mct
> **一句话**: 环的第 1 道：从确界原理推出单调收敛定理。
> **直觉**: 单调递增且被天花板挡住 → 把天花板换成"值域的上确界"，
>   mathlib 的 `tendsto_atTop_ciSup` 正好说"单调 + 有界 ⟹ 收敛到上确界"。
>   这里只是把"上确界存在"这个前提显式地交到 h（SupProperty）手里走一遍。
> **证明类别**: B（语义化组装：h 负责给出 IsLUB，专门定理负责给出收敛）；
>   不涉及手工 ε-N，因为 `tendsto_atTop_ciSup` 已经把最重的力学做完了。
> **依赖**: `analysis.real.sup`（IsLUB 的语言）
> **mathlib**: `tendsto_atTop_ciSup`, `IsLUB.ciSup_eq`
@isnad1 id=monotone.1h0v.s1.66d8f24fc58f from=translated src=- shape=1d48f1ac vocab=bcb174fe
-/
theorem monotone_convergence_of_sup (h : SupProperty) : MonotoneConvergenceProperty := by
  intro u hu hb
  rcases h (Set.range u) (Set.range_nonempty u) hb with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  have ht : Tendsto u atTop (𝓝 (⨆ i : ℕ, u i)) := tendsto_atTop_ciSup hu hb
  simpa [hx.ciSup_eq] using ht

/-- 单调序列收敛于 L ⟹ 每一项都在 L 下方（aₙ ≤ L）。
@isnad1 id=le.2h3v.s5.a733c1fd51a5 from=translated src=- shape=e81db19d vocab=59189f4b
-/
lemma monotone_le_limit {u : ℕ → ℝ} (hu : Monotone u) {L : ℝ}
    (hL : Tendsto u atTop (𝓝 L)) (n : ℕ) : u n ≤ L := by
  by_contra h
  have hpos : 0 < u n - L := sub_pos.mpr (lt_of_not_ge h)
  rcases Metric.tendsto_atTop.mp hL (u n - L) hpos with ⟨N, hN⟩
  let m := max n N
  have htem : |u m - L| < u n - L := by
    simpa [Real.dist_eq] using hN m (le_max_right n N)
  have hue : u n ≤ u m := hu (le_max_left n N)
  have hum : L < u m := lt_of_lt_of_le (lt_of_not_ge h) hue
  have hposm : 0 ≤ u m - L := le_of_lt (sub_pos.mpr hum)
  have hbig : u n - L ≤ |u m - L| := by
    calc
      u n - L ≤ u m - L := sub_le_sub_right hue L
      _ = |u m - L| := (abs_of_nonneg hposm).symm
  linarith

/-- 反单调序列收敛于 L ⟹ 每一项都在 L 上方（L ≤ vₙ）。
@isnad1 id=le.2h3v.s5.da96fbd94ff2 from=translated src=- shape=bd0d1fd2 vocab=a6483e07
-/
lemma antitone_limit_le {v : ℕ → ℝ} (hv : Antitone v) {L : ℝ}
    (hL : Tendsto v atTop (𝓝 L)) (n : ℕ) : L ≤ v n := by
  have hc : Monotone (fun m : ℕ => -v m) := by
    intro m k hmk
    exact neg_le_neg (hv hmk)
  have hcl : Tendsto (fun m : ℕ => -v m) atTop (𝓝 (-L)) := hL.neg
  have hlt : -(v n) ≤ -L := monotone_le_limit hc hcl n
  nlinarith

/--
> **Entry**: analysis.completeness.equivalence-cycle.mct-to-nested-intervals
> **一句话**: 环的第 2 道：从单调收敛定理推出闭区间套定理。
> **直觉**: aₙ 单调递增且被 b₀ 挡住 → 收敛到 x₁；
>   -bₙ 单调递增且被 -a₀ 挡住 → 收敛到 y，即 bₙ 收敛到 -y。
>   关键落点：x₁ ≤ -y（对区间长度做中点裁决），于是 x₁ 落在每个 [aₙ, bₙ] 里。
> **证明类别**: B（真刀真枪的 ε 论证，但只做了一次"中间点裁决"，其余由单调性包揽）。
> **依赖**: `analysis.completeness.equivalence-cycle.sup-to-mct`（同款思想）
> **mathlib**: `Metric.tendsto_atTop`, `abs_lt`, `Filter.Tendsto.neg`
@isnad1 id=nestedin.1h0v.s1.702004eeb6b1 from=translated src=- shape=1d48f1ac vocab=b4b0a715
-/
theorem nested_intervals_of_monotone_convergence
    (h : MonotoneConvergenceProperty) : NestedIntervalsProperty := by
  intro a b hma hnb hle
  have hba : BddAbove (Set.range a) := by
    refine ⟨b 0, ?_⟩
    intro x hx
    rcases hx with ⟨k, rfl⟩
    calc
      a k ≤ b k := hle k
      _ ≤ b 0 := hnb (by norm_num : 0 ≤ k)
  rcases h a hma hba with ⟨x, hxa⟩
  let c : ℕ → ℝ := fun n => -b n
  have hmc : Monotone c := by
    intro m k hmk
    dsimp [c]
    exact neg_le_neg (hnb hmk)
  have hbc : BddAbove (Set.range c) := by
    refine ⟨-a 0, ?_⟩
    intro y hy
    rcases hy with ⟨k, rfl⟩
    dsimp [c]
    calc
      -b k ≤ -a k := neg_le_neg (hle k)
      _ ≤ -a 0 := neg_le_neg (hma (by norm_num : 0 ≤ k))
  rcases h c hmc hbc with ⟨y, hyc⟩
  have hxb : Tendsto b atTop (𝓝 (-y)) := by
    simpa [c] using hyc.neg
  have hxy : x ≤ -y := by
    by_contra hgt
    have hlt : -y < x := lt_of_not_ge hgt
    let e : ℝ := (x + y) / 2
    have he : 0 < e := by
      dsimp [e]
      have hpos : 0 < x + y := by linarith
      exact div_pos hpos (by norm_num)
    rcases Metric.tendsto_atTop.mp hxa e he with ⟨N₁, hN₁⟩
    rcases Metric.tendsto_atTop.mp hxb e he with ⟨N₂, hN₂⟩
    let N := max N₁ N₂
    have hN1 : N₁ ≤ N := le_max_left N₁ N₂
    have hN2 : N₂ ≤ N := le_max_right N₁ N₂
    have haN : |a N - x| < e := by
      simpa [Real.dist_eq] using hN₁ N hN1
    have hbN : |b N - (-y)| < e := by
      simpa [Real.dist_eq] using hN₂ N hN2
    have haL : x - e < a N := by
      have h₁ : -(e) < a N - x := (abs_lt.mp haN).1
      linarith
    have hbR : b N < -y + e := by
      have h₂ : b N - (-y) < e := (abs_lt.mp hbN).2
      linarith
    have hmid : x - e = -y + e := by
      dsimp [e]
      ring
    have hgtN : b N < a N := by
      dsimp [e] at *
      nlinarith
    exact (lt_irrefl (a N)) (lt_of_le_of_lt (hle N) hgtN)
  refine ⟨x, ?_⟩
  intro n
  constructor
  · exact monotone_le_limit hma hxa n
  · exact le_trans hxy (antitone_limit_le hnb hxb n)

/-! ### 第三道（C 类）：闭区间套 ⟹ 有限覆盖 —— 二分反证
引理清单（§0 铁律4：一次只做一条，逐条编译）：
1. `NoFiniteCover U l r`：谓词，"对 [l,r] 无有限子覆盖"。
2. `halfbiseq U a b n`：二分进程，(lₙ, rₙ)。
3. `finite_cover_halves`：左右半各有有限子覆盖 ⟹ 整段有。
4. `right_half_no_finite_cover`：整段无且左半有 ⟹ 右半无。
5. `halfbiseq_length`：rₙ − lₙ = (b − a)/2ⁿ。
6. `halfbiseq_le`：lₙ ≤ rₙ；`halfbiseq_left_mono_step` / `halfbiseq_right_antitone_step`。
7. `halfbiseq_nofinite_cover`：无有限子覆盖性质逐层传递。
8. `finite_cover_of_nested_intervals`：主定理（NIT h 得公共点 x → 开集收纳 → 矛盾）。
-/

/-- 谓词：开覆盖列 {Uᵢ} 对 [l, r] 没有有限子覆盖。-/
def NoFiniteCover (U : ι → Set ℝ) (l r : ℝ) : Prop :=
  ¬ ∃ t : Finset ι, ∀ x ∈ Set.Icc l r, ∃ i ∈ t, x ∈ U i

/-- `NoFiniteCover` 的判定（非计算，供二分进程的 `if` 使用）。-/
noncomputable instance NoFiniteCover.decidable (U : ι → Set ℝ) (l r : ℝ) :
    Decidable (NoFiniteCover U l r) := by
  classical
  infer_instance

/-- 二分进程：每层取中点；(lₙ, rₙ) 表示第 n 层的区间，长度为 (b−a)/2ⁿ。-/
noncomputable def halfbiseq (U : ι → Set ℝ) (a b : ℝ) : ℕ → ℝ × ℝ
  | 0 => (a, b)
  | n + 1 =>
      let (l, r) := halfbiseq U a b n
      if _h : NoFiniteCover U l ((l + r) / 2) then (l, (l + r) / 2)
      else ((l + r) / 2, r)

/-- 中点分裂：若左右两半各有一族有限子覆盖，合起来覆盖整段，故此段也有限可覆盖。
@isnad1 id=ex.4h5v.s7.33f96ebcb5c7 from=translated src=- shape=e952343a vocab=06507150
-/
lemma finite_cover_halves (U : ι → Set ℝ) {l m r : ℝ} (_hlm : l ≤ m) (_hmr : m ≤ r)
    (hc₁ : ∃ t : Finset ι, ∀ x ∈ Set.Icc l m, ∃ i ∈ t, x ∈ U i)
    (hc₂ : ∃ t : Finset ι, ∀ x ∈ Set.Icc m r, ∃ i ∈ t, x ∈ U i) :
    ∃ t : Finset ι, ∀ x ∈ Set.Icc l r, ∃ i ∈ t, x ∈ U i := by
  classical
  rcases hc₁ with ⟨t₁, ht₁⟩
  rcases hc₂ with ⟨t₂, ht₂⟩
  refine ⟨t₁ ∪ t₂, ?_⟩
  intro x hx
  by_cases hxm : x ≤ m
  · rcases ht₁ x ⟨hx.1, hxm⟩ with ⟨i, hit, hxi⟩
    exact ⟨i, ⟨Finset.mem_union_left t₂ hit, hxi⟩⟩
  · have hmx : m ≤ x := le_of_not_ge hxm
    rcases ht₂ x ⟨hmx, hx.2⟩ with ⟨i, hit, hxi⟩
    exact ⟨i, ⟨Finset.mem_union_right t₁ hit, hxi⟩⟩

/-- 二分保持性质：整段无有限子覆盖、左半有有限子覆盖 ⟹ 右半必无有限子覆盖。
@isnad1 id=nofinite.4h5v.s5.9c5a507eb70e from=translated src=- shape=902269a1 vocab=00986864
-/
lemma right_half_no_finite_cover (U : ι → Set ℝ) {l m r : ℝ} (hlm : l ≤ m) (hmr : m ≤ r)
    (hnc : NoFiniteCover U l r) (hnl : ¬ NoFiniteCover U l m) : NoFiniteCover U m r := by
  classical
  intro h
  rcases (Classical.not_not.mp hnl) with ⟨t₁, ht₁⟩
  rcases h with ⟨t₂, ht₂⟩
  exact hnc (finite_cover_halves U hlm hmr ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩)

/-- 二分每层长度恰好减半：lenₙ₊₁ = lenₙ / 2。
@isnad1 id=eq.0h5v.s6.e01de573c9aa from=translated src=- shape=439f2508 vocab=1d88cc94
-/
lemma halfbiseq_length_step (U : ι → Set ℝ) (a b : ℝ) (n : ℕ) :
    (halfbiseq U a b (n + 1)).2 - (halfbiseq U a b (n + 1)).1
      = ((halfbiseq U a b n).2 - (halfbiseq U a b n).1) / 2 := by
  by_cases h : NoFiniteCover U (halfbiseq U a b n).1 (((halfbiseq U a b n).1 + (halfbiseq U a b n).2) / 2)
  · simp only [halfbiseq]
    rw [dite_eq_left h]
    ring
  · simp only [halfbiseq]
    rw [dite_eq_right h]
    ring

/-- 二分各层的长度：rₙ − lₙ = (b − a) / 2ⁿ。
@isnad1 id=eq.0h5v.s6.7d4e4198f20a from=translated src=- shape=f28076c2 vocab=f7a17587
-/
lemma halfbiseq_length (U : ι → Set ℝ) (a b : ℝ) :
    ∀ n, (halfbiseq U a b n).2 - (halfbiseq U a b n).1 = (b - a) / 2 ^ n := by
  intro n
  induction n with
  | zero => simp [halfbiseq]
  | succ n ih =>
      rw [halfbiseq_length_step]
      rw [ih]
      field_simp
      ring

/-- 二分各层保持 lₙ ≤ rₙ（a ≤ b 起步）。
@isnad1 id=le.1h5v.s5.8bd67cb6cc03 from=translated src=- shape=0b5e0a91 vocab=51332401
-/
lemma halfbiseq_le (U : ι → Set ℝ) (a b : ℝ) (hab : a ≤ b) :
    ∀ n, (halfbiseq U a b n).1 ≤ (halfbiseq U a b n).2 := by
  intro n
  induction n with
  | zero => simpa [halfbiseq] using hab
  | succ n ih =>
      by_cases h : NoFiniteCover U (halfbiseq U a b n).1 (((halfbiseq U a b n).1 + (halfbiseq U a b n).2) / 2)
      · simp only [halfbiseq]
        rw [dite_eq_left h]
        nlinarith
      · simp only [halfbiseq]
        rw [dite_eq_right h]
        nlinarith

/-- 左端点单调不减：lₙ ≤ lₙ₊₁。
@isnad1 id=le.1h5v.s5.a897e7817d7f from=translated src=- shape=697e88bc vocab=77a9c479
-/
lemma halfbiseq_left_mono_step (U : ι → Set ℝ) (a b : ℝ) (hab : a ≤ b) (n : ℕ) :
    (halfbiseq U a b n).1 ≤ (halfbiseq U a b (n + 1)).1 := by
  by_cases h : NoFiniteCover U (halfbiseq U a b n).1 (((halfbiseq U a b n).1 + (halfbiseq U a b n).2) / 2)
  · simp only [halfbiseq]
    rw [dite_eq_left h]
  · simp only [halfbiseq]
    rw [dite_eq_right h]
    have hle : (halfbiseq U a b n).1 ≤ (halfbiseq U a b n).2 := halfbiseq_le U a b hab n
    nlinarith

/-- 右端点单调不增：rₙ₊₁ ≤ rₙ。
@isnad1 id=le.1h5v.s5.23adfa9ce48c from=translated src=- shape=eb295128 vocab=8e28bf24
-/
lemma halfbiseq_right_antitone_step (U : ι → Set ℝ) (a b : ℝ) (hab : a ≤ b) (n : ℕ) :
    (halfbiseq U a b (n + 1)).2 ≤ (halfbiseq U a b n).2 := by
  by_cases h : NoFiniteCover U (halfbiseq U a b n).1 (((halfbiseq U a b n).1 + (halfbiseq U a b n).2) / 2)
  · simp only [halfbiseq]
    rw [dite_eq_left h]
    have hle : (halfbiseq U a b n).1 ≤ (halfbiseq U a b n).2 := halfbiseq_le U a b hab n
    nlinarith
  · simp only [halfbiseq]
    rw [dite_eq_right h]

/-- 无有限子覆盖性质逐层传递：整段无 ⟹ 每一层区间都无。
@isnad1 id=nofinite.2h5v.s5.e2e6e9f367d2 from=translated src=- shape=e7b728aa vocab=21afd780
-/
lemma halfbiseq_nofinite_cover (U : ι → Set ℝ) {a b : ℝ} (hab : a ≤ b)
    (hnc : NoFiniteCover U a b) :
    ∀ n, NoFiniteCover U (halfbiseq U a b n).1 (halfbiseq U a b n).2 := by
  intro n
  induction n with
  | zero => simpa [halfbiseq] using hnc
  | succ n ih =>
      have hlr : (halfbiseq U a b n).1 ≤ (halfbiseq U a b n).2 := halfbiseq_le U a b hab n
      have hlm : (halfbiseq U a b n).1 ≤ ((halfbiseq U a b n).1 + (halfbiseq U a b n).2) / 2 := by
        nlinarith
      have hmr : ((halfbiseq U a b n).1 + (halfbiseq U a b n).2) / 2 ≤ (halfbiseq U a b n).2 := by
        nlinarith
      by_cases h : NoFiniteCover U (halfbiseq U a b n).1 (((halfbiseq U a b n).1 + (halfbiseq U a b n).2) / 2)
      · simp only [halfbiseq]
        rw [dite_eq_left h]
        exact h
      · simp only [halfbiseq]
        rw [dite_eq_right h]
        exact right_half_no_finite_cover U hlm hmr ih h

/--
> **Entry**: analysis.completeness.equivalence-cycle.nested-intervals-to-finite-cover
> **一句话**: 环的第 3 道：从闭区间套定理推出有限覆盖原理。
> **直觉**: 反证——若 [a,b] 无有限子覆盖，则二分下去每层都有一半仍无有限子覆盖，
>   得嵌套闭区间套；闭区间套定理给公共点 x；x 被某个开集 Uᵢ 连同一小段 [lₙ,rₙ] 整个包住，
>   于是 [lₙ,rₙ] 其实被单个 Uᵢ 覆盖，与"每层都无有限子覆盖"矛盾。
> **证明类别**: C（核心手工构造：二分进程 halfbiseq 的全程机械构造 + 末端 ε 球收纳）。
> **依赖**: 本文件 §3 的 `halfbiseq_*` 引理族、`right_half_no_finite_cover`
> **mathlib**: `monotone_nat_of_le_succ`, `antitone_nat_of_succ_le`,
>   `Metric.isOpen_iff`, `tendsto_pow_atTop_nhds_zero_of_norm_lt_one`
@isnad1 id=finiteco.1h0v.s1.9738c743f28b from=translated src=- shape=1d48f1ac vocab=f6fe5d05
-/
theorem finite_cover_of_nested_intervals (h : NestedIntervalsProperty) : FiniteCoverProperty := by
  intro a b ι U hUo hcover
  by_cases hab : a ≤ b
  · by_contra hnoc
    have hnf : NoFiniteCover U a b := hnoc
    let A : ℕ → ℝ := fun n => (halfbiseq U a b n).1
    let B : ℕ → ℝ := fun n => (halfbiseq U a b n).2
    have hmonoA : Monotone A := by
      refine monotone_nat_of_le_succ ?_
      intro n
      simpa [A] using halfbiseq_left_mono_step U a b hab n
    have hantiB : Antitone B := by
      refine antitone_nat_of_succ_le ?_
      intro n
      simpa [B] using halfbiseq_right_antitone_step U a b hab n
    have hleAB : ∀ n, A n ≤ B n := by
      intro n
      simpa [A, B] using halfbiseq_le U a b hab n
    rcases h A B hmonoA hantiB hleAB with ⟨x, hx⟩
    have hxab : x ∈ Set.Icc a b := by
      have h0 := hx 0
      simpa [A, B, halfbiseq] using h0
    rcases (Set.mem_iUnion.mp (hcover hxab)) with ⟨i₀, hxi₀⟩
    rcases (Metric.isOpen_iff.mp (hUo i₀)) x hxi₀ with ⟨ε, hεpos, hε⟩
    have hlen_tendsto : Tendsto (fun n : ℕ => B n - A n) atTop (𝓝 0) := by
      have hpow : Tendsto (fun n : ℕ => ((1 / 2 : ℝ) ^ n)) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)
      have hscaled : Tendsto (fun n : ℕ => (b - a) * ((1 / 2 : ℝ) ^ n)) atTop (𝓝 0) := by
        simpa using hpow.const_mul (b - a)
      have heq : (fun n : ℕ => B n - A n) = (fun n : ℕ => (b - a) * ((1 / 2 : ℝ) ^ n)) := by
        funext n
        have hlen : B n - A n = (b - a) / 2 ^ n := by
          simpa [A, B] using halfbiseq_length U a b n
        rw [hlen]
        rw [one_div_pow]
        field_simp
      simpa [heq] using hscaled
    rcases Metric.tendsto_atTop.mp hlen_tendsto ε hεpos with ⟨N, hN⟩
    have hN' : |B N - A N| < ε := by
      simpa [Real.dist_eq] using hN N (le_refl N)
    have hnonneg : 0 ≤ B N - A N := sub_nonneg.mpr (hleAB N)
    have hlenN : B N - A N < ε := by
      rwa [abs_of_nonneg hnonneg] at hN'
    have hsub : Set.Icc (A N) (B N) ⊆ U i₀ := by
      intro y hy
      have hxN : x ∈ Set.Icc (A N) (B N) := hx N
      have hdx : dist y x ≤ B N - A N := by
        rw [Real.dist_eq, abs_le]
        constructor <;> nlinarith [hy.1, hy.2, hxN.1, hxN.2]
      exact hε (lt_of_le_of_lt hdx hlenN)
    have hnfN : NoFiniteCover U (A N) (B N) := by
      simpa [A, B] using (halfbiseq_nofinite_cover U hab hnf) N
    have hcover_single : ∃ t : Finset ι, ∀ y ∈ Set.Icc (A N) (B N), ∃ i ∈ t, y ∈ U i := by
      refine ⟨{i₀}, ?_⟩
      intro y hy
      exact ⟨i₀, by simp, hsub hy⟩
    exact hnfN hcover_single
  · refine ⟨∅, ?_⟩
    intro x hx
    have hab' : a ≤ b := le_trans hx.1 hx.2
    exact absurd hab' hab

/-! ### 第四道（B 类）：有限覆盖 ⟹ 聚点 —— 反证 + 开覆盖构造 -/

/-- 非聚点的开邻域刻画：x 不是 s 的聚点 ⟺ 存在邻域 U，U 里 s 的点至多只有 x 自己。
@isnad1 id=iff.0h2v.s5.39433363dbd6 from=translated src=- shape=7fd58918 vocab=21972fc9
-/
lemma not_accPt_iff_exists_nhds {s : Set ℝ} {x : ℝ} :
    ¬ AccPt x (𝓟 s) ↔ ∃ U ∈ 𝓝 x, U ∩ s ⊆ {x} := by
  constructor
  · intro h
    rw [accPt_iff_nhds] at h
    push Not at h
    rcases h with ⟨U, hU, hsub⟩
    refine ⟨U, hU, ?_⟩
    intro y hy
    exact Set.mem_singleton_iff.mpr (hsub y hy)
  · intro h
    rcases h with ⟨U, hU, hsub⟩
    rw [accPt_iff_nhds]
    push Not
    refine ⟨U, hU, ?_⟩
    intro y hy
    exact Set.mem_singleton_iff.mp (hsub hy)

/--
> **Entry**: analysis.completeness.equivalence-cycle.finite-cover-to-accumulation-point
> **一句话**: 环的第 4 道：从有限覆盖原理推出聚点定理。
> **直觉**: 反证——若有界无限集 s 无聚点，则每个点 x 都有一个开邻域只与 s 交于（至多）x 自己；
>   这些邻域盖住包裹 s 的闭区间，有限覆盖抽出的有限个邻域里 s 至多有限个点，与 s 无限矛盾。
> **证明类别**: B（反证 + 开覆盖构造 + 有限子覆盖收尾，无重型手工 ε）。
> **依赖**: 本文件 §3 `not_accPt_iff_exists_nhds`
> **mathlib**: `accPt_iff_nhds`, `Metric.mem_nhds_iff`, `Metric.mem_ball_self`,
>   `Finset.finite_toSet`, `Set.Infinite.not_finite`
@isnad1 id=accumula.1h0v.s1.c986610bf432 from=translated src=- shape=1d48f1ac vocab=255956ed
-/
theorem accumulation_point_of_finite_cover (h : FiniteCoverProperty) : AccumulationPointProperty := by
  intro s hs_inf hb_above hb_below
  have hnonempty : s.Nonempty := hs_inf.nonempty
  have hsub : s ⊆ Set.Icc (sInf s) (sSup s) := by
    intro x hx
    constructor
    · exact (isGLB_csInf hnonempty hb_below).1 hx
    · exact (Real.isLUB_sSup hnonempty hb_above).1 hx
  by_contra hno
  push Not at hno
  have hnbhd : ∀ x : ℝ, ∃ U : Set ℝ, IsOpen U ∧ x ∈ U ∧ U ∩ s ⊆ {x} := by
    intro x
    rcases (not_accPt_iff_exists_nhds.mp (hno x)) with ⟨U, hU, hsubU⟩
    rcases Metric.mem_nhds_iff.mp hU with ⟨ε, hεpos, hball⟩
    refine ⟨Metric.ball x ε, Metric.isOpen_ball, Metric.mem_ball_self hεpos, ?_⟩
    intro y hy
    exact hsubU ⟨hball hy.1, hy.2⟩
  choose U hUo hUx hUsub using hnbhd
  have hcover' : Set.Icc (sInf s) (sSup s) ⊆ ⋃ x, U x := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨x, hUx x⟩
  rcases h (sInf s) (sSup s) ℝ U hUo hcover' with ⟨t, ht⟩
  have hsub_fin : s ⊆ (t : Set ℝ) := by
    intro y hy
    have hycc : y ∈ Set.Icc (sInf s) (sSup s) := hsub hy
    rcases ht y hycc with ⟨i, hit, hyi⟩
    have hy_eq_i : y = i := Set.mem_singleton_iff.mp (hUsub i ⟨hyi, hy⟩)
    simpa [hy_eq_i] using hit
  have hfin : s.Finite := (Finset.finite_toSet t).subset hsub_fin
  exact hs_inf.not_finite hfin

/-! ### 第五道（C 类）：聚点 ⟹ Cauchy 收敛 —— 有界 + 聚点 + 子列 -/

/-- Cauchy 序列有界：值域上下有界。
@isnad1 id=and.1h1v.s4.f3c54d1703c0 from=translated src=- shape=c6f5f4de vocab=cd29b7c1
-/
lemma cauchy_seq_bounded {u : ℕ → ℝ} (hu : CauchySeq u) :
    BddAbove (Set.range u) ∧ BddBelow (Set.range u) := by
  rcases cauchySeq_bdd hu with ⟨R, _hR, hbd⟩
  have hbd0 : ∀ n, |u n - u 0| < R := by
    intro n
    simpa [Real.dist_eq] using hbd n 0
  constructor
  · refine ⟨u 0 + R, ?_⟩
    intro y hy
    rcases hy with ⟨n, rfl⟩
    have hle : u n - u 0 ≤ R := (abs_le.mp (le_of_lt (hbd0 n))).2
    linarith
  · refine ⟨u 0 - R, ?_⟩
    intro y hy
    rcases hy with ⟨n, rfl⟩
    have hle : -R ≤ u n - u 0 := (abs_le.mp (le_of_lt (hbd0 n))).1
    linarith

/-- 核心桥：x 是 range u 的聚点 ⟹ x 是序列 u 的 cluster point（沿 atTop）。
@isnad1 id=mapclust.1h2v.s5.13b7c15f3eac from=translated src=- shape=5f7c27d3 vocab=efdf35b7
-/
lemma mapClusterPt_of_accPt_range {u : ℕ → ℝ} {x : ℝ}
    (h : AccPt x (𝓟 (Set.range u))) : MapClusterPt x atTop u := by
  rw [mapClusterPt_iff_frequently]
  intro s hs
  rw [Nat.frequently_atTop_iff_infinite]
  by_contra hfin
  have hpre : Set.Finite {n : ℕ | u n ∈ s} := by
    classical
    exact not_not.mp hfin
  have hfinite_inter : (s ∩ Set.range u).Finite := by
    have himg : s ∩ Set.range u ⊆ (fun n : ℕ => u n) '' {n : ℕ | u n ∈ s} := by
      intro y hy
      rcases hy.2 with ⟨n, rfl⟩
      exact ⟨n, hy.1, rfl⟩
    exact Set.Finite.subset (Set.Finite.image (fun n : ℕ => u n) hpre) himg
  have hfinite_sdiff : (s ∩ (Set.range u \ {x})).Finite := by
    exact Set.Finite.subset hfinite_inter (by intro y hy; exact ⟨hy.1, hy.2.1⟩)
  have hacc : ClusterPt x (𝓟 (Set.range u \ {x})) := accPt_principal_iff_clusterPt.mp h
  have hclosed : IsClosed (s ∩ (Set.range u \ {x})) := hfinite_sdiff.isClosed
  have hx_notin : x ∉ s ∩ (Set.range u \ {x}) := by
    intro hx'
    exact hx'.2.2 rfl
  have hcompl_nhds : (s ∩ (Set.range u \ {x}))ᶜ ∈ 𝓝 x :=
    IsOpen.mem_nhds hclosed.isOpen_compl hx_notin
  have hs' : s ∩ (s ∩ (Set.range u \ {x}))ᶜ ∈ 𝓝 x := Filter.inter_mem hs hcompl_nhds
  have hnonempty := (clusterPt_principal_iff.mp hacc) (s ∩ (s ∩ (Set.range u \ {x}))ᶜ) hs'
  rcases hnonempty with ⟨y, hy⟩
  exact hy.1.2 ⟨hy.1.1, hy.2⟩

/-- Cauchy 序列的聚点即其极限。
@isnad1 id=tendsto.2h2v.s5.387f8bf9d451 from=translated src=- shape=16647608 vocab=9041e148
-/
lemma tendsto_of_cauchySeq_of_accPt_range {u : ℕ → ℝ} (hu : CauchySeq u) {x : ℝ}
    (hx : AccPt x (𝓟 (Set.range u))) : Tendsto u atTop (𝓝 x) := by
  have hmap : MapClusterPt x atTop u := mapClusterPt_of_accPt_range hx
  rcases MapClusterPt.tendsto_subseq hmap with ⟨φ, hφ, hsub⟩
  exact tendsto_nhds_of_cauchySeq_of_subseq hu hφ.tendsto_atTop hsub

/-- 有限值域的 Cauchy 列收敛：鸽笼得常值子列，Cauchy 再把它拉成整体收敛。
@isnad1 id=ex.2h1v.s5.8bd79bc43f62 from=translated src=- shape=ef486da8 vocab=92543105
-/
lemma cauchySeq_tendsto_of_finite_range {u : ℕ → ℝ} (hu : CauchySeq u)
    (hfin : (Set.range u).Finite) : ∃ l : ℝ, Tendsto u atTop (𝓝 l) := by
  have hinf_fiber : ∃ c ∈ Set.range u, Set.Infinite {m : ℕ | u m = c} := by
    by_contra hno
    have hall : ∀ c ∈ Set.range u, Set.Finite {m : ℕ | u m = c} := by
      intro c hc
      exact not_not.mp (by intro hinf; exact hno ⟨c, hc, hinf⟩)
    have hfinite_union : (⋃ c ∈ Set.range u, {m : ℕ | u m = c}).Finite :=
      Set.Finite.biUnion hfin hall
    have hcov : (Set.univ : Set ℕ) ⊆ ⋃ c ∈ Set.range u, {m : ℕ | u m = c} := by
      intro n _
      exact Set.mem_biUnion ⟨n, rfl⟩ rfl
    have hfin_nat : (Set.univ : Set ℕ).Finite := hfinite_union.subset hcov
    exact Set.infinite_univ.not_finite hfin_nat
  rcases hinf_fiber with ⟨c, _hc, hinf⟩
  rcases Nat.exists_strictMono_subsequence (P := fun n => u n = c) (by
    intro N
    rcases Set.Infinite.exists_gt hinf (N + 1) with ⟨n, hnc, hn⟩
    exact ⟨n, by omega, hnc⟩) with ⟨φ, hφ, hφc⟩
  have hsub : Tendsto (u ∘ φ) atTop (𝓝 c) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    refine ⟨0, ?_⟩
    intro n _hn
    simpa [hφc n, Real.dist_eq] using hε
  exact ⟨c, tendsto_nhds_of_cauchySeq_of_subseq hu hφ.tendsto_atTop hsub⟩

/--
> **Entry**: analysis.completeness.equivalence-cycle.accumulation-point-to-cauchy
> **一句话**: 环的第 5 道：从聚点定理推出 Cauchy 收敛准则。
> **直觉**: Cauchy 列必有界；值域无限则聚点定理给聚点，聚点即极限；
>   值域有限则鸽笼给常值子列，Cauchy 再把它拉成整体收敛。
> **证明类别**: C（核心手工构造：聚点→cluster point 的桥 + 鸽笼 + 子列拉平）。
> **依赖**: 本文件 §3 `cauchy_seq_bounded`、`mapClusterPt_of_accPt_range`、
>   `tendsto_of_cauchySeq_of_accPt_range`、`cauchySeq_tendsto_of_finite_range`
> **mathlib**: `cauchySeq_bdd`, `Nat.exists_strictMono_subsequence`,
>   `tendsto_nhds_of_cauchySeq_of_subseq`, `Set.Finite.biUnion`
@isnad1 id=cauchyco.1h0v.s1.e98041ad50d0 from=translated src=- shape=1d48f1ac vocab=98db7acc
-/
theorem cauchy_convergence_of_accumulation_point (h : AccumulationPointProperty) :
    CauchyConvergenceProperty := by
  intro u hu
  by_cases hfin : (Set.range u).Finite
  · exact cauchySeq_tendsto_of_finite_range hu hfin
  · have hb := cauchy_seq_bounded hu
    have hinf : (Set.range u).Infinite := hfin
    rcases h (Set.range u) hinf hb.1 hb.2 with ⟨x, hx⟩
    exact ⟨x, tendsto_of_cauchySeq_of_accPt_range hu hx⟩

/-! ### 第六道（C 类）：Cauchy ⟹ 确界 —— 二分逼近上确界
引理清单（§0 铁律4：一次只做一条，逐条编译）：
1. `bisect_upper`：二分找上确界的进程，`(lₙ, rₙ)`。
2. `bisect_upper_le`：lₙ ≤ rₙ；`bisect_upper_left_mono_step` / `right_antitone_step`。
3. `bisect_upper_length`：rₙ − lₙ = (b − a)/2ⁿ。
4. `bisect_upper_right_upper`：rₙ 恒为 s 的上界（不变量）。
5. `bisect_upper_left_not_upper`：lₙ 恒非 s 的上界（不变量）。
6. `bisect_upper_left_cauchy` / `right_cauchy`：两侧序列都是 Cauchy。
7. `sup_of_cauchy_convergence`：主定理（Cauchy 给极限 x，x 是 s 的上确界）。
-/

/-- `upperBounds s` 的可判定性（非计算，供二分进程的 `if` 使用）。-/
noncomputable instance upperBounds.decidable (s : Set ℝ) (x : ℝ) :
    Decidable (x ∈ upperBounds s) := by
  classical
  infer_instance

/-- 二分进程：每层取中点；中点仍是上界则右端收缩，否则左端右移。-/
noncomputable def bisect_upper (s : Set ℝ) (a b : ℝ) : ℕ → ℝ × ℝ
  | 0 => (a, b)
  | n + 1 =>
      let (l, r) := bisect_upper s a b n
      if _h : (l + r) / 2 ∈ upperBounds s then (l, (l + r) / 2)
      else ((l + r) / 2, r)

/-- 二分各层保持 lₙ ≤ rₙ。
@isnad1 id=le.1h4v.s5.f3d20616926a from=translated src=- shape=14d82cc9 vocab=553be030
-/
lemma bisect_upper_le (s : Set ℝ) (a b : ℝ) (hab : a ≤ b) :
    ∀ n, (bisect_upper s a b n).1 ≤ (bisect_upper s a b n).2 := by
  intro n
  induction n with
  | zero => simpa [bisect_upper] using hab
  | succ n ih =>
      by_cases h : ((bisect_upper s a b n).1 + (bisect_upper s a b n).2) / 2 ∈ upperBounds s
      · simp only [bisect_upper]
        rw [dite_eq_left h]
        nlinarith
      · simp only [bisect_upper]
        rw [dite_eq_right h]
        nlinarith

/-- 左端点单调不减。
@isnad1 id=le.1h4v.s5.4d50f9cb0228 from=translated src=- shape=3e1ad1ad vocab=b2d20568
-/
lemma bisect_upper_left_mono_step (s : Set ℝ) (a b : ℝ) (hab : a ≤ b) (n : ℕ) :
    (bisect_upper s a b n).1 ≤ (bisect_upper s a b (n + 1)).1 := by
  by_cases h : ((bisect_upper s a b n).1 + (bisect_upper s a b n).2) / 2 ∈ upperBounds s
  · simp only [bisect_upper]
    rw [dite_eq_left h]
  · simp only [bisect_upper]
    rw [dite_eq_right h]
    have hle : (bisect_upper s a b n).1 ≤ (bisect_upper s a b n).2 := bisect_upper_le s a b hab n
    nlinarith

/-- 右端点单调不增。
@isnad1 id=le.1h4v.s5.5487bc8b95de from=translated src=- shape=51504691 vocab=3e34e717
-/
lemma bisect_upper_right_antitone_step (s : Set ℝ) (a b : ℝ) (hab : a ≤ b) (n : ℕ) :
    (bisect_upper s a b (n + 1)).2 ≤ (bisect_upper s a b n).2 := by
  by_cases h : ((bisect_upper s a b n).1 + (bisect_upper s a b n).2) / 2 ∈ upperBounds s
  · simp only [bisect_upper]
    rw [dite_eq_left h]
    have hle : (bisect_upper s a b n).1 ≤ (bisect_upper s a b n).2 := bisect_upper_le s a b hab n
    nlinarith
  · simp only [bisect_upper]
    rw [dite_eq_right h]

/-- 二分每层长度恰好减半。
@isnad1 id=eq.0h4v.s6.f1fd74213202 from=translated src=- shape=eb2238c4 vocab=d089d676
-/
lemma bisect_upper_length_step (s : Set ℝ) (a b : ℝ) (n : ℕ) :
    (bisect_upper s a b (n + 1)).2 - (bisect_upper s a b (n + 1)).1
      = ((bisect_upper s a b n).2 - (bisect_upper s a b n).1) / 2 := by
  by_cases h : ((bisect_upper s a b n).1 + (bisect_upper s a b n).2) / 2 ∈ upperBounds s
  · simp only [bisect_upper]
    rw [dite_eq_left h]
    ring
  · simp only [bisect_upper]
    rw [dite_eq_right h]
    ring

/-- 二分各层长度：rₙ − lₙ = (b − a) / 2ⁿ。
@isnad1 id=eq.0h4v.s6.8cc51bcddc19 from=translated src=- shape=7d297913 vocab=e1fe9faf
-/
lemma bisect_upper_length (s : Set ℝ) (a b : ℝ) :
    ∀ n, (bisect_upper s a b n).2 - (bisect_upper s a b n).1 = (b - a) / 2 ^ n := by
  intro n
  induction n with
  | zero => simp [bisect_upper]
  | succ n ih =>
      rw [bisect_upper_length_step]
      rw [ih]
      field_simp
      ring

/-- 不变量：右端点 rₙ 恒为 s 的上界。
@isnad1 id=mem.1h4v.s5.19c214d836ad from=translated src=- shape=9c227ce7 vocab=5cc03950
-/
lemma bisect_upper_right_upper (s : Set ℝ) {a b : ℝ} (hb : b ∈ upperBounds s) :
    ∀ n, (bisect_upper s a b n).2 ∈ upperBounds s := by
  intro n
  induction n with
  | zero => simpa [bisect_upper] using hb
  | succ n ih =>
      by_cases h : ((bisect_upper s a b n).1 + (bisect_upper s a b n).2) / 2 ∈ upperBounds s
      · simp only [bisect_upper]
        rw [dite_eq_left h]
        exact h
      · simp only [bisect_upper]
        rw [dite_eq_right h]
        exact ih

/-- 不变量：左端点 lₙ 恒非 s 的上界。
@isnad1 id=not.1h4v.s5.f9ec51493e85 from=translated src=- shape=0a6e4c6e vocab=d5a10980
-/
lemma bisect_upper_left_not_upper (s : Set ℝ) {a b : ℝ} (ha : a ∉ upperBounds s) :
    ∀ n, (bisect_upper s a b n).1 ∉ upperBounds s := by
  intro n
  induction n with
  | zero => simpa [bisect_upper] using ha
  | succ n ih =>
      by_cases h : ((bisect_upper s a b n).1 + (bisect_upper s a b n).2) / 2 ∈ upperBounds s
      · simp only [bisect_upper]
        rw [dite_eq_left h]
        exact ih
      · simp only [bisect_upper]
        rw [dite_eq_right h]
        exact h

/-- 二分左端点序列 lₙ 是 Cauchy：区间直径趋于 0，lₙ 夹在 [l_N, r_N] 里。
@isnad1 id=cauchyse.1h3v.s4.3a52144bde9c from=translated src=- shape=b3420b51 vocab=0b92cec0
-/
lemma bisect_upper_left_cauchy (s : Set ℝ) {a b : ℝ} (hab : a ≤ b) :
    CauchySeq (fun n => (bisect_upper s a b n).1) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have htend : Tendsto (fun n : ℕ => (b - a) / 2 ^ n) atTop (𝓝 0) := by
    have hpow : Tendsto (fun n : ℕ => ((1 / 2 : ℝ) ^ n)) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)
    have hscaled : Tendsto (fun n : ℕ => (b - a) * ((1 / 2 : ℝ) ^ n)) atTop (𝓝 0) := by
      simpa using hpow.const_mul (b - a)
    have heq : (fun n : ℕ => (b - a) / 2 ^ n) = (fun n : ℕ => (b - a) * ((1 / 2 : ℝ) ^ n)) := by
      funext n
      rw [one_div_pow]
      field_simp
    simpa [heq] using hscaled
  rcases Metric.tendsto_atTop.mp htend ε hε with ⟨N, hN⟩
  have hlen_lt : (b - a) / 2 ^ N < ε := by
    have hN0 : |b - a| / 2 ^ N < ε := by
      simpa [Real.dist_eq] using hN N (le_refl N)
    have hnonneg : 0 ≤ b - a := sub_nonneg.mpr hab
    simpa [abs_of_nonneg hnonneg] using hN0
  let l : ℕ → ℝ := fun n => (bisect_upper s a b n).1
  let r : ℕ → ℝ := fun n => (bisect_upper s a b n).2
  have hmono_l : Monotone l := by
    refine monotone_nat_of_le_succ ?_
    intro n
    simpa [l] using bisect_upper_left_mono_step s a b hab n
  have hanti_r : Antitone r := by
    refine antitone_nat_of_succ_le ?_
    intro n
    simpa [r] using bisect_upper_right_antitone_step s a b hab n
  have hle_lr : ∀ n, l n ≤ r n := by
    intro n
    simpa [l, r] using bisect_upper_le s a b hab n
  refine ⟨N, ?_⟩
  intro m hm n hn
  have hle_diam : |l m - l n| ≤ r N - l N := by
    rw [abs_le]
    constructor <;> nlinarith [hmono_l hm, le_trans (hle_lr m) (hanti_r hm),
      hmono_l hn, le_trans (hle_lr n) (hanti_r hn), hmono_l (le_refl N)]
  have hdiam : r N - l N = (b - a) / 2 ^ N := by
    simpa [l, r] using bisect_upper_length s a b N
  rw [Real.dist_eq]
  nlinarith

/-- 二分右端点序列 rₙ 是 Cauchy。
@isnad1 id=cauchyse.1h3v.s4.db6466e8124f from=translated src=- shape=b3420b51 vocab=34966689
-/
lemma bisect_upper_right_cauchy (s : Set ℝ) {a b : ℝ} (hab : a ≤ b) :
    CauchySeq (fun n => (bisect_upper s a b n).2) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have htend : Tendsto (fun n : ℕ => (b - a) / 2 ^ n) atTop (𝓝 0) := by
    have hpow : Tendsto (fun n : ℕ => ((1 / 2 : ℝ) ^ n)) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)
    have hscaled : Tendsto (fun n : ℕ => (b - a) * ((1 / 2 : ℝ) ^ n)) atTop (𝓝 0) := by
      simpa using hpow.const_mul (b - a)
    have heq : (fun n : ℕ => (b - a) / 2 ^ n) = (fun n : ℕ => (b - a) * ((1 / 2 : ℝ) ^ n)) := by
      funext n
      rw [one_div_pow]
      field_simp
    simpa [heq] using hscaled
  rcases Metric.tendsto_atTop.mp htend ε hε with ⟨N, hN⟩
  have hlen_lt : (b - a) / 2 ^ N < ε := by
    have hN0 : |b - a| / 2 ^ N < ε := by
      simpa [Real.dist_eq] using hN N (le_refl N)
    have hnonneg : 0 ≤ b - a := sub_nonneg.mpr hab
    simpa [abs_of_nonneg hnonneg] using hN0
  let l : ℕ → ℝ := fun n => (bisect_upper s a b n).1
  let r : ℕ → ℝ := fun n => (bisect_upper s a b n).2
  have hmono_l : Monotone l := by
    refine monotone_nat_of_le_succ ?_
    intro n
    simpa [l] using bisect_upper_left_mono_step s a b hab n
  have hanti_r : Antitone r := by
    refine antitone_nat_of_succ_le ?_
    intro n
    simpa [r] using bisect_upper_right_antitone_step s a b hab n
  have hle_lr : ∀ n, l n ≤ r n := by
    intro n
    simpa [l, r] using bisect_upper_le s a b hab n
  refine ⟨N, ?_⟩
  intro m hm n hn
  have hle_diam : |r m - r n| ≤ r N - l N := by
    rw [abs_le]
    constructor <;> nlinarith [hanti_r hm, hanti_r hn,
      le_trans (hmono_l hm) (hle_lr m), le_trans (hmono_l hn) (hle_lr n)]
  have hdiam : r N - l N = (b - a) / 2 ^ N := by
    simpa [l, r] using bisect_upper_length s a b N
  rw [Real.dist_eq]
  nlinarith

/-- c / 2ⁿ → 0（阿基米德原理的体现）。
@isnad1 id=tendsto.0h1v.s5.4b86c840d2fa from=translated src=- shape=5818500f vocab=aaf022dd
-/
lemma tendsto_div_two_pow {c : ℝ} : Tendsto (fun n : ℕ => c / 2 ^ n) atTop (𝓝 0) := by
  have hpow : Tendsto (fun n : ℕ => ((1 / 2 : ℝ) ^ n)) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)
  have hscaled : Tendsto (fun n : ℕ => c * ((1 / 2 : ℝ) ^ n)) atTop (𝓝 0) := by
    simpa using hpow.const_mul c
  have heq : (fun n : ℕ => c / 2 ^ n) = (fun n : ℕ => c * ((1 / 2 : ℝ) ^ n)) := by
    funext n
    rw [one_div_pow]
    field_simp
  simpa [heq] using hscaled

/--
> **Entry**: analysis.completeness.equivalence-cycle.cauchy-to-sup
> **一句话**: 环的第 6 道：从 Cauchy 收敛准则推出确界原理（二分逼近上确界）。
> **直觉**: 非空有上界的 s，取 x₀ ∈ s、上界 M；反复取中点二分 [x₀, M]，
>   保持"右端是上界、左端不是上界"；两端都是 Cauchy（区间直径 → 0），
>   Cauchy 给同一极限 x，x 正是 s 的上确界。
> **证明类别**: C（核心手工构造：二分进程 bisect_upper 全程 + Cauchy 收极限 + IsLUB 两件套）。
> **依赖**: 本文件 §3 `bisect_upper_*` 引理族
> **mathlib**: `ge_of_tendsto`, `tendsto_nhds_unique`, `tendsto_pow_atTop_nhds_zero_of_norm_lt_one`
@isnad1 id=supprope.1h0v.s1.9d6c835011d5 from=translated src=- shape=1d48f1ac vocab=3bd91f06
-/
theorem sup_of_cauchy_convergence (h : CauchyConvergenceProperty) : SupProperty := by
  intro s hs_nonempty hbdd
  rcases hs_nonempty with ⟨x₀, hx₀⟩
  rcases hbdd with ⟨M, hM⟩
  by_cases hx₀_upper : x₀ ∈ upperBounds s
  · refine ⟨x₀, ?_⟩
    refine ⟨hx₀_upper, ?_⟩
    intro y hy
    exact (mem_upperBounds.mp hy) x₀ hx₀
  · have hxM : x₀ ≤ M := (mem_upperBounds.mp hM) x₀ hx₀
    let l : ℕ → ℝ := fun n => (bisect_upper s x₀ M n).1
    let r : ℕ → ℝ := fun n => (bisect_upper s x₀ M n).2
    have hmono_l : Monotone l := by
      refine monotone_nat_of_le_succ ?_
      intro n
      simpa [l] using bisect_upper_left_mono_step s x₀ M hxM n
    have hl_cauchy : CauchySeq l := by
      simpa [l] using bisect_upper_left_cauchy s hxM
    have hr_cauchy : CauchySeq r := by
      simpa [r] using bisect_upper_right_cauchy s hxM
    rcases h l hl_cauchy with ⟨x, hx_tend⟩
    rcases h r hr_cauchy with ⟨y, hy_tend⟩
    have hlen_tend : Tendsto (fun n => r n - l n) atTop (𝓝 0) := by
      have heq : (fun n => r n - l n) = (fun n => (M - x₀) / 2 ^ n) := by
        funext n
        simpa [l, r] using bisect_upper_length s x₀ M n
      simpa [heq] using tendsto_div_two_pow (c := M - x₀)
    have hsub_tend : Tendsto (fun n => r n - l n) atTop (𝓝 (y - x)) :=
      Tendsto.sub hy_tend hx_tend
    have hyx : y = x := by
      have hxy : y - x = 0 := tendsto_nhds_unique hsub_tend hlen_tend
      linarith
    have hx_upper : ∀ z ∈ s, z ≤ x := by
      intro z hz
      have hr_upper : ∀ n, r n ∈ upperBounds s := by
        intro n
        simpa [r] using bisect_upper_right_upper s hM n
      have hz_le_r : ∀ n, z ≤ r n := by
        intro n
        exact (mem_upperBounds.mp (hr_upper n)) z hz
      have hz_le_y : z ≤ y := ge_of_tendsto hy_tend (Filter.Eventually.of_forall hz_le_r)
      simpa [hyx] using hz_le_y
    have hx_least : ∀ z ∈ upperBounds s, x ≤ z := by
      intro z hz
      by_contra hnot
      have hzx : z < x := lt_of_not_ge hnot
      have hpos : 0 < x - z := sub_pos.mpr hzx
      rcases Metric.tendsto_atTop.mp hx_tend (x - z) hpos with ⟨N, hN⟩
      have hlN_le_x : l N ≤ x := monotone_le_limit hmono_l hx_tend N
      have hlN_gt_z : z < l N := by
        have hdist : |l N - x| < x - z := by
          simpa [Real.dist_eq] using hN N (le_refl N)
        have habs : |l N - x| = x - l N := by
          rw [abs_of_nonpos (sub_nonpos.mpr hlN_le_x)]
          ring
        nlinarith
      have hlN_not_upper : l N ∉ upperBounds s := by
        simpa [l] using bisect_upper_left_not_upper s hx₀_upper N
      have hw_exists : ∃ w ∈ s, l N < w := by
        rw [mem_upperBounds] at hlN_not_upper
        push Not at hlN_not_upper
        simpa using hlN_not_upper
      rcases hw_exists with ⟨w, hws, hlw⟩
      have hz_not_upper : ¬ z ∈ upperBounds s := by
        rw [mem_upperBounds]
        push Not
        refine ⟨w, hws, ?_⟩
        exact lt_trans hlN_gt_z hlw
      exact hz_not_upper hz
    refine ⟨x, ?_⟩
    refine ⟨?_, ?_⟩
    · intro z hz
      exact hx_upper z hz
    · intro z hz
      exact hx_least z hz

end Analysis.Completeness

end SandronesLibrary
