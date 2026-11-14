/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open Filter Topology

/-!
# Analysis / Sequence —— 数列极限基础条目

本文件当前条目：

* **analysis.sequence.definition**（收敛的定义/ε-N 判据）：本库谓词
  `SequenceConvergesTo u l` 定义为：对每个 ε>0 存在 N，使得从第 N 项起
  |u n − l| < ε；并证明它等价于 `Tendsto u atTop (𝓝 l)`。
* **analysis.sequence.unique**（极限唯一）：同一个序列若有极限则极限唯一。
* **analysis.sequence.bounded**（收敛必有界）：收敛序列的值域既有上界也有下界。
* **analysis.sequence.squeeze**（夹逼定理）：两边夹住且同趋于 l，中间也趋于 l。
* **analysis.sequence.monotone-convergence**（单调有界收敛）：单调递增且值域有上界
  的序列收敛，且极限恰为其值域的上确界。
* **analysis.sequence.subsequence**（子序列）：收敛序列的任何子列收敛到同一极限。
* **analysis.sequence.bolzano-weierstrass**（波尔查诺-魏尔斯特拉斯）：有界实数列必有收敛子列。
* **analysis.sequence.cauchy**（Cauchy 收敛准则/完备性）：本库以双指标 ε-N 条件定义
  `SequenceIsCauchy`，桥接 Mathlib 的 `CauchySeq`，并证明实数列收敛 ⟺ 是 Cauchy 列。
* **analysis.sequence.liminf-limsup**（上/下极限）：liminf ≤ limsup，且相等 ⟺ 收敛。
* **analysis.sequence.add/sub/mul/div/const-mul**（极限四则运算）。
* **analysis.sequence.le**（极限保序）。
-/

namespace SandronesLibrary

namespace Analysis.Sequence

/-- 实数列 `u` 收敛到 `l` 的教材 ε-N 定义。
> **Entry**: analysis.sequence.definition-/
def SequenceConvergesTo (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |u n - l| < ε

/-- 实数列收敛，即存在某个实数极限。-/
def SequenceConvergent (u : ℕ → ℝ) : Prop :=
  ∃ l : ℝ, SequenceConvergesTo u l

/-- 展开本库数列收敛定义。
@isnad1 id=iff.0h2v.s5.8cf82cee5687 from=translated src=- shape=d80ab503 vocab=e5926296
-/
theorem sequenceConvergesTo_iff_epsilon_N {u : ℕ → ℝ} {l : ℝ} :
    SequenceConvergesTo u l ↔ ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |u n - l| < ε :=
  Iff.rfl

/--
> **Entry**: analysis.sequence.definition
> **一句话**: 数列收敛的 ε-N 判据——"最终会靠近极限"用"每个 ε 都最终满足"来刻画。
> **直觉**: "aₙ → l" 意思是：无论你要多近（ε），"从某一项往后全都落进 l 的 ε-邻域"。
>   它把"无限过程的最终结果"翻译成"有限次逼近的承诺"，是分析的基石。
> **依赖**: 无
> **mathlib**: `Metric.tendsto_atTop`, `Tendsto`, `𝓝`, `atTop`
@isnad1 id=iff.0h2v.s6.a6ad8b0bc0d6 from=translated src=- shape=9c402d1d vocab=ea0dcc61
-/
theorem tendsto_iff_epsilon_N {u : ℕ → ℝ} {l : ℝ} :
    Tendsto u atTop (𝓝 l) ↔ ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |u n - l| < ε := by
  -- 思路：度量空间里"趋于 l"就是"距离趋于 0"；距离在实轴上就是绝对值。
  simpa [Real.dist_eq] using Metric.tendsto_atTop (u := u) (a := l)

/-- 本库 ε-N 数列收敛定义与 Mathlib 滤子收敛接口完全等价。
@isnad1 id=iff.0h2v.s4.c6dc6c68d6f4 from=translated src=- shape=d03c0e57 vocab=ffbff8d0
-/
theorem sequenceConvergesTo_iff_tendsto {u : ℕ → ℝ} {l : ℝ} :
    SequenceConvergesTo u l ↔ Tendsto u atTop (𝓝 l) := by
  simpa [SequenceConvergesTo] using (tendsto_iff_epsilon_N (u := u) (l := l)).symm

/-- 本库“收敛列”定义与存在 Mathlib 滤子极限等价。
@isnad1 id=iff.0h1v.s4.dd414c0b20c3 from=translated src=- shape=ff921403 vocab=acf6903a
-/
theorem sequenceConvergent_iff_exists_tendsto {u : ℕ → ℝ} :
    SequenceConvergent u ↔ ∃ l : ℝ, Tendsto u atTop (𝓝 l) := by
  simp only [SequenceConvergent, sequenceConvergesTo_iff_tendsto]

/-- 实数列 `u` 是 Cauchy 列的教材双指标 ε-N 定义。
> **Entry**: analysis.sequence.cauchy-/
def SequenceIsCauchy (u : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, |u m - u n| < ε

/-- 展开本库 Cauchy 列定义。
@isnad1 id=iff.0h1v.s5.86e1c14f8d08 from=translated src=- shape=ec60a18b vocab=ee83513b
-/
theorem sequenceIsCauchy_iff_epsilon_N {u : ℕ → ℝ} :
    SequenceIsCauchy u ↔
      ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, |u m - u n| < ε :=
  Iff.rfl

/-- 本库双指标 ε-N 定义与 Mathlib 的 `CauchySeq` 完全等价。
@isnad1 id=iff.0h1v.s3.49ae8967983e from=translated src=- shape=10444140 vocab=6b8db010
-/
theorem sequenceIsCauchy_iff_cauchySeq {u : ℕ → ℝ} :
    SequenceIsCauchy u ↔ CauchySeq u := by
  simpa [SequenceIsCauchy, Real.dist_eq] using (Metric.cauchySeq_iff (u := u)).symm

/-- 教材接口下的极限唯一性。
> **Entry**: analysis.sequence.definition
@isnad1 id=eq.2h3v.s4.411606d4406c from=translated src=- shape=29728a40 vocab=0e2fbd3f
-/
theorem sequenceConvergesTo_unique {u : ℕ → ℝ} {a b : ℝ}
    (ha : SequenceConvergesTo u a) (hb : SequenceConvergesTo u b) : a = b := by
  exact tendsto_nhds_unique (sequenceConvergesTo_iff_tendsto.mp ha)
    (sequenceConvergesTo_iff_tendsto.mp hb)

/-- 教材接口下，收敛列必为 Cauchy 列。
> **Entry**: analysis.sequence.cauchy
@isnad1 id=sequence.1h2v.s3.aadaf4722945 from=translated src=- shape=aad63e9e vocab=40221d5c
-/
theorem sequenceConvergesTo_sequenceIsCauchy {u : ℕ → ℝ} {l : ℝ}
    (h : SequenceConvergesTo u l) : SequenceIsCauchy u := by
  exact sequenceIsCauchy_iff_cauchySeq.mpr
    (Filter.Tendsto.cauchy_map (sequenceConvergesTo_iff_tendsto.mp h))

/--
> **Entry**: analysis.sequence.unique
> **一句话**: 数列若有极限，极限唯一。
> **直觉**: 序列不可能同时"最终被 a 逮住"又"最终被 b(≠a) 逮住"——
>   取 ε 小于二者距离的一半，从足够大的 n 起会既是 a 的邻点又是 b 的邻点，矛盾。
> **依赖**: 无
> **mathlib**: `tendsto_nhds_unique`, `Tendsto`
@isnad1 id=eq.2h3v.s5.bef0f28285eb from=translated src=- shape=a5f22a41 vocab=aca016fa
-/
theorem seq_limit_unique {u : ℕ → ℝ} {a b : ℝ}
    (ha : Tendsto u atTop (𝓝 a)) (hb : Tendsto u atTop (𝓝 b)) : a = b := by
  -- 思路：极限唯一是 Hausdorff 空间的基本事实（通用引理直接可用）。
  exact tendsto_nhds_unique (f := u) ha hb

/-- 收敛序列的值域有上界（辅助：ε=1 的尾部界 + 前缀自动被滤掉）。
  `IsBoundedUnder` 是"最终在某界之下"的滤子语言，`bddAbove_range` 把它
  翻译回值域的有界性。
@isnad1 id=bddabove.1h2v.s4.bf5d607fb35d from=translated src=- shape=1d15647a vocab=bf53da7a
-/
theorem convergent_bddAbove {u : ℕ → ℝ} {l : ℝ} (h : Tendsto u atTop (𝓝 l)) :
    BddAbove (Set.range u) := by
  have hε : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |u n - l| < ε := by
    simpa [Real.dist_eq] using Metric.tendsto_atTop.mp h
  rcases hε 1 zero_lt_one with ⟨N, hN⟩
  have hev : ∀ᶠ n in atTop, u n ≤ l + 1 := by
    rw [eventually_atTop]
    refine ⟨N, ?_⟩
    intro n hn
    have hpos : u n - l < 1 := (abs_lt.mp (hN n hn)).2
    linarith
  exact (isBoundedUnder_of_eventually_le (f := atTop) (u := u) (a := l + 1) hev).bddAbove_range

/-- 收敛序列的值域有下界（镜像：ε=1 得尾部在 l−1 之上）。
@isnad1 id=bddbelow.1h2v.s4.fc895ab30331 from=translated src=- shape=1d15647a vocab=b1f4cc16
-/
theorem convergent_bddBelow {u : ℕ → ℝ} {l : ℝ} (h : Tendsto u atTop (𝓝 l)) :
    BddBelow (Set.range u) := by
  have hε : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |u n - l| < ε := by
    simpa [Real.dist_eq] using Metric.tendsto_atTop.mp h
  rcases hε 1 zero_lt_one with ⟨N, hN⟩
  have hev : ∀ᶠ n in atTop, l - 1 ≤ u n := by
    rw [eventually_atTop]
    refine ⟨N, ?_⟩
    intro n hn
    have hneg : -(1) < u n - l := (abs_lt.mp (hN n hn)).1
    linarith
  exact (isBoundedUnder_of_eventually_ge (f := atTop) (u := u) (a := l - 1) hev).bddBelow_range

/--
> **Entry**: analysis.sequence.bounded
> **一句话**: 收敛的数列必有界（值域既有上界又有下界）。
> **直觉**: 从第 N 项起全落在 (l−1, l+1) 里；前面只有有限多项，自然会"展不开"。
>   反过来不成立（有界不一定收敛，如 (−1)ⁿ）。这是"收敛→有界"的单向道。
> **依赖**: 无
> **mathlib**: `IsBoundedUnder`, `Metric.tendsto_atTop`, `BddAbove/BddBelow`
@isnad1 id=and.1h2v.s5.8167ee9a2b2e from=translated src=- shape=69e5a697 vocab=bb54b637
-/
theorem convergent_bounded {u : ℕ → ℝ} {l : ℝ} (h : Tendsto u atTop (𝓝 l)) :
    BddAbove (Set.range u) ∧ BddBelow (Set.range u) := by
  exact ⟨convergent_bddAbove h, convergent_bddBelow h⟩

/-- 教材“收敛列”接口下，数列值域有上下界。
@isnad1 id=and.1h1v.s4.7376fb1d070c from=translated src=- shape=6b1562d7 vocab=0b472f5b
-/
theorem sequenceConvergent_bounded {u : ℕ → ℝ} (h : SequenceConvergent u) :
    BddAbove (Set.range u) ∧ BddBelow (Set.range u) := by
  rcases h with ⟨l, hl⟩
  exact convergent_bounded (sequenceConvergesTo_iff_tendsto.mp hl)

/--
> **Entry**: analysis.sequence.squeeze
> **一句话**: 夹逼定理：aₙ ≤ bₙ ≤ cₙ 且 aₙ、cₙ 同趋于 l，则 bₙ 也趋于 l。
> **直觉**: 被两边挤住的东西无处可去。"挤住"=逐点不等式，"无处可去"
>   =两边都趋向同一处。
> **依赖**: `analysis.sequence.definition`（ε-N 判据的理解）
> **mathlib**: `tendsto_of_tendsto_of_tendsto_of_le_of_le`
@isnad1 id=tendsto.4h4v.s6.4cfa46677837 from=translated src=- shape=64eb9e40 vocab=abc36b8f
-/
theorem squeeze_theorem {a b c : ℕ → ℝ} {l : ℝ}
    (hle₁ : ∀ n, a n ≤ b n) (hle₂ : ∀ n, b n ≤ c n)
    (ha : Tendsto a atTop (𝓝 l)) (hc : Tendsto c atTop (𝓝 l)) :
    Tendsto b atTop (𝓝 l) := by
  -- 思路：把两个逐点不等式升成函数间的 ≤（Pi 阶即逐点），再套通用夹逼引理。
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le ha hc hle₁ hle₂

/--
> **Entry**: analysis.sequence.monotone-convergence
> **一句话**: 单调有界收敛定理：单调递增且值域有上界的序列必收敛，
>   且极限就是值域的上确界。
> **直觉**: 一路不回头地往上走，又被天花板挡着——那它只能越走越贴近天花板本身。
>   （本题的"天花板"=sSup。ℚ 里没有这个性质，完备性在这里第一回发威。）
> **依赖**: `analysis.real.sup`
> **mathlib**: `tendsto_atTop_ciSup`, `Real.isLUB_sSup`
@isnad1 id=and.2h1v.s5.34ab13ec9e9f from=translated src=- shape=7cf49016 vocab=11eb522a
-/
theorem monotone_convergence {u : ℕ → ℝ} (hu : Monotone u)
    (hb : BddAbove (Set.range u)) :
    Tendsto u atTop (𝓝 (sSup (Set.range u))) ∧ IsLUB (Set.range u) (sSup (Set.range u)) := by
  -- 思路：单调递增+有界 → sup 存在（确界原理），且单调序列收敛到 sup。
  constructor
  · rw [← (Real.isLUB_sSup (Set.range_nonempty u) hb).ciSup_eq]
    exact tendsto_atTop_ciSup hu hb
  · exact Real.isLUB_sSup (Set.range_nonempty u) hb

/--
> **Entry**: analysis.sequence.subsequence
> **一句话**: 子序列定义与主干定理——收敛序列的任何子列都收敛到同一极限。
> **直觉**: "子列" = 跳着取但绝不回头的取法（下标函数 φ 严格递增）。
>   主干已经收敛，局部主义跳着取值自然只更"追得上"。
> **依赖**: 无
> **mathlib**: `StrictMono.tendsto_atTop`, `Filter.Tendsto.comp`

子序列判定：v 是 u 的子列 ⟺ 存在严格递增的取法 φ，使 v = u ∘ φ。-/
def IsSubsequenceOf (u : ℕ → ℝ) (v : ℕ → ℝ) : Prop :=
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ v = u ∘ φ

/-- 收敛序列的任何子列收敛到同一极限（φ 严格递增 ⇒ φ→atTop，复合得证）。
@isnad1 id=tendsto.2h3v.s5.9cbdc4c7c06b from=translated src=- shape=090dfcd4 vocab=b60396db
-/
theorem subsequence_of_convergent {u : ℕ → ℝ} {l : ℝ}
    (hu : Tendsto u atTop (𝓝 l)) {v : ℕ → ℝ} (hsub : IsSubsequenceOf u v) :
    Tendsto v atTop (𝓝 l) := by
  rcases hsub with ⟨φ, hφ, rfl⟩
  exact hu.comp (StrictMono.tendsto_atTop hφ)

/-- 辅助：有上界又有下界的序列，整体落入某个对称闭区间 [−M, M]。
@isnad1 id=ex.2h1v.s5.4e4e87290240 from=translated src=- shape=185a662b vocab=8c463d7e
-/
lemma sequence_bounded_in_interval {u : ℕ → ℝ}
    (hb : BddAbove (Set.range u)) (hbdl : BddBelow (Set.range u)) :
    ∃ a b : ℝ, ∀ n : ℕ, u n ∈ Set.Icc a b := by
  rcases hb with ⟨b₀, hb₀⟩
  rcases hbdl with ⟨a₀, ha₀⟩
  let M : ℝ := max |a₀| |b₀|
  refine ⟨-M, M, ?_⟩
  intro n
  constructor
  · dsimp [M]
    calc
      -max |a₀| |b₀| ≤ -|a₀| := neg_le_neg (le_max_left |a₀| |b₀|)
      _ ≤ a₀ := neg_abs_le a₀
      _ ≤ u n := ha₀ ⟨n, rfl⟩
  · dsimp [M]
    calc
      u n ≤ b₀ := hb₀ ⟨n, rfl⟩
      _ ≤ |b₀| := le_abs_self b₀
      _ ≤ max |a₀| |b₀| := le_max_right |a₀| |b₀|

/--
> **Entry**: analysis.sequence.bolzano-weierstrass
> **一句话**: 波尔查诺-魏尔斯特拉斯定理：有界实数列必有收敛的子列。
> **直觉**: 有界 ⟹ 全值藏在一个闭区间里；闭区间紧，紧集中的序列必含收敛子列
>   （子列极限也在区间里）。
> **依赖**: `analysis.sequence.bounded`, `analysis.sequence.subsequence`
> **mathlib**: `CompactIccSpace.isCompact_Icc`, `IsCompact.isSeqCompact`

闭区间版本：值全在 [a, b] 的序列有收敛子列，且极限仍在 [a, b] 内。
@isnad1 id=ex.1h3v.s6.61e056d5f699 from=translated src=- shape=d65adba6 vocab=4b5edf2a
-/
theorem bolzano_weierstrass_interval {u : ℕ → ℝ} {a b : ℝ}
    (h : ∀ n : ℕ, u n ∈ Set.Icc a b) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ l : ℝ, l ∈ Set.Icc a b ∧ Tendsto (u ∘ φ) atTop (𝓝 l) := by
  have hIcc : IsCompact (Set.Icc a b) := CompactIccSpace.isCompact_Icc
  rcases hIcc.isSeqCompact h with ⟨l, hl, φ, hφ, hlim⟩
  exact ⟨φ, hφ, l, hl, hlim⟩

/-- 有界版本：把有界翻译进闭区间，再套闭区间版本。
@isnad1 id=ex.2h1v.s5.fb7f6f743faa from=translated src=- shape=3e449c19 vocab=ee51ace2
-/
theorem bolzano_weierstrass {u : ℕ → ℝ}
    (hb : BddAbove (Set.range u)) (hbdl : BddBelow (Set.range u)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ l : ℝ, Tendsto (u ∘ φ) atTop (𝓝 l) := by
  rcases sequence_bounded_in_interval hb hbdl with ⟨a, b, h⟩
  rcases bolzano_weierstrass_interval h with ⟨φ, hφ, l, _, hl⟩
  exact ⟨φ, hφ, l, hl⟩

/--
> **Entry**: analysis.sequence.cauchy
> **一句话**: Cauchy 收敛准则（完备性）：实数列收敛 ⟺ 是 Cauchy 列。
> **直觉**: 收敛 = 大家往同一处跑；Cauchy = 大家相互之间靠拢。
>   "相互不靠拢"则没有公共去处；"虽是 Cauchy 却不收敛"在 ℚ；ℝ 里必有其处。
> **依赖**: `analysis.sequence.subsequence`（语言准备）、`analysis.sequence.bounded`
> **mathlib**: `CauchySeq`, `Metric.cauchySeq_iff`, `cauchySeq_tendsto_of_complete`

收敛 ⟹ Cauchy：极限把两端距离从任意远处居中拉回（双 ε/2 三角不等式）。
@isnad1 id=cauchyse.1h2v.s4.c011a24e7aa3 from=translated src=- shape=eb72ebd5 vocab=d0733695
-/
theorem convergent_is_cauchy {u : ℕ → ℝ} {l : ℝ} (h : Tendsto u atTop (𝓝 l)) : CauchySeq u := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hε2 : 0 < ε / 2 := div_pos hε (by norm_num)
  rcases Metric.tendsto_atTop.mp h (ε / 2) hε2 with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro m hm n hn
  rw [Real.dist_eq]
  have htri : |u m - u n| ≤ |u m - l| + |u n - l| := by
    calc
      |u m - u n| = |(u m - l) + (l - u n)| := by
        rw [show (u m - l) + (l - u n) = u m - u n by ring]
      _ ≤ |u m - l| + |l - u n| := abs_add_le _ _
      _ = |u m - l| + |u n - l| := by rw [abs_sub_comm l (u n)]
  linarith [htri,
    (show |u m - l| < ε / 2 by simpa [Real.dist_eq] using hN m hm),
    (show |u n - l| < ε / 2 by simpa [Real.dist_eq] using hN n hn)]

/-- Cauchy ⟹ 收敛：实数完备性（ℝ 的 CompleteSpace 实例直接给出极限）。
@isnad1 id=ex.1h1v.s5.7f4ff57651c9 from=translated src=- shape=37c6944e vocab=d0733695
-/
theorem cauchy_seq_convergent {u : ℕ → ℝ} (h : CauchySeq u) : ∃ l : ℝ, Tendsto u atTop (𝓝 l) := by
  exact cauchySeq_tendsto_of_complete h

/--
> **Entry**: analysis.sequence.liminf-limsup
> **一句话**: 上/下极限：有界序列有 liminf ≤ limsup，且两极限相等 ⟺ 收敛到该值。
> **直觉**: limsup = "任何后续都跳不过的最矮天花板"，liminf = "任何后续都跌不破的最高地板"；
>   天花板从不低于地板（liminf ≤ limsup），两者挤成一起便是收敛。
> **依赖**: `analysis.sequence.bounded`（一致性口径：两向有界）
> **mathlib**: `Filter.liminf_le_limsup`, `tendsto_of_liminf_eq_limsup`

有界序列的下极限不超过上极限。
@isnad1 id=le.2h1v.s5.f692e917d116 from=translated src=- shape=e709a07a vocab=97012e6b
-/
theorem liminf_le_limsup_seq {u : ℕ → ℝ}
    (hU : IsBoundedUnder (· ≤ ·) atTop u) (hL : IsBoundedUnder (· ≥ ·) atTop u) :
    liminf u atTop ≤ limsup u atTop := by
  exact Filter.liminf_le_limsup (f := atTop) (u := u) hU hL

/-- liminf 与 limsup 相等（都 = a）⟹ 序列收敛到 a（两向有界时）。
@isnad1 id=tendsto.4h2v.s6.0765b405bdbc from=translated src=- shape=b6449f95 vocab=6db530c7
-/
theorem tendsto_of_liminf_eq_limsup_seq {u : ℕ → ℝ} {a : ℝ}
    (hU : IsBoundedUnder (· ≤ ·) atTop u) (hL : IsBoundedUnder (· ≥ ·) atTop u)
    (hinf : liminf u atTop = a) (hsup : limsup u atTop = a) :
    Tendsto u atTop (𝓝 a) := by
  exact tendsto_of_liminf_eq_limsup (f := atTop) (u := u) (a := a) hinf hsup hU hL

/-- **序列极限之和**：lim(aₙ + bₙ) = lim aₙ + lim bₙ。 
> **Entry**: analysis.sequence.add
@isnad1 id=tendsto.2h4v.s6.70ba80788c4c from=translated src=- shape=65b2a7a1 vocab=1f87b35e
-/
theorem seq_add {a b : ℕ → ℝ} {x y : ℝ}
    (ha : Tendsto a atTop (𝓝 x)) (hb : Tendsto b atTop (𝓝 y)) :
    Tendsto (fun n => a n + b n) atTop (𝓝 (x + y)) :=
  ha.add hb

/-- **序列极限之差**：lim(aₙ − bₙ) = lim aₙ − lim bₙ。 
> **Entry**: analysis.sequence.sub
@isnad1 id=tendsto.2h4v.s6.6b05b11f182b from=translated src=- shape=65b2a7a1 vocab=b5442cbc
-/
theorem seq_sub {a b : ℕ → ℝ} {x y : ℝ}
    (ha : Tendsto a atTop (𝓝 x)) (hb : Tendsto b atTop (𝓝 y)) :
    Tendsto (fun n => a n - b n) atTop (𝓝 (x - y)) :=
  ha.sub hb

/-- **序列极限之积**：lim(aₙ·bₙ) = lim aₙ·lim bₙ。 
> **Entry**: analysis.sequence.mul
@isnad1 id=tendsto.2h4v.s6.be6e87c4a85b from=translated src=- shape=65b2a7a1 vocab=298574cd
-/
theorem seq_mul {a b : ℕ → ℝ} {x y : ℝ}
    (ha : Tendsto a atTop (𝓝 x)) (hb : Tendsto b atTop (𝓝 y)) :
    Tendsto (fun n => a n * b n) atTop (𝓝 (x * y)) :=
  ha.mul hb

/-- **序列极限之商**：lim(aₙ/bₙ) = lim aₙ/lim bₙ（分母极限非零）。 
> **Entry**: analysis.sequence.div
@isnad1 id=tendsto.3h4v.s6.2cbed00194ca from=translated src=- shape=1d33586a vocab=aebbfd6d
-/
theorem seq_div {a b : ℕ → ℝ} {x y : ℝ} (hy : y ≠ 0)
    (ha : Tendsto a atTop (𝓝 x)) (hb : Tendsto b atTop (𝓝 y)) :
    Tendsto (fun n => a n / b n) atTop (𝓝 (x / y)) :=
  ha.div hb hy

/-- **序列极限的常数数乘**：lim(c·aₙ) = c·lim aₙ。 
> **Entry**: analysis.sequence.const-mul
@isnad1 id=tendsto.1h3v.s5.3dbfd837e5c8 from=translated src=- shape=2c210e92 vocab=298574cd
-/
theorem seq_const_mul {a : ℕ → ℝ} {x : ℝ} (c : ℝ)
    (ha : Tendsto a atTop (𝓝 x)) :
    Tendsto (fun n => c * a n) atTop (𝓝 (c * x)) :=
  ha.const_mul c

/-- **序列极限保序**：若 aₙ ≤ bₙ 恒成立且 aₙ→x、bₙ→y，则 x ≤ y。 
> **Entry**: analysis.sequence.le
@isnad1 id=le.3h4v.s5.ea4920241004 from=translated src=- shape=9dd415c1 vocab=abc36b8f
-/
theorem seq_le {a b : ℕ → ℝ} {x y : ℝ}
    (ha : Tendsto a atTop (𝓝 x)) (hb : Tendsto b atTop (𝓝 y))
    (hab : ∀ n, a n ≤ b n) : x ≤ y := by
  have hsub : Tendsto (fun n => b n - a n) atTop (𝓝 (y - x)) := hb.sub ha
  have hnonneg : ∀ᶠ n in atTop, (0 : ℝ) ≤ b n - a n :=
    Filter.Eventually.of_forall (fun n => by linarith [hab n])
  have h0 : 0 ≤ y - x := ge_of_tendsto hsub hnonneg
  linarith

end Analysis.Sequence

end SandronesLibrary
