/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku
import Tengoku.SandronesLibrary.SandronesLibrary.RealAnalysis.CoveringLemma

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# RealAnalysis / MaximalFunction —— Hardy–Littlewood 极大函数与弱型 (1,1) 估计（Folland RA-F3）

本文件当前条目（引理清单，§0 铁律 4：一次一条，逐条编译）：

* **real-analysis.maximal-function**（ℝ 上非中心 Hardy–Littlewood 极大函数的教材定义、
  基本性质、**对任意（不必可测的）`f` 的开集原像／下半连续性／Borel 可测性**、
  **弱型 `(1,1)` 估计**，以及通向 Lebesgue 微分定理的坏集控制骨架）✅。

> **教材定位**：Gerald B. Folland, *Real Analysis: Modern Techniques and Their Applications*,
> Second Edition, §3.4（Differentiation on Euclidean Space）。教材中
> `Hf(x) = sup_{Q ∋ x} (1/|Q|) ∫_Q |f|`（对含 `x` 的方体取上确界），
> Theorem 3.18 给出弱型 `(1,1)` 估计 `|{Hf > α}| ≤ (3ⁿ/α)‖f‖₁`。
> 本文件把同一量词域落到 ℝ 上的**开区间**，并复用已冻结的一维覆盖引理
> `SandronesLibrary.RealAnalysis.Covering`。

### 诚实边界（必读，自然语言不得越过这些线）

1. **一维**：本 Entry 交付的是 ℝ 上按开区间取上确界的非中心极大函数，**不是** ℝⁿ 上的极大函数；
   教材 ℝⁿ 版本要求本文件不具备的球／方体几何与 `3ⁿ` 覆盖常数。
2. **弱型常数是 4，不是 `3ⁿ`**：证明走 Mathlib Vitali 覆盖引理
   `Vitali.exists_disjoint_subfamily_covering_enlargement_ball` 的 `τ > 3` 口径，下游取 `τ = 4`。
   本库**不声称复刻** Folland 的常数 `3ⁿ`（`n = 1` 时 Folland 给 3，本库给 4）。
3. **弱型估计是测度不等式**：结论形状是 `volume {x | c < Mf x} ≤ 4 * c⁻¹ * ∫⁻ |f|`，
   **不是**逐点不等式，也**不是** a.e. 等式；自然语言不得写成逐点结论。
4. **积分类型**：右端是 `lintegral`（`ℝ≥0∞` 值）`∫⁻ y, ENNReal.ofReal |f y|`；
   测度是 Lebesgue `volume`（σ-有限、非负）；标量函数 `f : ℝ → ℝ` 且 `Integrable f volume`。
5. **本窗不交付 a.e. 微分定理**：Lebesgue 点与 Lebesgue 微分定理（RA-F4）、
   FTC 的 a.e. 版本（RA-F6）均**不在**本文件范围内。第 5 节只交付
   「坏集测度被 `O(‖f - g‖₁)` 控制」这一**证明骨架**，供 RA-F4 使用。
6. **`maximalFunction_mono` 的假设是 `|f| ≤ |g|` 逐点**，不是 `f ≤ g`：
   `f ≤ g` 对实值函数不蕴含 `|f| ≤ |g|`（如 `f = -5, g = 1`），故教材陈述需按绝对值改写；
   非负情形由 `maximalFunction_mono_of_nonneg` 覆盖。

### Mathlib 角色（本文件）

* `MeasureTheory.lintegral`（记号 `∫⁻`）、`ENNReal`：**语义一致的正式承载**（教材的
  `(1/|I|)∫_I |f|` 与 `ℝ≥0∞` 值上确界直接对应）。
* `Measurable`／`AEMeasurable`／`LowerSemicontinuous`：**语义一致的正式承载**
  （「`Hf` 下半连续故 Borel 可测」正是教材论证）。
* `measurable_of_Ioi`：由 `{c < f}` 的开性得 `Measurable f` 的**私有证明后端**。
* `lintegral_iUnion`、`lintegral_mono_set`、`ENNReal.tsum_mul_left`、`ENNReal.tsum_le_tsum`：
  弱型估计中把不交区间族的积分合并回全积分的**私有证明后端**。
* `Real.volume_Ioo`、`Measure.restrict_apply_univ`：区间测度与限制测度的**私有证明后端**。
* `Vitali.exists_disjoint_subfamily_covering_enlargement_ball`（经冻结覆盖引理间接使用）：
  **私有证明后端**（本库不重证覆盖组合核心）。
-/

namespace SandronesLibrary

namespace RealAnalysis.MaximalFunction

open MeasureTheory Set Metric
open SandronesLibrary.RealAnalysis.Covering
open scoped NNReal ENNReal Topology

/-! ## 1. 教材定义 -/

/-- **Hardy–Littlewood 非中心极大函数**（Folland §3.4 的一维形式）。

教材定义：`Hf(x) = sup_{I ∋ x} (1/|I|) ∫_I |f|`，其中上确界取遍所有含 `x` 的开区间 `I`。
本定义把它写成 `ℝ≥0∞` 值：

`maximalFunction f x = ⨆ (I : OpenInterval) (_ : x ∈ I.toSet),
  (volume I.toSet)⁻¹ * ∫⁻ y in I.toSet, ENNReal.ofReal |f y|`

值域取 `ℝ≥0∞`（允许 `∞`），因此**不需要** `f` 可积或可测；被积函数取 `ENNReal.ofReal |f y|`，
与教材的 `|f|` 一致。上确界的指标是「含 `x` 的开区间」，由冻结结构 `OpenInterval` 承载。
> **Entry**: real-analysis.maximal-function-/
noncomputable def maximalFunction (f : ℝ → ℝ) (x : ℝ) : ℝ≥0∞ :=
  ⨆ (I : OpenInterval) (_ : x ∈ I.toSet),
    (volume I.toSet)⁻¹ * ∫⁻ y in I.toSet, ENNReal.ofReal |f y|

/-! ## 2. 基本性质 -/

/-- **极大函数非负**：`0 ≤ Mf x`。由 `ℝ≥0∞` 的序结构直接得到。
> **Entry**: real-analysis.maximal-function-/
theorem maximalFunction_nonneg (f : ℝ → ℝ) (x : ℝ) : 0 ≤ maximalFunction f x :=
  zero_le

/-- **极大函数关于绝对值单调**：若逐点 `|f y| ≤ |g y|`，则 `Mf ≤ Mg`（逐点，故也整体）。

注意假设是**绝对值**的逐点控制而非 `f ≤ g`：实值函数的 `f ≤ g` 不蕴含 `|f| ≤ |g|`
（取 `f = -5`、`g = 1` 即反例）。非负情形见 `maximalFunction_mono_of_nonneg`。
> **Entry**: real-analysis.maximal-function-/
theorem maximalFunction_mono {f g : ℝ → ℝ} (h : ∀ y, |f y| ≤ |g y|) :
    maximalFunction f ≤ maximalFunction g := by
  intro x
  refine iSup_le fun I => iSup_le fun hx => ?_
  refine le_trans (mul_le_mul_right (lintegral_mono fun y => ENNReal.ofReal_le_ofReal (h y)) _) ?_
  exact le_iSup_of_le I (le_iSup_of_le hx le_rfl)

/-- **非负函数的极大函数单调**：`0 ≤ f` 且 `f ≤ g` 时 `Mf ≤ Mg`。
这是教材中「`f ≤ g` 蕴含 `Hf ≤ Hg`」在实值函数上的**正确**表述（需要非负性）。
> **Entry**: real-analysis.maximal-function-/
theorem maximalFunction_mono_of_nonneg {f g : ℝ → ℝ} (hf : 0 ≤ f) (h : f ≤ g) :
    maximalFunction f ≤ maximalFunction g :=
  maximalFunction_mono fun y => by
    rw [abs_of_nonneg (hf y)]
    exact le_trans (h y) (le_abs_self (g y))

private theorem volume_toSet_ne_zero (I : OpenInterval) : volume I.toSet ≠ 0 := by
  rw [OpenInterval.toSet, Real.volume_Ioo]
  exact ENNReal.ofReal_ne_zero_iff.2 (by linarith [I.lt])

private theorem volume_toSet_ne_top (I : OpenInterval) : volume I.toSet ≠ ∞ := by
  rw [OpenInterval.toSet, Real.volume_Ioo]
  exact ENNReal.ofReal_ne_top

/-- 常函数的区间平均等于该常数：`(1/|I|)∫_I a = a`（`a : ℝ≥0∞`）。
> **Entry**: real-analysis.maximal-function-/
private theorem inv_mul_lintegral_const (I : OpenInterval) (a : ℝ≥0∞) :
    (volume I.toSet)⁻¹ * ∫⁻ _y in I.toSet, a = a := by
  rw [lintegral_const, Measure.restrict_apply_univ, ← mul_assoc, ← ENNReal.div_eq_inv_mul,
    ENNReal.div_mul_cancel (volume_toSet_ne_zero I) (volume_toSet_ne_top I)]

/-- **常函数的极大函数**：`M (fun _ => a) x = ofReal |a|`（对每个 `x`）。

教材事实「常函数的平均就是它自己」在极大函数上的体现：每个含 `x` 的开区间给出同一个平均值
`ofReal |a|`，而含 `x` 的开区间非空（如 `(x-1, x+1)`），故上确界就是它。
> **Entry**: real-analysis.maximal-function-/
theorem maximalFunction_const (a x : ℝ) :
    maximalFunction (fun _ => a) x = ENNReal.ofReal |a| := by
  refine le_antisymm ?_ ?_
  · refine iSup_le fun I => iSup_le fun _ => ?_
    rw [inv_mul_lintegral_const]
  · refine le_iSup_of_le ⟨x - 1, x + 1, by linarith⟩ ?_
    refine le_iSup_of_le (show x ∈ (⟨x - 1, x + 1, by linarith⟩ : OpenInterval).toSet from
      ⟨by linarith, by linarith⟩) ?_
    rw [inv_mul_lintegral_const]

/-- **区间平均只依赖 a.e. 类**：`f =ᵐ[volume] g` 时，对每个开区间 `I` 有
`∫⁻ y in I.toSet, ofReal |f y| = ∫⁻ y in I.toSet, ofReal |g y|`。

这是「极大函数尊重 a.e. 相等」的桥：`f = g` a.e. 意味着对每个区间（有限测度集）限制后仍 a.e. 相等，
而 `lintegral` 不区分 a.e. 相等的被积函数。
> **Entry**: real-analysis.maximal-function-/
theorem lintegral_abs_congr_ae {f g : ℝ → ℝ} (h : f =ᵐ[volume] g) (I : OpenInterval) :
    ∫⁻ y in I.toSet, ENNReal.ofReal |f y| = ∫⁻ y in I.toSet, ENNReal.ofReal |g y| := by
  refine lintegral_congr_ae ?_
  filter_upwards [h.filter_mono (ae_mono (Measure.restrict_le_self (s := I.toSet)))] with y hy
  rw [hy]

/-- **a.e. 相等的函数给出逐点相等的极大函数**：`f =ᵐ[volume] g` 时 `Mf = Mg`（作为函数相等）。

比名称暗示的更强：因为每个开区间的平均都相等（`lintegral_abs_congr_ae`），
两个上确界在**每个** `x` 处相等，不只是 a.e.。a.e. 版本见 `maximalFunction_congr_ae`。
> **Entry**: real-analysis.maximal-function-/
theorem maximalFunction_congr_of_ae_eq {f g : ℝ → ℝ} (h : f =ᵐ[volume] g) :
    maximalFunction f = maximalFunction g := by
  funext x
  simp only [maximalFunction]
  refine iSup_congr fun I => iSup_congr fun _ => ?_
  rw [lintegral_abs_congr_ae h I]

/-- **极大函数尊重 a.e. 相等（a.e. 形式）**：`f =ᵐ[volume] g` 时
`Mf =ᵐ[volume] Mg`。由更强的逐点版本 `maximalFunction_congr_of_ae_eq` 立即得到。
> **Entry**: real-analysis.maximal-function-/
theorem maximalFunction_congr_ae {f g : ℝ → ℝ} (h : f =ᵐ[volume] g) :
    maximalFunction f =ᵐ[volume] maximalFunction g := by
  rw [maximalFunction_congr_of_ae_eq h]

/-! ## 3. 可测性边界（对任意 `f`，不需可测） -/

/-- **水平集 `{c < Mf}` 是开集**（对**任意** `f : ℝ → ℝ`，不需要 `f` 可测或可积）。

关键恒等式：

`{x | c < Mf x} = ⋃ (I : OpenInterval)
  (_ : c < (volume I.toSet)⁻¹ * ∫⁻ y in I.toSet, ofReal |f y|), I.toSet`

右边是开区间的并（任意并保持开性）。方向 `⊆` 用两次 `lt_iSup_iff` 取出见证区间与其平均值下界；
方向 `⊇` 用 `le_iSup_of_le` 把区间平均值放回上确界。这正是教材「`Hf` 下半连续」的证明。
> **Entry**: real-analysis.maximal-function-/
theorem isOpen_lt_maximalFunction (f : ℝ → ℝ) (c : ℝ≥0∞) :
    IsOpen {x : ℝ | c < maximalFunction f x} := by
  have hset : {x : ℝ | c < maximalFunction f x} =
      ⋃ (I : OpenInterval)
        (_ : c < (volume I.toSet)⁻¹ * ∫⁻ y in I.toSet, ENNReal.ofReal |f y|), I.toSet := by
    ext x
    constructor
    · intro hx
      simp only [maximalFunction, Set.mem_ofPred_eq] at hx
      obtain ⟨I, hI⟩ := lt_iSup_iff.1 hx
      obtain ⟨hxI, hlt⟩ := lt_iSup_iff.1 hI
      exact mem_iUnion.2 ⟨I, mem_iUnion.2 ⟨hlt, hxI⟩⟩
    · intro hx
      simp only [mem_iUnion] at hx
      obtain ⟨I, hlt, hxI⟩ := hx
      exact lt_of_lt_of_le hlt (le_iSup_of_le I (le_iSup_of_le hxI le_rfl))
  rw [hset]
  exact isOpen_iUnion fun I => isOpen_iUnion fun _ => OpenInterval.isOpen_toSet I

/-- **水平集 `{c < Mf}` 是 Borel 集**（对任意 `f`）。由开性直接得到。
> **Entry**: real-analysis.maximal-function-/
theorem measurableSet_lt_maximalFunction (f : ℝ → ℝ) (c : ℝ≥0∞) :
    MeasurableSet {x : ℝ | c < maximalFunction f x} :=
  (isOpen_lt_maximalFunction f c).measurableSet

/-- **极大函数下半连续**（对任意 `f`）：`LowerSemicontinuous (maximalFunction f)`。

Mathlib 的 `LowerSemicontinuous` 就是「每个 `Ioi c` 的原像是开集」，与
`isOpen_lt_maximalFunction` 逐字对应。
> **Entry**: real-analysis.maximal-function-/
theorem lowerSemicontinuous_maximalFunction (f : ℝ → ℝ) :
    LowerSemicontinuous (maximalFunction f) :=
  lowerSemicontinuous_iff_isOpen_preimage.2 fun c =>
    isOpen_lt_maximalFunction f c

/-- **极大函数 Borel 可测**（对任意 `f`）：`Measurable (maximalFunction f)`。

由 `measurable_of_Ioi`：`ℝ≥0∞` 是第二可数线性序拓扑，`{x | c < f x}` 对每个 `c` 可测
即可测。注意这里**没有**任何关于 `f` 的正则性假设。
> **Entry**: real-analysis.maximal-function-/
theorem measurable_maximalFunction (f : ℝ → ℝ) : Measurable (maximalFunction f) :=
  measurable_of_Ioi (f := maximalFunction f) fun c => measurableSet_lt_maximalFunction f c

/-- **极大函数 a.e. 可测**（对任意 `f`）：`AEMeasurable (maximalFunction f) volume`。
由 `Measurable.aemeasurable` 得到。
> **Entry**: real-analysis.maximal-function-/
theorem aemeasurable_maximalFunction (f : ℝ → ℝ) :
    AEMeasurable (maximalFunction f) volume :=
  (measurable_maximalFunction f).aemeasurable

/-! ## 4. 弱型 `(1,1)` 估计 -/

/-- **弱型估计的单区间步骤（测度形式）**：若 `c < (1/|I|)∫_I |f|`，则
`|I| ≤ c⁻¹ ∫_I |f|`。

证明：把 `c < (volume I)⁻¹ * ∫_I` 经 `ENNReal.lt_div_iff_mul_lt` 化为
`c * |I| < ∫_I`，两边左乘 `c⁻¹`（`c ≠ 0, c ≠ ∞`）并用 `c⁻¹ * c = 1` 化简。
> **Entry**: real-analysis.maximal-function-/
theorem volume_le_inv_mul_lintegral_of_lt_average {f : ℝ → ℝ} {c : ℝ≥0} (hc : 0 < c)
    {I : OpenInterval}
    (havg : (c : ℝ≥0∞) < (volume I.toSet)⁻¹ * ∫⁻ y in I.toSet, ENNReal.ofReal |f y|) :
    volume I.toSet ≤ (c : ℝ≥0∞)⁻¹ * ∫⁻ y in I.toSet, ENNReal.ofReal |f y| := by
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by
    simpa only [ne_eq, ENNReal.coe_eq_zero] using ne_of_gt hc
  have hct : (c : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top
  have hmain : (c : ℝ≥0∞) * volume I.toSet < ∫⁻ y in I.toSet, ENNReal.ofReal |f y| := by
    rw [← ENNReal.div_eq_inv_mul] at havg
    exact (ENNReal.lt_div_iff_mul_lt (Or.inl (volume_toSet_ne_zero I))
      (Or.inl (volume_toSet_ne_top I))).1 havg
  have h : (c : ℝ≥0∞)⁻¹ * ((c : ℝ≥0∞) * volume I.toSet) <
      (c : ℝ≥0∞)⁻¹ * ∫⁻ y in I.toSet, ENNReal.ofReal |f y| :=
    ENNReal.mul_lt_mul_right (ENNReal.inv_ne_zero.2 hct) (ENNReal.inv_ne_top.2 hc0) hmain
  calc
    volume I.toSet = (c : ℝ≥0∞)⁻¹ * ((c : ℝ≥0∞) * volume I.toSet) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]
    _ ≤ (c : ℝ≥0∞)⁻¹ * ∫⁻ y in I.toSet, ENNReal.ofReal |f y| := le_of_lt h

/-- **弱型估计的半径一致有界步骤**：`f` 可积、`c > 0`、`c < (1/|I|)∫_I |f|` 时

`I.radius ≤ (∫⁻ y, ofReal |f y|).toReal / (2 * c)`。

这是把坏集塞进覆盖引理的**关键一步**：先由单区间不等式得 `c * |I| < ∫_I |f| ≤ ∫_ℝ |f| < ∞`，
取 `toReal` 并用 `|I| = u - l = 2 * radius` 与 `volume I = ofReal (u - l)` 换算，
最后除以 `2c`。可积性只用来保证 `∫⁻ y, ofReal |f y| ≠ ∞`。
> **Entry**: real-analysis.maximal-function-/
theorem radius_le_of_lt_average {f : ℝ → ℝ} (hf : Integrable f volume) {c : ℝ≥0} (hc : 0 < c)
    {I : OpenInterval}
    (havg : (c : ℝ≥0∞) < (volume I.toSet)⁻¹ * ∫⁻ y in I.toSet, ENNReal.ofReal |f y|) :
    I.radius ≤ (∫⁻ y, ENNReal.ofReal |f y|).toReal / (2 * (c : ℝ)) := by
  have htop : ∫⁻ y, ENNReal.ofReal |f y| ≠ ∞ := ne_of_lt (by simpa using hf.abs.lintegral_lt_top)
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by
    simpa only [ne_eq, ENNReal.coe_eq_zero] using ne_of_gt hc
  have hct : (c : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top
  have hmain : (c : ℝ≥0∞) * volume I.toSet < ∫⁻ y in I.toSet, ENNReal.ofReal |f y| := by
    rw [← ENNReal.div_eq_inv_mul] at havg
    exact (ENNReal.lt_div_iff_mul_lt (Or.inl (volume_toSet_ne_zero I))
      (Or.inl (volume_toSet_ne_top I))).1 havg
  have hle : ∫⁻ y in I.toSet, ENNReal.ofReal |f y| ≤ ∫⁻ y, ENNReal.ofReal |f y| := by
    simpa using lintegral_mono_set (subset_univ I.toSet)
  have hlt : (c : ℝ≥0∞) * volume I.toSet < ∫⁻ y, ENNReal.ofReal |f y| :=
    lt_of_lt_of_le hmain hle
  have hltR : (c : ℝ) * (I.u - I.l) < (∫⁻ y, ENNReal.ofReal |f y|).toReal := by
    have h1 := (ENNReal.toReal_lt_toReal (ENNReal.mul_ne_top hct (volume_toSet_ne_top I))
      htop).2 hlt
    have h2 : ((c : ℝ≥0∞) * volume I.toSet).toReal = (c : ℝ) * (I.u - I.l) := by
      rw [ENNReal.toReal_mul, ENNReal.coe_toReal, OpenInterval.toSet, Real.volume_Ioo,
        ENNReal.toReal_ofReal (by linarith [I.lt])]
    rwa [h2] at h1
  have hcpos : (0 : ℝ) < c := by exact_mod_cast hc
  have h2c : (0 : ℝ) < 2 * c := by linarith
  have hdiv : (c * (I.u - I.l)) / (2 * c) <
      (∫⁻ y, ENNReal.ofReal |f y|).toReal / (2 * c) :=
    div_lt_div_of_pos_right hltR h2c
  have heq : (c * (I.u - I.l)) / (2 * c) = (I.u - I.l) / 2 := by
    rw [div_eq_div_iff (ne_of_gt h2c) (by norm_num : (2 : ℝ) ≠ 0)]
    ring
  calc
    I.radius = (I.u - I.l) / 2 := rfl
    _ = (c * (I.u - I.l)) / (2 * c) := heq.symm
    _ ≤ (∫⁻ y, ENNReal.ofReal |f y|).toReal / (2 * (c : ℝ)) := le_of_lt hdiv

/-- **Hardy–Littlewood 弱型 `(1,1)` 估计（本 Entry 核心，一维、常数 4）**。

设 `f : ℝ → ℝ` 可积（`Integrable f volume`），`c : ℝ≥0` 且 `0 < c`，则坏集
`E = {x | (c : ℝ≥0∞) < maximalFunction f x}` 满足**测度不等式**

`volume E ≤ 4 * (c : ℝ≥0∞)⁻¹ * ∫⁻ y, ENNReal.ofReal |f y|`。

证明骨架（教材 §3.4 的覆盖论证，一维区间版）：

1. 对 `x ∈ E`，用两次 `lt_iSup_iff` 取出见证区间 `I x ∋ x` 使 `c < (1/|I x|)∫_{I x} |f|`；
   用 `Classical.choose`（经 `if h : x ∈ E`）把它补成全函数 `sel : ℝ → OpenInterval`；
2. `radius_le_of_lt_average` 给出半径一致界 `R = (∫⁻ |f|).toReal / (2c)`；
3. 冻结的覆盖引理 `exists_disjoint_interval_subfamily_covering_enlargement`（取 `τ = 4`）
   抽出不交子族 `u ⊆ E`，使每个 `sel x` 落在某个 `sel b`（`b ∈ u`）的 4-放大球内；
4. `volume_iUnion_le_mul_tsum` 把 `volume E` 压到 `ofReal 4 * ∑' b : u, volume (sel b)`；
5. `volume_le_inv_mul_lintegral_of_lt_average` 逐项换积分，再用 `lintegral_iUnion`
   （`u` 至多可数、区间两两不交）合并回 `∫⁻ y, ofReal |f y|`，最后用 `lintegral_mono_set`
   控制到全积分。

**常数 4 的来源**：Mathlib 的 Vitali 放大覆盖只保证 `τ > 3`，本库取 `τ = 4`。
Folland 在 ℝⁿ 上用球／方体陈述、常数 `3ⁿ`（`n = 1` 时为 3）；**本库不声称复刻该常数**。
> **Entry**: real-analysis.maximal-function-/
theorem maximalFunction_weak_type (f : ℝ → ℝ) (hf : Integrable f volume)
    (c : ℝ≥0) (hc : 0 < c) :
    volume {x : ℝ | (c : ℝ≥0∞) < maximalFunction f x} ≤
      4 * (c : ℝ≥0∞)⁻¹ * ∫⁻ y, ENNReal.ofReal |f y| := by
  classical
  set E : Set ℝ := {x : ℝ | (c : ℝ≥0∞) < maximalFunction f x} with hE
  have hEexists : ∀ x ∈ E, ∃ I : OpenInterval, x ∈ I.toSet ∧
      (c : ℝ≥0∞) < (volume I.toSet)⁻¹ * ∫⁻ y in I.toSet, ENNReal.ofReal |f y| := by
    intro x hx
    rw [hE] at hx
    simp only [Set.mem_ofPred_eq, maximalFunction] at hx
    obtain ⟨I, hI⟩ := lt_iSup_iff.1 hx
    obtain ⟨hxI, hlt⟩ := lt_iSup_iff.1 hI
    exact ⟨I, hxI, hlt⟩
  let sel : ℝ → OpenInterval := fun x =>
    if h : x ∈ E then (hEexists x h).choose else ⟨0, 1, by norm_num⟩
  have hsel_mem : ∀ x ∈ E, x ∈ (sel x).toSet := by
    intro x hx
    dsimp only [sel]
    rw [dite_eq_left hx]
    exact (hEexists x hx).choose_spec.1
  have hsel_lt : ∀ x ∈ E, (c : ℝ≥0∞) <
      (volume (sel x).toSet)⁻¹ * ∫⁻ y in (sel x).toSet, ENNReal.ofReal |f y| := by
    intro x hx
    dsimp only [sel]
    rw [dite_eq_left hx]
    exact (hEexists x hx).choose_spec.2
  obtain ⟨u, huE, hdisj, hcov⟩ :=
    exists_disjoint_interval_subfamily_covering_enlargement E sel
      ((∫⁻ y, ENNReal.ofReal |f y|).toReal / (2 * (c : ℝ)))
      (fun x hx => radius_le_of_lt_average hf hc (hsel_lt x hx)) (τ := 4) (by norm_num)
  have hcount : Countable u := (hdisj.countable_of_nonempty_interior fun i _ => by
    rw [(OpenInterval.isOpen_toSet (sel i)).interior_eq]
    exact ⟨(sel i).center, OpenInterval.center_mem_toSet (sel i)⟩).to_subtype
  have hterm : ∀ b : u, volume ((sel b).toSet) ≤
      (c : ℝ≥0∞)⁻¹ * ∫⁻ y in (sel b).toSet, ENNReal.ofReal |f y| :=
    fun b => volume_le_inv_mul_lintegral_of_lt_average hc (hsel_lt b.1 (huE b.2))
  have hleall : ∫⁻ y in ⋃ b : u, (sel b).toSet, ENNReal.ofReal |f y| ≤
      ∫⁻ y, ENNReal.ofReal |f y| := by
    have hsub : (⋃ b : u, (sel b).toSet) ⊆ Set.univ := subset_univ _
    simpa using lintegral_mono_set hsub
  have hdisj' : Pairwise (Function.onFun Disjoint fun b : u => (sel b).toSet) := by
    intro a b hab
    exact hdisj a.2 b.2 fun h => hab (Subtype.ext h)
  have htsum : ∑' b : u, volume ((sel b).toSet) ≤
      (c : ℝ≥0∞)⁻¹ * ∫⁻ y, ENNReal.ofReal |f y| := by
    calc
      ∑' b : u, volume ((sel b).toSet)
          ≤ ∑' b : u, (c : ℝ≥0∞)⁻¹ * ∫⁻ y in (sel b).toSet, ENNReal.ofReal |f y| :=
            ENNReal.tsum_le_tsum hterm
      _ = (c : ℝ≥0∞)⁻¹ * ∑' b : u, ∫⁻ y in (sel b).toSet, ENNReal.ofReal |f y| :=
            ENNReal.tsum_mul_left
      _ = (c : ℝ≥0∞)⁻¹ * ∫⁻ y in ⋃ b : u, (sel b).toSet, ENNReal.ofReal |f y| := by
            congr 1
            exact (lintegral_iUnion (s := fun b : u => (sel b).toSet)
              (fun b => OpenInterval.measurableSet_toSet (sel b)) hdisj'
              (fun y => ENNReal.ofReal |f y|)).symm
      _ ≤ (c : ℝ≥0∞)⁻¹ * ∫⁻ y, ENNReal.ofReal |f y| :=
            mul_le_mul_right hleall _
  have hcover : volume E ≤ ENNReal.ofReal 4 * ∑' b : u, volume ((sel b).toSet) := by
    refine le_trans (measure_mono ?_)
      (volume_iUnion_le_mul_tsum E sel u huE hdisj hcov (by norm_num))
    intro x hx
    exact mem_iUnion₂.2 ⟨x, hx, hsel_mem x hx⟩
  calc
    volume E ≤ ENNReal.ofReal 4 * ∑' b : u, volume ((sel b).toSet) := hcover
    _ ≤ ENNReal.ofReal 4 * ((c : ℝ≥0∞)⁻¹ * ∫⁻ y, ENNReal.ofReal |f y|) :=
          mul_le_mul_right htsum _
    _ = 4 * (c : ℝ≥0∞)⁻¹ * ∫⁻ y, ENNReal.ofReal |f y| := by
          rw [show ENNReal.ofReal 4 = (4 : ℝ≥0∞) by norm_num, mul_assoc]

/-! ## 5. 坏集控制骨架（RA-F4 的前置，本窗只交付骨架） -/

/-- **差函数的弱型估计（坏集控制骨架）**：若 `f - g` 可积，则对 `c > 0`

`volume {x | (c : ℝ≥0∞) < M (f - g) x} ≤ 4 * c⁻¹ * ∫⁻ y, ofReal |f y - g y|`。

它在 Lebesgue 微分定理（Folland Theorem 3.21）证明里的角色是**坏集控制**：
先用连续函数（或简单函数）类证明 a.e. 收敛，再用本估计把坏集
`{M(f - g) > ε}` 的测度压到 `O(‖f - g‖₁)`，最后用连续／简单函数在 `L¹` 中的稠密性取极限。
本估计只是该骨架中的测度控制一环，**本身不是** a.e. 收敛结论。

**诚实边界**：Lebesgue 点与 Lebesgue 微分定理本身（RA-F4）**不在**本 Entry 范围内，
本窗只交付上述坏集控制；Folland Theorem 3.21 的 a.e. 结论既未陈述也未证明。
> **Entry**: real-analysis.maximal-function-/
theorem maximalFunction_weak_type_sub {f g : ℝ → ℝ}
    (h : Integrable (fun y => f y - g y) volume) (c : ℝ≥0) (hc : 0 < c) :
    volume {x : ℝ | (c : ℝ≥0∞) < maximalFunction (fun y => f y - g y) x} ≤
      4 * (c : ℝ≥0∞)⁻¹ * ∫⁻ y, ENNReal.ofReal |f y - g y| :=
  maximalFunction_weak_type (fun y => f y - g y) h c hc

end RealAnalysis.MaximalFunction

end SandronesLibrary
