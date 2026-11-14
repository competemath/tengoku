/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# RealAnalysis / AbsoluteContinuityFunction —— 绝对连续函数（Folland RA-F5 §3.6）

本文件当前条目（引理清单）：

* **real-analysis.absolute-continuity-function**（绝对连续函数：教材 ε-δ 定义的 Lean 承载与量词
  展开、`Lipschitz ⟹ AC ⟹ BV ⟹ a.e. 可导` 这条链、AC ⟹ 一致连续、代数封闭性，以及
  “变上限积分是 AC”这一 RA-F6 入口桥）✅。

> **语言说明**：Folland §3.6 定义：`f` 在 `[a,b]` 上**绝对连续**，若
> `∀ ε > 0, ∃ δ > 0`，使得对 `[a,b]` 中任意有限个两两不交的开区间 `(aₖ, bₖ)`，只要
> `∑ (bₖ - aₖ) < δ` 就有 `∑ |f(bₖ) - f(aₖ)| < ε`。Mathlib 的
> `AbsolutelyContinuousOnInterval f a b` 把这族区间编码成 `ℕ × (ℕ → ℝ × ℝ)` 的元素，
> 并把“总长度趋于 0”写成滤子 `AbsolutelyContinuousOnInterval.totalLengthFilter` 上的
> `Tendsto`；`absolutelyContinuousOnInterval_iff` 证明它与教材 ε-δ 量词等价。两者语义一致，
> 故本库直接复用该谓词作为**正式公开承载**，不另造同构 `def`。

> **对象层级**：`AbsolutelyContinuousOnInterval` 是**区间上**的谓词
> （`f : ℝ → X`，`a b : ℝ`，区间 `uIcc a b`），**不是**全局谓词；`a > b` 时 `uIcc a b = uIcc b a`，
> 故它对端点顺序对称（见 `.symm`）。

### Mathlib 角色（本文件）

* `AbsolutelyContinuousOnInterval`：**正式公开承载**（课程定义直接采用）。
* `absolutelyContinuousOnInterval_iff`：**教材量词展开**（filter 定义 ↔ ε-δ 定义）。
* `LipschitzOnWith.absolutelyContinuousOnInterval`、`ContDiffOn.absolutelyContinuousOnInterval`：
  “更强正则性 ⟹ AC”的**私有证明后端**。
* `AbsolutelyContinuousOnInterval.boundedVariationOn`、`...ae_differentiableAt`：
  AC ⟹ BV ⟹ a.e. 可导的**私有证明后端**（本文件提升为教材命题）。
* `IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral`：**桥**——
  “变上限积分是 AC”是 RA-F6（FTC 的 a.e. 版本）的入口方向，**本窗只交付 AC 这一侧**。

### 诚实边界（本条目）

* a.e. 结论一律写成 `∀ᵐ x, …`，**不是**逐点结论。
* 不含 AC ⟹ 导数可积、也不含 `∫ f' = f(b) - f(a)`（Newton–Leibniz 的 a.e. 版本，RA-F6）。
-/

namespace SandronesLibrary

namespace RealAnalysis.AbsoluteContinuityFunction

open Set Filter MeasureTheory
open scoped NNReal ENNReal Topology MeasureTheory Interval

variable {X : Type*} [PseudoMetricSpace X]
variable {F : Type*} [SeminormedAddCommGroup F]

/-! ## 1. 定义层与教材量词展开 -/

/-- **Lean 侧定义展开**：`AbsolutelyContinuousOnInterval f a b` 就是“区间族上的函数
`E ↦ ∑ᵢ dist (f (aᵢ)) (f (bᵢ))` 沿长度滤子 `totalLengthFilter`（限制到不交区间族
`disjWithin a b`）趋于 `0`”。这是 Mathlib 的定义体本身，故为 `Iff.rfl`；它把教材的
“总长度 → 0 时振幅和 → 0”写成 `Tendsto`。
> **Entry**: real-analysis.absolute-continuity-function-/
theorem absolutelyContinuousOnInterval_iff_tendsto (f : ℝ → X) (a b : ℝ) :
    AbsolutelyContinuousOnInterval f a b ↔
      Tendsto (fun E : ℕ × (ℕ → ℝ × ℝ) =>
          ∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2))
        (AbsolutelyContinuousOnInterval.totalLengthFilter (X := ℝ) ⊓
          𝓟 (AbsolutelyContinuousOnInterval.disjWithin a b)) (𝓝 0) :=
  Iff.rfl

/-- **教材 ε-δ 展开（Folland §3.6 定义）**：`f` 在 `uIcc a b` 上绝对连续，当且仅当
`∀ ε > 0, ∃ δ > 0`，使得对任意有限个两两不交、端点都落在 `uIcc a b` 中的区间
`(aᵢ, bᵢ)`（`i < n`），只要 `∑ᵢ dist aᵢ bᵢ < δ` 就有 `∑ᵢ dist (f aᵢ) (f bᵢ) < ε`。
这是教材量词与 Lean 承载之间的等价刻画（Mathlib 已证）。
> **Entry**: real-analysis.absolute-continuity-function-/
theorem absolutelyContinuousOnInterval_iff_epsilon_delta (f : ℝ → X) (a b : ℝ) :
    AbsolutelyContinuousOnInterval f a b ↔
      ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ E,
        E ∈ AbsolutelyContinuousOnInterval.disjWithin a b →
        ∑ i ∈ Finset.range E.1, dist (E.2 i).1 (E.2 i).2 < δ →
        ∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2) < ε :=
  absolutelyContinuousOnInterval_iff f a b

/-- **有限不交区间族的对象层级**：`E ∈ disjWithin a b` 展开为“`E.1 = n` 个区间
`(E.2 i).1, (E.2 i).2`（`i < n`）端点都在 `uIcc a b` 中，且对应的 `uIoc` 两两不交”。
这条把教材“有限个两两不交的区间”精确对应到 Lean 的 `ℕ × (ℕ → ℝ × ℝ)` 编码。
> **Entry**: real-analysis.absolute-continuity-function-/
theorem mem_disjWithin_iff {a b : ℝ} {E : ℕ × (ℕ → ℝ × ℝ)} :
    E ∈ AbsolutelyContinuousOnInterval.disjWithin a b ↔
      (∀ i ∈ Finset.range E.1, (E.2 i).1 ∈ uIcc a b ∧ (E.2 i).2 ∈ uIcc a b) ∧
        Set.PairwiseDisjoint (Finset.range E.1) (fun i => uIoc (E.2 i).1 (E.2 i).2) :=
  Iff.rfl

/-! ## 2. 与 Lipschitz 连续的关系 -/

/-- **Lipschitz ⟹ 绝对连续（教材定理）**：若 `f` 在 `uIcc a b` 上以常数 `K` Lipschitz 连续，
则 `f` 在 `uIcc a b` 上绝对连续。教材证明取 `δ = ε / (K + 1)`：不交区间族的总长度乘以 `K`
控制振幅和。反向不成立（AC 不必 Lipschitz）。
> **Entry**: real-analysis.absolute-continuity-function-/
theorem lipschitzOnWith_absolutelyContinuousOnInterval {f : ℝ → X} {a b : ℝ} {K : ℝ≥0}
    (h : LipschitzOnWith K f (uIcc a b)) : AbsolutelyContinuousOnInterval f a b :=
  h.absolutelyContinuousOnInterval

/-- **`C¹` ⟹ 绝对连续（教材推论）**：`f` 在 `uIcc a b` 上连续可微（`ContDiffOn ℝ 1`），
则 `f` 绝对连续。这是“更强正则性 ⟹ AC”的又一条入口；它同时说明 AC 类严格大于 `C¹` 类：
AC 只保证**几乎处处**可导，不保证处处可导，例如 `x ↦ max x 0` 在 `[-1,1]` 上是区间可积函数
`1_{[0,∞)}` 的变上限积分，因而绝对连续，但在 `x = 0` 处不可导。
> **Entry**: real-analysis.absolute-continuity-function-/
theorem contDiffOn_one_absolutelyContinuousOnInterval {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ → E} {a b : ℝ} (h : ContDiffOn ℝ 1 f (uIcc a b)) :
    AbsolutelyContinuousOnInterval f a b :=
  h.absolutelyContinuousOnInterval

/-! ## 3. 与有界变差、a.e. 导数的关系：`Lipschitz ⟹ AC ⟹ BV ⟹ a.e. 可导` -/

/-- **绝对连续 ⟹ 有界变差（教材定理）**：若 `f` 在 `uIcc a b` 上绝对连续，则 `f` 在 `uIcc a b` 上
有界变差。教材证明把 `[a,b]` 切成若干长度 `< δ` 的小区间（`δ` 取 AC 定义中对 `ε = 1` 的那一个），
每段变差 `< 1`，故总变差有限。
> **Entry**: real-analysis.absolute-continuity-function-/
theorem absolutelyContinuousOnInterval_boundedVariationOn {f : ℝ → F} {a b : ℝ}
    (h : AbsolutelyContinuousOnInterval f a b) : BoundedVariationOn f (uIcc a b) :=
  h.boundedVariationOn

/-- **绝对连续 ⟹ 几乎处处可导（教材定理）**：若 `f : ℝ → ℝ` 在 `uIcc a b` 上绝对连续，则 `f` 在
`uIcc a b` 上**几乎处处**（关于 `volume`）可导：`∀ᵐ x, x ∈ uIcc a b → DifferentiableAt ℝ f x`。
证明走 AC ⟹ BV（`absolutelyContinuousOnInterval_boundedVariationOn`）再套
`BoundedVariationOn.ae_differentiableAt_of_mem_uIcc`。
> **诚实边界**：这是 a.e. 结论，**不是**逐点结论——零测例外集可以非空。也不含
> `∫ f' = f(b) - f(a)`（RA-F6）。
> **Entry**: real-analysis.absolute-continuity-function-/
theorem absolutelyContinuousOnInterval_ae_differentiableAt {f : ℝ → ℝ} {a b : ℝ}
    (h : AbsolutelyContinuousOnInterval f a b) :
    ∀ᵐ x : ℝ, x ∈ uIcc a b → DifferentiableAt ℝ f x :=
  h.ae_differentiableAt

/-! ## 4. 连续性强度：AC ⟹ 一致连续 ⟹ 连续 -/

/-- **AC ⟹ 一致连续（教材定理）**：绝对连续比一致连续更强。教材中 AC 定义里的 ε-δ 对**所有**
有限不交区间族一致成立，取单区间族即得一致连续性。
> **Entry**: real-analysis.absolute-continuity-function-/
theorem absolutelyContinuousOnInterval_uniformContinuousOn {f : ℝ → F} {a b : ℝ}
    (h : AbsolutelyContinuousOnInterval f a b) : UniformContinuousOn f (uIcc a b) :=
  h.uniformContinuousOn

/-- **AC ⟹ 连续**：由一致连续推出（`uIcc a b` 上的一致连续函数连续）。
> **Entry**: real-analysis.absolute-continuity-function-/
theorem absolutelyContinuousOnInterval_continuousOn {f : ℝ → F} {a b : ℝ}
    (h : AbsolutelyContinuousOnInterval f a b) : ContinuousOn f (uIcc a b) :=
  h.continuousOn

/-- **AC ⟹ 有界**：`uIcc a b` 紧，连续函数在其上有界。
> **Entry**: real-analysis.absolute-continuity-function-/
theorem absolutelyContinuousOnInterval_exists_bound {f : ℝ → F} {a b : ℝ}
    (h : AbsolutelyContinuousOnInterval f a b) :
    ∃ C : ℝ, ∀ x ∈ uIcc a b, ‖f x‖ ≤ C :=
  h.exists_bound

/-! ## 5. 代数封闭性 -/

/-- **AC 对加法封闭**。
> **Entry**: real-analysis.absolute-continuity-function-/
theorem absolutelyContinuousOnInterval_add {f g : ℝ → F} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hg : AbsolutelyContinuousOnInterval g a b) :
    AbsolutelyContinuousOnInterval (f + g) a b :=
  hf.add hg

/-- **AC 对减法封闭**。
> **Entry**: real-analysis.absolute-continuity-function-/
theorem absolutelyContinuousOnInterval_sub {f g : ℝ → F} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hg : AbsolutelyContinuousOnInterval g a b) :
    AbsolutelyContinuousOnInterval (f - g) a b :=
  hf.sub hg

/-- **AC 对取负封闭**。
> **Entry**: real-analysis.absolute-continuity-function-/
theorem absolutelyContinuousOnInterval_neg {f : ℝ → F} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) : AbsolutelyContinuousOnInterval (-f) a b :=
  hf.neg

/-- **AC 对实数数乘封闭**（实值情形）。
> **Entry**: real-analysis.absolute-continuity-function-/
theorem absolutelyContinuousOnInterval_const_mul {f : ℝ → ℝ} {a b : ℝ} (c : ℝ)
    (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun x => c * f x) a b :=
  hf.const_mul c

/-- **AC 对标量乘法封闭**（`M` 为半范数环、`F` 为 `M`-模，且范数与标量乘法相容）。
> **Entry**: real-analysis.absolute-continuity-function-/
theorem absolutelyContinuousOnInterval_const_smul {M : Type*} [SeminormedRing M] [Module M F]
    [NormSMulClass M F] (c : M) {f : ℝ → F} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun x => c • f x) a b :=
  hf.const_smul c

/-- **AC 对乘积封闭**（实值情形）：两个绝对连续实值函数的乘积绝对连续。证明用“AC ⟹ 有界”
把乘积的振幅和拆成 `C · ∑ dist g + D · ∑ dist f`。
> **Entry**: real-analysis.absolute-continuity-function-/
theorem absolutelyContinuousOnInterval_mul {f g : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hg : AbsolutelyContinuousOnInterval g a b) :
    AbsolutelyContinuousOnInterval (f * g) a b :=
  hf.mul hg

/-- **AC 对逐点标量积封闭**（`M` 值函数与 `F` 值函数）。
> **Entry**: real-analysis.absolute-continuity-function-/
theorem absolutelyContinuousOnInterval_smul {M : Type*} [SeminormedRing M] [Module M F]
    [NormSMulClass M F] {f : ℝ → M} {g : ℝ → F} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hg : AbsolutelyContinuousOnInterval g a b) :
    AbsolutelyContinuousOnInterval (f • g) a b :=
  hf.smul hg

/-- **端点顺序对称**：`AC` 在 `uIcc a b` 上等价于在 `uIcc b a` 上（`uIcc` 对端点对称）。
> **Entry**: real-analysis.absolute-continuity-function-/
theorem absolutelyContinuousOnInterval_symm {f : ℝ → X} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) : AbsolutelyContinuousOnInterval f b a :=
  hf.symm

/-- **单调性（限制到子区间）**：`AC` 在较大区间上成立则在子区间上成立。
> **Entry**: real-analysis.absolute-continuity-function-/
theorem absolutelyContinuousOnInterval_mono {f : ℝ → X} {a b c d : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (habcd : uIcc c d ⊆ uIcc a b) :
    AbsolutelyContinuousOnInterval f c d :=
  hf.mono habcd

/-- **AC 与 Lipschitz 函数的复合**：若 `g` 在 `uIcc a b` 上以 `K` Lipschitz 连续，且 `f` 把
`uIcc a b` 映入 `uIcc a b`，则 `g ∘ f` 在 `uIcc a b` 上绝对连续。
**Mathlib 没有这条引理**，本库按教材思路自证：取 AC 定义中对 `ε / (K + 1)` 的 `δ`，逐项用
`dist (g x) (g y) ≤ K · dist x y` 控制，再做算术
`K · (ε/(K+1)) < (K+1) · (ε/(K+1)) = ε`。
> **Entry**: real-analysis.absolute-continuity-function-/
theorem lipschitzOnWith_comp_absolutelyContinuousOnInterval {f g : ℝ → ℝ} {a b : ℝ} {K : ℝ≥0}
    (hf : AbsolutelyContinuousOnInterval f a b) (hg : LipschitzOnWith K g (uIcc a b))
    (hmaps : MapsTo f (uIcc a b) (uIcc a b)) :
    AbsolutelyContinuousOnInterval (g ∘ f) a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := hf (ε / (K + 1)) (by positivity)
  refine ⟨δ, hδ, fun E hE hlen => ?_⟩
  calc ∑ i ∈ Finset.range E.1, dist (g (f (E.2 i).1)) (g (f (E.2 i).2))
      ≤ ∑ i ∈ Finset.range E.1, (K : ℝ) * dist (f (E.2 i).1) (f (E.2 i).2) := by
        refine Finset.sum_le_sum fun i hi => ?_
        exact hg.dist_le_mul (f (E.2 i).1) (hmaps (hE.1 i hi).1) (f (E.2 i).2)
          (hmaps (hE.1 i hi).2)
    _ = (K : ℝ) * ∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2) := by
        rw [Finset.mul_sum]
    _ ≤ (K : ℝ) * (ε / (K + 1)) := by
        gcongr
        exact (h E hE hlen).le
    _ < ((K : ℝ) + 1) * (ε / (K + 1)) := by
        gcongr
        linarith
    _ = ε := by
        field_simp

/-! ## 6. 桥：变上限积分是绝对连续（RA-F6 入口方向，本窗不交付 FTC） -/

/-- **变上限积分是 AC（RA-F6 入口桥）**：若 `f` 在 `a..b` 上区间可积，`c ∈ uIcc a b`，则
`x ↦ ∫ v in c..x, f v` 在 `uIcc a b` 上绝对连续。
> **诚实边界**：这里只交付 **AC 这一侧**。反方向——AC ⟹ 导数可积且
> `∫ x in a..b, deriv f x = f b - f a`（FTC 的 a.e. 版本，即 Newton–Leibniz 表示）——
> 属于 **RA-F6，本窗不交付**；它依赖 RA-F4 的 Lebesgue 微分定理。
> **Entry**: real-analysis.absolute-continuity-function-/
theorem intervalIntegrable_absolutelyContinuousOnInterval_intervalIntegral {f : ℝ → ℝ} {a b c : ℝ}
    (h : IntervalIntegrable f volume a b) (hc : c ∈ uIcc a b) :
    AbsolutelyContinuousOnInterval (fun x => ∫ v in c..x, f v) a b :=
  h.absolutelyContinuousOnInterval_intervalIntegral hc

end RealAnalysis.AbsoluteContinuityFunction

end SandronesLibrary
