/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# RealAnalysis / MonotoneFunction —— 单调函数（Folland RA-F5，§3.5 单调函数部分）

本文件当前条目（引理清单）：

* **real-analysis.monotone-function**（单调函数 `Monotone f`（`f : ℝ → ℝ`）的教材量词展开、
  间断结构（左右极限与跳跃点至多可数）、Lebesgue-a.e. 可导性、以及通往 Lebesgue–Stieltjes
  测度 `StieltjesFunction.measure` 的桥；末尾给出与同批有界变差条目的公开接口）✅。

> **语言说明**：实分析阶段（ROADMAP §6 Phase 5）以 Folland *Real Analysis* 第二版 §3.5
> （Functions of Bounded Variation and Lebesgue–Stieltjes Measures，单调函数部分）为教材。
> Mathlib 的 `Monotone` 与教材定义「`x ≤ y ⟹ f x ≤ f y`」逐字一致，故本库直接复用
> `Monotone` 作为**正式公开承载**，不另造同构 `def`；本文件只补教材量词展开、间断结构的
> 夹逼刻画、跳跃点可数性、a.e. 可导性的显式测度陈述，以及 Stieltjes 测度桥。

> **命名说明**：本文件的公开声明一律放在库自己的命名空间
> `SandronesLibrary.RealAnalysis.MonotoneFunction` 下（本库既有约定，见
> `RealAnalysis.MeasureDerivative.*`），不向 Mathlib 的 `Monotone` 命名空间注入新名字，
> 以免与 Mathlib 后续版本撞名。每条声明的 docstring 给出对应的 Mathlib 名字与角色。

### Mathlib 角色（本文件）

* `Monotone`（`f : ℝ → ℝ` 上的谓词）、`MonotoneOn`：**正式公开承载**（课程定义直接采用）。
* `Monotone.leftLim_le` / `Monotone.le_rightLim` / `Monotone.leftLim_le_rightLim` /
  `Monotone.le_leftLim` / `Monotone.rightLim_le`：左右极限的**序关系后端**（语义与教材一致），
  本文件在其上给出教材化的夹逼（`leftLim_le_self`、`self_le_rightLim`）。
* `Monotone.continuousAt_iff_leftLim_eq_rightLim`：**连续性判据后端**（教材「左右极限相等」），
  本文件把它展开成含函数值的教材形式 `continuousAt_iff_leftLim_eq_self_and_rightLim_eq_self`。
* `Monotone.countable_not_continuousAt`：**间断点至多可数的正式承载**（第二可数值域上的
  Mathlib 一般形式）；本文件给出 `ℝ → ℝ` 的教材特化与跳跃点形式。
* `Monotone.ae_hasDerivAt` / `Monotone.ae_differentiableAt`：**a.e. 可导性的正式承载**；
  本文件给出把 a.e. 滤子的测度写成显式 `volume` 的教材陈述。
* `Monotone.stieltjesFunction`、`StieltjesFunction`、`StieltjesFunction.measure`、
  `StieltjesFunction.measure_Ioc/Icc/Ioo/Ico/singleton`、
  `StieltjesFunction.instIsLocallyFiniteMeasure`：**Lebesgue–Stieltjes 测度的正式承载**；
  本文件把它们接到单调函数 `f` 本身（用 `f` 的左右极限表出区间测度）。
* `MonotoneOn.eVariationOn_eq`、`BoundedVariationOn`、`eVariationOn`：有界变差侧的
  **正式承载与后端**；本文件只补 `ℝ` 上 `Icc` 的教材接口。

### 诚实边界

1. **所有 a.e. 结论都是 `∀ᵐ x ∂volume` 形式的几乎处处命题，不是逐点命题**；本文件
   `ae_hasDerivAt_volume` / `ae_differentiableAt_volume` 的陈述中测度写成显式 `volume`。
2. 跳跃点（间断点）「至多可数」在 Mathlib 中是**第二可数值域空间**上的结论
   （`Monotone.countable_not_continuousAt`）；本文件 `countable_not_continuousAt_real` 只是
   `ℝ → ℝ` 的教材特化，`countable_jumpPoints` 是同一定理的跳跃点形式。
3. `Monotone.stieltjesFunction` 是 `f` 的**右连续化** `x ↦ f(x⁺) = Function.rightLim f x`，
   因此 `StieltjesFunction.measure` 的区间公式用 `f` 的右极限／左极限表出；只有 `f` 本身
   右连续时才退化为教材字面的 `f b - f a`（`stieltjesFunction_measure_Ioc_of_rightContinuous`）。
4. 本 Entry **不含** FTC 的 a.e. 版本（RA-F6），**不含** Lebesgue 微分定理与 Lebesgue 点
   （RA-F4）；`ae_hasDerivAt_volume` 是这两条路线的下游接口，本身不证明微分定理。
5. 类型边界：`volume`（`ℝ` 上的 Lebesgue 测度）、`StieltjesFunction.measure`
   （`ℝ` 上局部有限的 Borel 测度）、`Measure.rnDeriv`（取值 `ℝ≥0∞` 的 Radon–Nikodym 导数，
   本文件取其 `ENNReal.toReal`）。区间测度取值为 `ℝ≥0∞`（`ENNReal.ofReal`）。
6. 与同批 `real-analysis.bounded-variation` 的分工：`SandronesLibrary.RealAnalysis.BoundedVariation`
   已给出 `uIcc` 形式（`monotoneOn_boundedVariationOn_uIcc`）；本文件的 `Icc` 形式是教材
   `a ≤ b` 区间下的陈述，供上层直接消费，不重复其 `uIcc` 一般化。
-/

namespace SandronesLibrary

namespace RealAnalysis.MonotoneFunction

open MeasureTheory Set Filter
open scoped ENNReal MeasureTheory

/-! ## 1. 正式承载与教材量词展开 -/

/-- **单调函数（Folland §3.5 教材量词）**：`f : ℝ → ℝ` 单调，当且仅当
`∀ x y, x ≤ y → f x ≤ f y`。Mathlib 的 `Monotone` 定义体即为该量词，故为 `Iff.rfl`；
本定理只把教材量词显式写出，供上层以展开形式使用。
> **Entry**: real-analysis.monotone-function
@isnad1 id=iff.0h1v.s4.36a533af47ba from=translated src=- shape=63ff7a0c vocab=a507717f
-/
theorem monotone_iff_forall_le {f : ℝ → ℝ} : Monotone f ↔ ∀ x y, x ≤ y → f x ≤ f y :=
  Iff.rfl

/-- **集合上的单调（教材量词）**：`MonotoneOn f s ↔ ∀ x ∈ s, ∀ y ∈ s, x ≤ y → f x ≤ f y`。
教材通常只关心区间 `s = Icc a b` 或 `s = univ`；这里给出一般集合上的显式量词展开。
> **Entry**: real-analysis.monotone-function
@isnad1 id=iff.0h2v.s5.00145b1b27af from=translated src=- shape=774e50ee vocab=d0a97924
-/
theorem monotoneOn_iff_forall_le {f : ℝ → ℝ} {s : Set ℝ} :
    MonotoneOn f s ↔ ∀ x ∈ s, ∀ y ∈ s, x ≤ y → f x ≤ f y :=
  Iff.rfl

/-- **全局单调与全空间上单调等价**：`Monotone f ↔ MonotoneOn f univ`。这是教材「`f` 在
`ℝ` 上单调」与 Mathlib 两种承载（`Monotone`、`MonotoneOn`）之间的精确对照。
> **Entry**: real-analysis.monotone-function
@isnad1 id=iff.0h1v.s4.d4fd53b91db0 from=translated src=- shape=0e159c24 vocab=3b088093
-/
theorem monotone_iff_monotoneOn_univ {f : ℝ → ℝ} : Monotone f ↔ MonotoneOn f univ :=
  ⟨fun h => h.monotoneOn univ, fun h x y hxy => h (mem_univ x) (mem_univ y) hxy⟩

/-! ## 2. 间断结构：左极限、右极限与跳跃点 -/

/-- **左极限不超过函数值**：单调函数的左极限 `f(x⁻) = Function.leftLim f x` 满足
`f(x⁻) ≤ f x`（教材夹逼 `f(x⁻) ≤ f(x) ≤ f(x⁺)` 的左半）。Mathlib 只有
`Monotone.leftLim_le`（`x ≤ y ⟹ f(x⁻) ≤ f y`），本定理取 `y = x` 的教材特化。
> **Entry**: real-analysis.monotone-function
@isnad1 id=le.1h2v.s4.d2a15a9383cb from=translated src=- shape=10d3df22 vocab=dd31f5a2
-/
theorem leftLim_le_self {f : ℝ → ℝ} (hf : Monotone f) (x : ℝ) :
    Function.leftLim f x ≤ f x :=
  hf.leftLim_le le_rfl

/-- **函数值不超过右极限**：单调函数满足 `f x ≤ f(x⁺) = Function.rightLim f x`
（教材夹逼 `f(x⁻) ≤ f(x) ≤ f(x⁺)` 的右半）。
> **Entry**: real-analysis.monotone-function
@isnad1 id=le.1h2v.s4.b25657a995af from=translated src=- shape=816cebea vocab=cc142c94
-/
theorem self_le_rightLim {f : ℝ → ℝ} (hf : Monotone f) (x : ℝ) :
    f x ≤ Function.rightLim f x :=
  hf.le_rightLim le_rfl

/-- **跳跃非负**：单调函数的单侧极限满足 `f(x⁻) ≤ f(x⁺)`，即跳跃量 `f(x⁺) - f(x⁻) ≥ 0`。
这是 `Monotone.leftLim_le_rightLim`（`x ≤ y ⟹ f(x⁻) ≤ f(y⁺)`）在 `y = x` 的教材特化。
> **Entry**: real-analysis.monotone-function
@isnad1 id=le.1h2v.s5.a83f881f0074 from=translated src=- shape=812b9072 vocab=524aaa25
-/
theorem leftLim_le_rightLim_self {f : ℝ → ℝ} (hf : Monotone f) (x : ℝ) :
    Function.leftLim f x ≤ Function.rightLim f x :=
  hf.leftLim_le_rightLim le_rfl

/-- **连续 ⟺ 两个单侧极限都存在且都等于函数值**：对单调函数 `f`，
`ContinuousAt f x ↔ f(x⁻) = f x ∧ f(x⁺) = f x`。Mathlib 的
`Monotone.continuousAt_iff_leftLim_eq_rightLim` 只断言 `f(x⁻) = f(x⁺)`；由夹逼
`f(x⁻) ≤ f x ≤ f(x⁺)`（本文件 `leftLim_le_self`、`self_le_rightLim`）可补上「等于函数值」，
这正是教材对间断点（跳跃点）的定义形式。
> **Entry**: real-analysis.monotone-function
@isnad1 id=iff.1h2v.s5.591fbd12df09 from=translated src=- shape=850bc991 vocab=030d41ff
-/
theorem continuousAt_iff_leftLim_eq_self_and_rightLim_eq_self {f : ℝ → ℝ}
    (hf : Monotone f) (x : ℝ) :
    ContinuousAt f x ↔ Function.leftLim f x = f x ∧ Function.rightLim f x = f x := by
  constructor
  · intro h
    exact ⟨h.continuousWithinAt.leftLim_eq, h.continuousWithinAt.rightLim_eq⟩
  · rintro ⟨h1, h2⟩
    exact (hf.continuousAt_iff_leftLim_eq_rightLim).2 (h1.trans h2.symm)

/-- **单调函数的间断点至多可数（`ℝ → ℝ` 教材形式）**：`{x | ¬ ContinuousAt f x}` 可数。
Mathlib 的正式承载是 `Monotone.countable_not_continuousAt`，其假设为第二可数的值域空间；
本定理是 `ℝ → ℝ` 的教材特化（Folland §3.5 中「单调函数的间断点集至多可数」的原文情形）。
> **Entry**: real-analysis.monotone-function
@isnad1 id=countabl.1h1v.s5.0a4d01723ade from=translated src=- shape=aa01e6de vocab=1d858eff
-/
theorem countable_not_continuousAt_real {f : ℝ → ℝ} (hf : Monotone f) :
    {x : ℝ | ¬ ContinuousAt f x}.Countable :=
  hf.countable_not_continuousAt

/-- **跳跃点至多可数**：单调函数的跳跃点集
`{x | f(x⁻) < f(x⁺)}` 至多可数。由 `continuousAt_iff_leftLim_eq_self_and_rightLim_eq_self`
的判据，跳跃点恰是间断点，再用 `countable_not_continuousAt_real` 得证；这是教材「单调函数
只有可多个跳跃」的精确 Lean 形式（严格小于，而非 `≠`，用到了跳跃非负）。
> **Entry**: real-analysis.monotone-function
@isnad1 id=countabl.1h1v.s5.d8a5fdb448a8 from=translated src=- shape=12129ab6 vocab=018f2b8e
-/
theorem countable_jumpPoints {f : ℝ → ℝ} (hf : Monotone f) :
    {x : ℝ | Function.leftLim f x < Function.rightLim f x}.Countable := by
  refine Set.Countable.mono ?_ (countable_not_continuousAt_real hf)
  intro x hx hc
  exact absurd ((hf.continuousAt_iff_leftLim_eq_rightLim).1 hc) (ne_of_lt hx)

/-! ## 3. 几乎处处可导性 -/

/-- **单调函数 a.e. 可导，且导数等于 Stieltjes 测度关于 Lebesgue 的 Radon–Nikodym 导数**：
`∀ᵐ x ∂volume, HasDerivAt f ((hf.stieltjesFunction.measure).rnDeriv volume x).toReal x`。
这是 **a.e. 等式**，不是逐点等式；等号右端的测度是 `hf.stieltjesFunction.measure`
（`f` 的右连续化所定的局部有限 Borel 测度），参考测度是 `volume`（Lebesgue），
`Measure.rnDeriv` 取值 `ℝ≥0∞`，故外层取 `ENNReal.toReal`。

Mathlib 已有 `Monotone.ae_hasDerivAt`（同一命题，a.e. 滤子的测度由实例隐式给出）；本定理把
测度写成显式 `volume`，作为本 Entry 的桥头陈述与下一层 `ae_differentiableAt_volume` 的前提。
> **Entry**: real-analysis.monotone-function
@isnad1 id=eventual.1h1v.s6.53ddec48e2af from=translated src=- shape=34b66d7b vocab=090b3572
-/
theorem ae_hasDerivAt_volume {f : ℝ → ℝ} (hf : Monotone f) :
    ∀ᵐ x ∂(volume : Measure ℝ),
      HasDerivAt f (hf.stieltjesFunction.measure.rnDeriv volume x).toReal x :=
  hf.ae_hasDerivAt

/-- **单调函数 Lebesgue-a.e. 可导（显式测度形式）**：`∀ᵐ x ∂volume, DifferentiableAt ℝ f x`。
由 `ae_hasDerivAt_volume` 取 `HasDerivAt.differentiableAt` 得到。**这是 a.e. 结论，不得读成
逐点可导**；Mathlib 的对应承载是 `Monotone.ae_differentiableAt`。
> **Entry**: real-analysis.monotone-function
@isnad1 id=eventual.1h1v.s6.e7696965ba81 from=translated src=- shape=6312ffa5 vocab=2952e3cb
-/
theorem ae_differentiableAt_volume {f : ℝ → ℝ} (hf : Monotone f) :
    ∀ᵐ x ∂(volume : Measure ℝ), DifferentiableAt ℝ f x := by
  filter_upwards [ae_hasDerivAt_volume hf] with x hx using hx.differentiableAt

/-! ## 4. Stieltjes 测度桥（本 Entry 核心） -/

/-- **Stieltjes 测度是局部有限测度**：对单调函数 `f : ℝ → ℝ`，右连续化所定的
Lebesgue–Stieltjes 测度 `hf.stieltjesFunction.measure` 是 `ℝ` 上的局部有限 Borel 测度。
Mathlib 的实例是 `StieltjesFunction.instIsLocallyFiniteMeasure`；本定理把它作为教材命题
（「Stieltjes 测度在每个紧区间上有限」）暴露出来，供 Radon–Nikodym 与 a.e. 导数使用。
> **Entry**: real-analysis.monotone-function
@isnad1 id=islocall.1h1v.s5.fb492d6c97e4 from=translated src=- shape=e95f41fd vocab=0181a95a
-/
theorem stieltjesFunction_measure_isLocallyFinite {f : ℝ → ℝ} (hf : Monotone f) :
    IsLocallyFiniteMeasure hf.stieltjesFunction.measure :=
  inferInstance

/-- **右连续化的左极限等于原函数的左极限**：`leftLim (↑hf.stieltjesFunction) a = leftLim f a`，
即 `(f(·⁺))(a⁻) = f(a⁻)`。这条把 `StieltjesFunction.measure` 的区间公式中出现的
`leftLim (↑hf.stieltjesFunction)` 换回 `f` 自己的左极限，是下面五个区间测度公式的关键引理。
证明用左右极限的 `sSup`/`sInf` 刻画（`Monotone.leftLim_eq_sSup`、`Monotone.rightLim_eq_sInf`）
与 `csSup_le`、`le_csSup`、`le_csInf` 的夹逼。
> **Entry**: real-analysis.monotone-function
@isnad1 id=eq.1h2v.s5.edb820ea5ad2 from=translated src=- shape=0c2f6aea vocab=e2d14919
-/
theorem leftLim_stieltjesFunction {f : ℝ → ℝ} (hf : Monotone f) (a : ℝ) :
    Function.leftLim (hf.stieltjesFunction : ℝ → ℝ) a = Function.leftLim f a := by
  change Function.leftLim (Function.rightLim f) a = Function.leftLim f a
  rw [Monotone.leftLim_eq_sSup hf.rightLim, hf.leftLim_eq_sSup]
  refine le_antisymm (csSup_le ?_ ?_) (csSup_le ?_ ?_)
  · exact ⟨Function.rightLim f (a - 1), a - 1, by simp, rfl⟩
  · rintro b ⟨y, hy, rfl⟩
    obtain ⟨z, hyz, hza⟩ := exists_between (show y < a from hy)
    exact (hf.rightLim_le hyz).trans
      (le_csSup ⟨f a, by rintro b ⟨w, hw, rfl⟩; exact hf (le_of_lt hw)⟩ ⟨z, hza, rfl⟩)
  · exact ⟨f (a - 1), a - 1, by simp, rfl⟩
  · rintro b ⟨y, hy, rfl⟩
    exact (hf.le_rightLim le_rfl).trans
      (le_csSup ⟨Function.rightLim f a, by rintro b ⟨w, hw, rfl⟩; exact hf.rightLim (le_of_lt hw)⟩
        ⟨y, hy, rfl⟩)

/-- **右连续的单调函数与其 Stieltjes 函数相等**：若 `f` 右连续
（`∀ x, ContinuousWithinAt f (Ici x) x`），则 `hf.stieltjesFunction = ⟨f, hf, hrc⟩`，
即右连续化不再改变 `f`。这是「教材里 `μ_f((a,b]) = f(b) - f(a)`」成立的**充分条件**；
一般单调函数只有右连续化后的版本。
> **Entry**: real-analysis.monotone-function
@isnad1 id=eq.2h1v.s6.4d969ed81808 from=translated src=- shape=f2357f2d vocab=33772365
-/
theorem stieltjesFunction_eq_self {f : ℝ → ℝ} (hf : Monotone f)
    (hrc : ∀ x, ContinuousWithinAt f (Ici x) x) : hf.stieltjesFunction = ⟨f, hf, hrc⟩ := by
  ext x
  change Function.rightLim f x = f x
  exact (hrc x).rightLim_eq

/-- **Lebesgue–Stieltjes 测度的右半开区间公式（一般单调函数）**：
`μ_f((a,b]) = f(b⁺) - f(a⁺)`，其中 `μ_f = hf.stieltjesFunction.measure`。
Mathlib 的 `StieltjesFunction.measure_Ioc` 给出 `μ_f((a,b]) = f(b) - f(a)`（对
`StieltjesFunction` 自身），本定理把它翻译回原单调函数 `f` 的右极限。
> **Entry**: real-analysis.monotone-function
@isnad1 id=eq.1h3v.s6.a7d3c097f677 from=translated src=- shape=b9d6deca vocab=ec416425
-/
theorem stieltjesFunction_measure_Ioc {f : ℝ → ℝ} (hf : Monotone f) (a b : ℝ) :
    hf.stieltjesFunction.measure (Ioc a b) =
      ENNReal.ofReal (Function.rightLim f b - Function.rightLim f a) := by
  simp only [StieltjesFunction.measure_Ioc, Monotone.stieltjesFunction_eq]

/-- **Lebesgue–Stieltjes 测度的闭区间公式**：`μ_f([a,b]) = f(b⁺) - f(a⁻)`。
教材里写作 `μ_f([a,b]) = f(b) - f(a-)`（右连续约定下 `f(b⁺) = f(b)`）。
> **Entry**: real-analysis.monotone-function
@isnad1 id=eq.1h3v.s6.e305e1cd3706 from=translated src=- shape=b9d6deca vocab=5e975c79
-/
theorem stieltjesFunction_measure_Icc {f : ℝ → ℝ} (hf : Monotone f) (a b : ℝ) :
    hf.stieltjesFunction.measure (Icc a b) =
      ENNReal.ofReal (Function.rightLim f b - Function.leftLim f a) := by
  rw [StieltjesFunction.measure_Icc, leftLim_stieltjesFunction hf]
  simp only [Monotone.stieltjesFunction_eq]

/-- **Lebesgue–Stieltjes 测度的开区间公式**：`μ_f((a,b)) = f(b⁻) - f(a⁺)`。
开区间排除了两端点，故两端都取与区间内部一致的单侧极限。
> **Entry**: real-analysis.monotone-function
@isnad1 id=eq.1h3v.s6.e584c48396a9 from=translated src=- shape=b9d6deca vocab=568b8a78
-/
theorem stieltjesFunction_measure_Ioo {f : ℝ → ℝ} (hf : Monotone f) (a b : ℝ) :
    hf.stieltjesFunction.measure (Ioo a b) =
      ENNReal.ofReal (Function.leftLim f b - Function.rightLim f a) := by
  rw [StieltjesFunction.measure_Ioo, leftLim_stieltjesFunction hf]
  simp only [Monotone.stieltjesFunction_eq]

/-- **Lebesgue–Stieltjes 测度的左闭右开区间公式**：`μ_f([a,b)) = f(b⁻) - f(a⁻)`。
> **Entry**: real-analysis.monotone-function
@isnad1 id=eq.1h3v.s6.9045e0dbdccc from=translated src=- shape=b9d6deca vocab=de3c35f4
-/
theorem stieltjesFunction_measure_Ico {f : ℝ → ℝ} (hf : Monotone f) (a b : ℝ) :
    hf.stieltjesFunction.measure (Ico a b) =
      ENNReal.ofReal (Function.leftLim f b - Function.leftLim f a) := by
  simp only [StieltjesFunction.measure_Ico, leftLim_stieltjesFunction hf]

/-- **Lebesgue–Stieltjes 测度的单点公式（跳跃量）**：`μ_f({a}) = f(a⁺) - f(a⁻)`，
即单点测度恰为 `f` 在 `a` 处的跳跃量；由跳跃非负（`leftLim_le_rightLim_self`）知右端非负。
这是教材把「跳跃」与「Stieltjes 测度的原子部分」对应起来的关键等式。
> **Entry**: real-analysis.monotone-function
@isnad1 id=eq.1h2v.s6.263f823cd7cf from=translated src=- shape=903e4a36 vocab=2189de86
-/
theorem stieltjesFunction_measure_singleton {f : ℝ → ℝ} (hf : Monotone f) (a : ℝ) :
    hf.stieltjesFunction.measure {a} =
      ENNReal.ofReal (Function.rightLim f a - Function.leftLim f a) := by
  rw [StieltjesFunction.measure_singleton, leftLim_stieltjesFunction hf]
  simp only [Monotone.stieltjesFunction_eq]

/-- **教材形式：右连续单调函数的 Lebesgue–Stieltjes 测度满足 `μ_f((a,b]) = f(b) - f(a)`**：
在 `f` 右连续（`∀ x, ContinuousWithinAt f (Ici x) x`）时，
`hf.stieltjesFunction.measure (Ioc a b) = ENNReal.ofReal (f b - f a)`。
这正是 Folland §3.5 构造 Lebesgue–Stieltjes 测度时的定义式；一般单调函数必须先右连续化
（见 `stieltjesFunction_measure_Ioc`）。
> **Entry**: real-analysis.monotone-function
@isnad1 id=eq.2h3v.s6.19569db411c1 from=translated src=- shape=d8d7e3ea vocab=3695057c
-/
theorem stieltjesFunction_measure_Ioc_of_rightContinuous {f : ℝ → ℝ} (hf : Monotone f)
    (hrc : ∀ x, ContinuousWithinAt f (Ici x) x) (a b : ℝ) :
    hf.stieltjesFunction.measure (Ioc a b) = ENNReal.ofReal (f b - f a) := by
  rw [stieltjesFunction_measure_Ioc hf, (hrc b).rightLim_eq, (hrc a).rightLim_eq]

/-! ## 5. 与有界变差的接口（供 `real-analysis.bounded-variation` 使用） -/

end RealAnalysis.MonotoneFunction

end SandronesLibrary
