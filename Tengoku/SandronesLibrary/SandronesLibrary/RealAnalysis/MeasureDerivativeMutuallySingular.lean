/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# RealAnalysis / MeasureDerivativeMutuallySingular —— 互奇异测度（Folland RA-F2）

本文件当前条目（引理清单）：

* **real-analysis.measure-derivative.mutually-singular**（互奇异测度 `μ ⟂ₘ ν`：教材定义
  “存在可测集 `s` 使 `μ s = 0` 且 `ν sᶜ = 0`”的显式量词展开、零测度／加法／标量倍／单调性等
  基本性质、与 `Disjoint` 测度和 `ae` 滤子的桥，以及互奇异与绝对连续相遇时测度为零的关键使用者）✅。

> **语言说明**：实分析阶段（§Phase5）mathlib 的 `MeasureTheory.Measure.MutuallySingular`
> 与 Folland 第 3 章 §3.2 的定义逐字一致（存在一个可测集 `s`，`μ` 集中在 `s` 上为零、
> `ν` 集中在 `sᶜ` 上为零），故本库直接复用该谓词与记号 `μ ⟂ₘ ν` 作为**正式公开承载**，
> 不另造同构 `def`；本文件只补教材量词展开、零测度与代数性质、与滤子／集合论不相交的桥。

### Mathlib 角色（本文件）

* `MeasureTheory.Measure.MutuallySingular` + 记号 `⟂ₘ`：**正式公开承载**（课程定义直接采用）。
* `Measure.MutuallySingular.comm/symm/zero_left/zero_right/add_left/add_right/smul/mono/self_iff/
  withDensity`：语义一致的**性质后端**，本文件把它们提升为教材命题名。
* `Measure.MutuallySingular.nullSet` 及 `measurableSet_nullSet`／`measure_nullSet`／
  `measure_compl_nullSet`：定义中见证互奇异的集合 `s` 的公开载体与它满足的两条测度等式
  （本库的展开/刻画）。
* `Measure.mutuallySingular_iff_disjoint`、`Measure.mutuallySingular_iff_disjoint_ae`：互奇异
  ↔ 测度（作为 `Measure α` 上的格元素）不相交、↔ 几乎处处滤子不相交的**桥**。
* `Measure.eq_zero_of_absolutelyContinuous_of_mutuallySingular`：互奇异与绝对连续相遇时测度为零，
  是本 Entry 的**关键使用者**，连接 `real-analysis.measure-derivative.absolute-continuity`。
* `MeasureTheory.withDensity_absolutelyContinuous`：密度测度 `μ.withDensity f` 的绝对连续方向，
  在 `Measure.MutuallySingular.withDensity` 这一侧与互奇异相互作用（Radon–Nikodym 前置）。
-/

namespace SandronesLibrary

namespace RealAnalysis.MeasureDerivative

open MeasureTheory
open scoped MeasureTheory ENNReal

variable {α : Type*} [MeasurableSpace α]
  {μ ν ν' ν₁ ν₂ μ₁ μ₂ : Measure α}

/-! ## 1. 定义与量词展开 -/

/-- **互奇异（Folland §3.2 定义）**：`μ` 与 `ν` 互奇异，当且仅当存在可测集 `s` 使得
`μ s = 0` 且 `ν sᶜ = 0`（即 `s` 是 `μ` 的零集、其补是 `ν` 的零集）。本定理给出教材量词的
显式展开；Mathlib 的定义本身即为该量词，故为 `Iff.rfl`。
> **Entry**: real-analysis.measure-derivative.mutually-singular
@isnad1 id=iff.0h3v.s6.fe0e4dd50a48 from=translated src=- shape=49c5d9c8 vocab=fdd04ef9
-/
theorem mutuallySingular_iff (μ ν : Measure α) :
    μ ⟂ₘ ν ↔ ∃ s : Set α, MeasurableSet s ∧ μ s = 0 ∧ ν sᶜ = 0 :=
  Iff.rfl

/-- **见证集合可测**：若 `μ ⟂ₘ ν`，则其定义中的见证集合 `h.nullSet` 可测。
> **Entry**: real-analysis.measure-derivative.mutually-singular
@isnad1 id=measurab.1h3v.s4.3e1c80616d9e from=translated src=- shape=37418f1c vocab=ce52aa6a
-/
theorem mutuallySingular_nullSet_measurable (h : μ ⟂ₘ ν) : MeasurableSet h.nullSet :=
  h.measurableSet_nullSet

/-- **见证集合是 `μ`-零集**：若 `μ ⟂ₘ ν`，则 `μ h.nullSet = 0`。
> **Entry**: real-analysis.measure-derivative.mutually-singular
@isnad1 id=eq.1h3v.s5.f766803c074d from=translated src=- shape=c6795780 vocab=1528256e
-/
theorem mutuallySingular_nullSet_measure (h : μ ⟂ₘ ν) : μ h.nullSet = 0 :=
  h.measure_nullSet

/-- **见证集合的补是 `ν`-零集**：若 `μ ⟂ₘ ν`，则 `ν h.nullSetᶜ = 0`。
> **Entry**: real-analysis.measure-derivative.mutually-singular
@isnad1 id=eq.1h3v.s5.0f5ddd0a97d9 from=translated src=- shape=cb0aacac vocab=955d8f00
-/
theorem mutuallySingular_measure_compl_nullSet (h : μ ⟂ₘ ν) : ν h.nullSetᶜ = 0 :=
  h.measure_compl_nullSet

/-! ## 2. 交换、自反与零测度 -/

/-- **互异性的对称性（`↔` 形式）**：`μ ⟂ₘ ν` 当且仅当 `ν ⟂ₘ μ`。
> **Entry**: real-analysis.measure-derivative.mutually-singular
@isnad1 id=iff.0h3v.s4.6d50c68f80e4 from=translated src=- shape=0a1543a7 vocab=c044da4b
-/
theorem mutuallySingular_comm : μ ⟂ₘ ν ↔ ν ⟂ₘ μ :=
  Measure.MutuallySingular.comm

/-- **互异性的对称性（蕴含形式）**：`ν ⟂ₘ μ` 蕴含 `μ ⟂ₘ ν`。
> **Entry**: real-analysis.measure-derivative.mutually-singular
@isnad1 id=mutually.1h3v.s4.a9eaf16f5035 from=translated src=- shape=2631c8c5 vocab=c044da4b
-/
theorem mutuallySingular_symm (h : ν ⟂ₘ μ) : μ ⟂ₘ ν :=
  h.symm

/-- **零测度在左互奇异**：`0 ⟂ₘ μ`。
> **Entry**: real-analysis.measure-derivative.mutually-singular
@isnad1 id=mutually.0h2v.s4.247ad3727684 from=translated src=- shape=c76b362b vocab=c044da4b
-/
theorem mutuallySingular_zero_left (μ : Measure α) : (0 : Measure α) ⟂ₘ μ :=
  Measure.MutuallySingular.zero_left

/-- **零测度在右互奇异**：`μ ⟂ₘ 0`。
> **Entry**: real-analysis.measure-derivative.mutually-singular
@isnad1 id=mutually.0h2v.s4.524d63bcf5b1 from=translated src=- shape=fe8a939f vocab=c044da4b
-/
theorem mutuallySingular_zero_right (μ : Measure α) : μ ⟂ₘ 0 :=
  Measure.MutuallySingular.zero_right

/-- **与自身互奇异刻画零测度**：`μ ⟂ₘ μ` 当且仅当 `μ = 0`。
> **Entry**: real-analysis.measure-derivative.mutually-singular
@isnad1 id=iff.0h2v.s5.268df2eb798f from=translated src=- shape=7d64aec5 vocab=c044da4b
-/
theorem mutuallySingular_self_iff (μ : Measure α) : μ ⟂ₘ μ ↔ μ = 0 :=
  Measure.MutuallySingular.self_iff μ

/-! ## 3. 代数性质（加法、标量倍、单调性） -/

/-- **左端加法**：`ν₁ ⟂ₘ μ`、`ν₂ ⟂ₘ μ` 蕴含 `ν₁ + ν₂ ⟂ₘ μ`。
> **Entry**: real-analysis.measure-derivative.mutually-singular
@isnad1 id=mutually.2h4v.s5.f4a72336ed80 from=translated src=- shape=8d80c994 vocab=9e4df1a5
-/
theorem mutuallySingular_add_left (h₁ : ν₁ ⟂ₘ μ) (h₂ : ν₂ ⟂ₘ μ) : ν₁ + ν₂ ⟂ₘ μ :=
  Measure.MutuallySingular.add_left h₁ h₂

/-- **右端加法**：`μ ⟂ₘ ν₁`、`μ ⟂ₘ ν₂` 蕴含 `μ ⟂ₘ ν₁ + ν₂`。
> **Entry**: real-analysis.measure-derivative.mutually-singular
@isnad1 id=mutually.2h4v.s5.fd6aa4898124 from=translated src=- shape=c7405e2f vocab=9e4df1a5
-/
theorem mutuallySingular_add_right (h₁ : μ ⟂ₘ ν₁) (h₂ : μ ⟂ₘ ν₂) : μ ⟂ₘ ν₁ + ν₂ :=
  Measure.MutuallySingular.add_right h₁ h₂

/-- **单调性**：若 `μ₁ ⟂ₘ ν₁`、`μ₂ ≤ μ₁`、`ν₂ ≤ ν₁`，则 `μ₂ ⟂ₘ ν₂`。
教材中常表述为“互异性的子测度仍互奇异”。
> **Entry**: real-analysis.measure-derivative.mutually-singular
@isnad1 id=mutually.3h5v.s6.aab48409a65f from=translated src=- shape=5adbf986 vocab=a84edbf1
-/
theorem mutuallySingular_mono (h : μ₁ ⟂ₘ ν₁) (hμ : μ₂ ≤ μ₁) (hν : ν₂ ≤ ν₁) : μ₂ ⟂ₘ ν₂ :=
  h.mono hμ hν

/-- **密度测度在左端保持互奇异**：若 `μ ⟂ₘ ν`，则对任意 `f : α → ℝ≥0∞` 有
`μ.withDensity f ⟂ₘ ν`。
> **Entry**: real-analysis.measure-derivative.mutually-singular
@isnad1 id=mutually.1h4v.s5.b600e94a618f from=translated src=- shape=a81d4cc6 vocab=288e3c84
-/
theorem mutuallySingular_withDensity (h : μ ⟂ₘ ν) (f : α → ℝ≥0∞) :
    μ.withDensity f ⟂ₘ ν :=
  h.withDensity (f := f)

/-! ## 4. 与集合论不相交、a.e. 滤子的桥，以及关键使用者 -/

/-- **与 `Measure` 格运算的桥**：`μ ⟂ₘ ν` 当且仅当测度作为 `Measure α` 中的元素不相交
（`Disjoint μ ν`，即下确界为 `0`）。这把互奇异性接入测度格的序结构。
> **Entry**: real-analysis.measure-derivative.mutually-singular
@isnad1 id=iff.0h3v.s5.7780c80767a6 from=translated src=- shape=b788bff8 vocab=7d0f83be
-/
theorem mutuallySingular_iff_disjoint : μ ⟂ₘ ν ↔ Disjoint μ ν :=
  Measure.mutuallySingular_iff_disjoint

/-- **与几乎处处滤子的桥**：`μ ⟂ₘ ν` 当且仅当 `ae μ` 与 `ae ν` 作为滤子不相交
（`Disjoint (ae μ) (ae ν)`），即“`μ`-a.e. 的性质”与“`ν`-a.e. 的性质”互相独立。
> **Entry**: real-analysis.measure-derivative.mutually-singular
@isnad1 id=iff.0h3v.s5.1cb14ea51d10 from=translated src=- shape=b6519261 vocab=0516453c
-/
theorem mutuallySingular_iff_disjoint_ae : μ ⟂ₘ ν ↔ Disjoint (ae μ) (ae ν) :=
  Measure.mutuallySingular_iff_disjoint_ae

/-- **关键使用者：互奇异 + 绝对连续 ⟹ 零测度**：若 `μ ≪ ν` 且 `μ ⟂ₘ ν`，则 `μ = 0`。
这是本 Entry 与 `real-analysis.measure-derivative.absolute-continuity` 的连接点，
也是 Lebesgue 分解唯一性的核心代数事实。
> **Entry**: real-analysis.measure-derivative.mutually-singular-/
theorem eq_zero_of_mutuallySingular_of_absolutelyContinuous
    (h_ac : μ ≪ ν) (h_ms : μ ⟂ₘ ν) : μ = 0 :=
  Measure.eq_zero_of_absolutelyContinuous_of_mutuallySingular h_ac h_ms

end RealAnalysis.MeasureDerivative

end SandronesLibrary
