/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.RealAnalysis.ProductMeasure
import Tengoku.Seed.MeasureTheory.Function.LpSpace.Basic
import Tengoku.Seed.MeasureTheory.Function.LpSpace.Complete

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# `Lᵖ` 空间：定义、几乎处处等价类与范数

教材常把 `Lᵖ` 暂写成满足 `∫ ‖f‖ᵖ < ∞` 的函数集合，但严格来说，几乎处处相等的
函数必须视为同一个元素，否则“范数为零推出函数为零”不成立。Mathlib 因而分两层：

* `MemLp f p μ` 是普通函数满足可测性和有限 `p`-范数的命题；
* `MeasureTheory.Lp E p μ` 是把函数按 `μ`-几乎处处相等取商后，再限制到有限
  `eLpNorm` 的真正赋范空间。

本文件固定这两层之间的教材接口，并在最后记录 `p ≥ 1` 时的 Riesz–Fischer 完备性。
Hölder、Chebyshev 与 Minkowski 等估计集中放在 `LpInequalities.lean`。
-/

namespace SandronesLibrary.RealAnalysis.Lp

open MeasureTheory Filter Topology
open scoped ENNReal

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
variable (μ : Measure α) (p : ℝ≥0∞)

/-- 本库的教材记号：`LpSpace E p μ` 就是 Mathlib 的 `MeasureTheory.Lp E p μ`。

> **Entry**: real-analysis.lp.basic-/
abbrev LpSpace (E : Type*) [NormedAddCommGroup E] (p : ℝ≥0∞) (μ : Measure α) :=
  MeasureTheory.Lp E p μ

/-- 普通函数属于 `Lᵖ` 的判据：它几乎处处强可测，并且扩展实数值 `p`-半范数有限。
@isnad1 id=iff.0h5v.s6.1e14b9976ae2 from=translated src=- shape=e83c3f81 vocab=27ae80e2
-/
theorem memLp_iff (f : α → E) :
    MemLp f p μ ↔ AEStronglyMeasurable f μ ∧ eLpNorm f p μ < ∞ := by
  rfl

/-- 把一个满足 `MemLp` 的普通函数送入按几乎处处相等取商后的 `Lᵖ` 空间。-/
noncomputable def ofFunction (f : α → E) (hf : MemLp f p μ) : LpSpace E p μ :=
  hf.toLp f

/-- `ofFunction` 所选出的代表元与原函数几乎处处相等。
@isnad1 id=eventual.1h5v.s8.6d914e7412a9 from=translated src=- shape=9e361b60 vocab=4e05548f
-/
theorem ofFunction_ae_eq (f : α → E) (hf : MemLp f p μ) :
    ofFunction μ p f hf =ᵐ[μ] f := by
  exact hf.coeFn_toLp

/-- 两个普通函数给出同一个 `Lᵖ` 元素，当且仅当它们几乎处处相等。

这条定理明确表达了 `Lᵖ` 的商空间本质，而不是把 `Lᵖ` 误认为逐点函数空间。
@isnad1 id=iff.2h6v.s8.b240b4838a4b from=translated src=- shape=653ec24b vocab=c047e3a0
-/
theorem ofFunction_eq_iff {f g : α → E} (hf : MemLp f p μ) (hg : MemLp g p μ) :
    ofFunction μ p f hf = ofFunction μ p g hg ↔ f =ᵐ[μ] g := by
  exact MemLp.toLp_eq_toLp_iff hf hg

/-- 从普通函数构造的 `Lᵖ` 元素，其实数范数是 `eLpNorm` 的有限实数值。
@isnad1 id=eq.1h5v.s8.365646b4a2c0 from=translated src=- shape=b1727bc0 vocab=cd8e974e
-/
theorem norm_ofFunction (f : α → E) (hf : MemLp f p μ) :
    ‖ofFunction μ p f hf‖ = ENNReal.toReal (eLpNorm f p μ) := by
  exact MeasureTheory.Lp.norm_toLp f hf

/-- `Lᵖ` 加法由代表元逐点相加给出，但等式只能在几乎处处意义下陈述。
@isnad1 id=eventual.0h6v.s10.a2704cd837cf from=translated src=- shape=c227c56b vocab=14dd3613
-/
theorem add_ae_eq (f g : LpSpace E p μ) :
    ⇑(f + g) =ᵐ[μ] fun x => f x + g x := by
  exact MeasureTheory.Lp.coeFn_add f g

/-- `Lᵖ` 元素等于零，当且仅当它的任意函数代表几乎处处为零。
@isnad1 id=iff.0h5v.s9.55304e340af0 from=translated src=- shape=84440fc0 vocab=7635b558
-/
theorem zero_iff_ae_zero (f : LpSpace E p μ) :
    f = 0 ↔ f =ᵐ[μ] (0 : α → E) := by
  exact MeasureTheory.Lp.eq_zero_iff_ae_eq_zero

/-! ## Riesz–Fischer 完备性 -/

/-- **`Lᵖ` 空间的完备性（Riesz–Fischer 定理）**：若值域 `E` 完备且 `p ≥ 1`，
则按几乎处处相等取商后的 `Lᵖ` 空间也是完备空间。

指数条件使用 `Fact (1 ≤ p)`，因为 `LpSpace E p μ` 的范数和度量结构本身就需要
在类型类搜索阶段知道 `p ≥ 1`。在具体应用中可用
`letI : Fact (1 ≤ p) := ⟨hp⟩` 把普通不等式假设安装为局部实例。

> **Entry**: real-analysis.lp.complete
@isnad1 id=complete.0h4v.s9.602617ea045b from=translated src=- shape=76b583b3 vocab=3bd8e97a
-/
theorem completeSpace_lp [CompleteSpace E] [Fact (1 ≤ p)] :
    CompleteSpace (LpSpace E p μ) := by
  infer_instance

/-- **Riesz–Fischer 的序列形式**：`Lᵖ` 中的每个 Cauchy 列都收敛到某个 `Lᵖ`
元素。这是完备性的教材展开式，便于后续直接构造极限函数时引用。

极限元素是几乎处处等价类，而不是预先指定的逐点函数；因此结论使用 `LpSpace`
中的范数拓扑收敛。
@isnad1 id=ex.1h5v.s11.8abdba28accf from=translated src=- shape=397d4336 vocab=cf8aa168
-/
theorem cauchySeq_tendsto_lp [CompleteSpace E] [Fact (1 ≤ p)]
    {u : ℕ → LpSpace E p μ} (hu : CauchySeq u) :
    ∃ f : LpSpace E p μ, Tendsto u atTop (𝓝 f) := by
  exact CompleteSpace.complete hu

end SandronesLibrary.RealAnalysis.Lp
