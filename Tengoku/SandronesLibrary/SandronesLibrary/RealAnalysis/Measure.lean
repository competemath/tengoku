/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# RealAnalysis / Measure —— 测度论基础（数学分析第二学期 R1）

本文件当前条目（引理清单，§0 铁律4：一次一条，逐条编译）：

* **real-analysis.measure.sigma-algebra**（σ-代数公理：空/全集/补/可数并/有限交并可测）✅。
* **real-analysis.measure.def**（测度公理：空集零测/可数可加/单调性/有限可加）✅。
* **real-analysis.measure.outer**（外测度次可加性）✅。
* **real-analysis.measure.caratheodory**（Carathéodory 定理：可测集构成 σ-代数/判据）✅。
* **real-analysis.measure.measurable-function**（可测函数：恒等/常/复合）✅。
* **real-analysis.measure.lintegral**（非负积分：常数/单调/零测）✅。
* **real-analysis.measure.monotone-convergence**（单调收敛定理 MCT）✅。
* **real-analysis.measure.fatou**（Fatou 引理）✅。
* **real-analysis.measure.dominated-convergence**（控制收敛定理 DCT）✅。
* **real-analysis.lebesgue-measure**（Lebesgue 测度：区间长度/区间可测）✅。

> **语言说明**：实分析阶段（§Phase5）mathlib 的 `MeasurableSpace`/`MeasurableSet`/
> `Measure` 等**教材结构可直接出现在签名**（测度积分是 mathlib 的核心库）。
-/

namespace SandronesLibrary

namespace RealAnalysis.Measure

open MeasureTheory Filter
open scoped Topology ENNReal

/-- **σ-代数公理：空集可测**。 
> **Entry**: real-analysis.measure.sigma-algebra-/
theorem meas_measurable_empty {X : Type*} [MeasurableSpace X] : MeasurableSet (∅ : Set X) := by
  exact MeasurableSet.empty

/-- **σ-代数公理：全集可测**。 
> **Entry**: real-analysis.measure.sigma-algebra-/
theorem meas_measurable_univ {X : Type*} [MeasurableSpace X] : MeasurableSet (Set.univ : Set X) := by
  exact MeasurableSet.univ

/-- **σ-代数公理：补集可测**。 
> **Entry**: real-analysis.measure.sigma-algebra-/
theorem meas_measurable_compl {X : Type*} [MeasurableSpace X] {s : Set X}
    (hs : MeasurableSet s) : MeasurableSet sᶜ := by
  exact hs.compl

/-- **σ-代数公理：可数并可测**。 
> **Entry**: real-analysis.measure.sigma-algebra-/
theorem meas_measurable_iUnion {X : Type*} {ι : Type*} [MeasurableSpace X] [Countable ι]
    {f : ι → Set X} (h : ∀ i : ι, MeasurableSet (f i)) : MeasurableSet (⋃ i, f i) := by
  exact MeasurableSet.iUnion h

/-- **σ-代数公理：有限交可测**。 
> **Entry**: real-analysis.measure.sigma-algebra-/
theorem meas_measurable_inter {X : Type*} [MeasurableSpace X] {s t : Set X}
    (hs : MeasurableSet s) (ht : MeasurableSet t) : MeasurableSet (s ∩ t) := by
  exact hs.inter ht

/-- **σ-代数公理：有限并可测**。 
> **Entry**: real-analysis.measure.sigma-algebra-/
theorem meas_measurable_union {X : Type*} [MeasurableSpace X] {s t : Set X}
    (hs : MeasurableSet s) (ht : MeasurableSet t) : MeasurableSet (s ∪ t) := by
  exact hs.union ht

/-- **测度公理：空集零测**：μ(∅) = 0。 
> **Entry**: real-analysis.measure.def-/
theorem meas_measure_empty {X : Type*} [MeasurableSpace X] (μ : Measure X) : μ ∅ = 0 := by
  exact measure_empty

/-- **测度公理：可数可加性**：可数个两两不交的可测集的并的测度 = 各测度之和。 
> **Entry**: real-analysis.measure.def-/
theorem meas_measure_sUnion {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {S : Set (Set X)} (hs : S.Countable) (hd : S.Pairwise Disjoint)
    (hmeas : ∀ s ∈ S, MeasurableSet s) : μ (⋃₀ S) = ∑' s : S, μ s := by
  exact measure_sUnion (μ := μ) hs hd hmeas

/-- **测度单调性**：s ⊆ t ⟹ μ(s) ≤ μ(t)。 
> **Entry**: real-analysis.measure.def-/
theorem meas_measure_mono {X : Type*} [MeasurableSpace X] (μ : Measure X) {s t : Set X}
    (hst : s ⊆ t) : μ s ≤ μ t := by
  exact measure_mono hst

/-- **测度有限可加性**：不相交可测集的并的测度 = 测度之和。 
> **Entry**: real-analysis.measure.def-/
theorem meas_measure_union {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {s₁ s₂ : Set X} (hd : Disjoint s₁ s₂) (hmeas : MeasurableSet s₂) :
    μ (s₁ ∪ s₂) = μ s₁ + μ s₂ := by
  exact measure_union hd hmeas

/-- **外测度次可加性**：外测度满足可数次可加——可数并的测度不超过各测度之和。 
> **Entry**: real-analysis.measure.outer-/
theorem meas_outer_measure_iUnion_le {X : Type*} {ι : Type*} [Countable ι]
    (m : OuterMeasure X) {s : ι → Set X} : m (⋃ i, s i) ≤ ∑' i, m (s i) := by
  exact measure_iUnion_le s

/-- **Carathéodory 判据**：s 可测 ⟺ 对一切 t，m(t) = m(t∩s) + m(t\s)。
  这是外测度限制成测度的核心判据。 
> **Entry**: real-analysis.measure.caratheodory-/
theorem meas_caratheodory_iff {X : Type*} {m : OuterMeasure X} {s : Set X} :
    MeasurableSet[m.caratheodory] s ↔ ∀ t : Set X, m t = m (t ∩ s) + m (t \ s) := by
  exact m.isCaratheodory_iff

/-- **可测函数：恒等**。 
> **Entry**: real-analysis.measure.measurable-function-/
theorem meas_measurable_id {X : Type*} [MeasurableSpace X] : Measurable (id : X → X) := by
  exact measurable_id

/-- **可测函数：常函数**。 
> **Entry**: real-analysis.measure.measurable-function-/
theorem meas_measurable_const {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (y : Y) :
    Measurable (fun _ : X => y) := by
  exact measurable_const

/-- **可测函数：复合**。 
> **Entry**: real-analysis.measure.measurable-function-/
theorem meas_measurable_comp {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    {f : X → Y} {g : Y → Z} (hg : Measurable g) (hf : Measurable f) : Measurable (g ∘ f) := by
  exact hg.comp hf

/-- **常数函数的积分**：∫⁻ c ∂μ = c · μ(X)（μ 是全空间测度）。 
> **Entry**: real-analysis.measure.lintegral-/
theorem meas_lintegral_const {X : Type*} [MeasurableSpace X] (μ : Measure X) (c : ℝ≥0∞) :
    (∫⁻ _, c ∂μ) = c * μ Set.univ := by
  exact lintegral_const c

/-- **积分的单调性**：f ≤ g（逐点）⟹ ∫⁻f ≤ ∫⁻g。 
> **Entry**: real-analysis.measure.lintegral-/
theorem meas_lintegral_mono {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {f g : X → ℝ≥0∞} (h : ∀ x, f x ≤ g x) : (∫⁻ x, f x ∂μ) ≤ (∫⁻ x, g x ∂μ) := by
  exact lintegral_mono h

/-- **非负积分零 ⟺ 函数几乎处处为零**：∫⁻f = 0 ⟺ f =ᵐ[μ] 0（可测 f）。 
> **Entry**: real-analysis.measure.lintegral-/
theorem meas_lintegral_eq_zero_iff {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {f : X → ℝ≥0∞} (hf : Measurable f) : (∫⁻ x, f x ∂μ) = 0 ↔ f =ᵐ[μ] 0 := by
  exact lintegral_eq_zero_iff hf

/-- **单调收敛定理（MCT）**：非负可测单调递增序列的积分 = 极限的积分。
  ∫⁻(⨆ fₙ) = ⨆ ∫⁻fₙ。 
> **Entry**: real-analysis.measure.monotone-convergence-/
theorem meas_lintegral_iSup {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {f : ℕ → X → ℝ≥0∞} (hf : ∀ n, Measurable (f n)) (h_mono : Monotone f) :
    (∫⁻ a, (⨆ n, f n a) ∂μ) = ⨆ n, ∫⁻ a, f n a ∂μ := by
  exact lintegral_iSup hf h_mono

/-- **Fatou 引理**：非负可测函数的 liminf 的积分 ≤ liminf 的积分。
  ∫⁻(liminf f) ≤ liminf ∫⁻f。 
> **Entry**: real-analysis.measure.fatou-/
theorem meas_lintegral_liminf_le {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {f : ℕ → X → ℝ≥0∞} (hf : ∀ n, Measurable (f n)) :
    (∫⁻ a, Filter.liminf (fun n => f n a) atTop ∂μ) ≤ Filter.liminf (fun n => ∫⁻ a, f n a ∂μ) atTop := by
  exact lintegral_liminf_le hf

/-- **控制收敛定理（DCT）**：若 Fₙ 被可积函数 bound 逐点控制，且 Fₙ → f a.e.，
  则 ∫Fₙ → ∫f。 
> **Entry**: real-analysis.measure.dominated-convergence-/
theorem meas_tendsto_lintegral_of_dominated {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {F : ℕ → X → ℝ≥0∞} {f : X → ℝ≥0∞} (bound : X → ℝ≥0∞)
    (hF_meas : ∀ n, Measurable (F n)) (h_bound : ∀ n, F n ≤ᵐ[μ] bound)
    (h_fin : (∫⁻ a, bound a ∂μ) ≠ ∞) (h_lim : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) atTop (𝓝 (f a))) :
    Tendsto (fun n => ∫⁻ a, F n a ∂μ) atTop (𝓝 (∫⁻ a, f a ∂μ)) := by
  exact tendsto_lintegral_of_dominated_convergence bound hF_meas h_bound h_fin h_lim

open scoped Interval

/-- **Lebesgue 测度的区间长度**：闭区间 [a,b] 的 Lebesgue 测度 = b-a。 
> **Entry**: real-analysis.lebesgue-measure-/
theorem meas_volume_Icc {a b : ℝ} : volume (Set.Icc a b) = ENNReal.ofReal (b - a) := by
  exact Real.volume_Icc

/-- **Lebesgue 测度的开区间长度**：开区间 (a,b) 的 Lebesgue 测度 = b-a。 
> **Entry**: real-analysis.lebesgue-measure-/
theorem meas_volume_Ioo {a b : ℝ} : volume (Set.Ioo a b) = ENNReal.ofReal (b - a) := by
  exact Real.volume_Ioo

/-- **闭区间 Lebesgue 可测**。 
> **Entry**: real-analysis.lebesgue-measure-/
theorem meas_measurable_Icc {a b : ℝ} : MeasurableSet (Set.Icc a b) := by
  exact measurableSet_Icc

/-- **开区间 Lebesgue 可测**。 
> **Entry**: real-analysis.lebesgue-measure-/
theorem meas_measurable_Ioo {a b : ℝ} : MeasurableSet (Set.Ioo a b) := by
  exact measurableSet_Ioo

end RealAnalysis.Measure

end SandronesLibrary
