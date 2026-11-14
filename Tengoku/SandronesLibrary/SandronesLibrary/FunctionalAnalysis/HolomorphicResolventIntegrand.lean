/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.FunctionalAnalysis.HolomorphicNeighborhood
import Tengoku.Seed.Analysis.Complex.CauchyIntegral
import Tengoku.Seed.MeasureTheory.Integral.IntegrableOn

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 预解映射与 Dunford 被积函数

本文件发展全纯函数演算（Dunford 演算）中不依赖有限 cycle 的解析部分：

* 复 Banach 代数上的第一预解恒等式，以及同一元素在两个谱参数处预解元的乘法交换性；
* 预解映射 `resolvent a` 在预解集 `resolventSet ℂ a` 上的复可微性、全纯性与连续性；
* Dunford 被积函数 `fun z ↦ f z • resolvent a z` 在共同有效开集上的复可微性与连续性，
  以及它在紧集上的 Bochner 可积性。

本文件不定义有限 cycle、绕数、cycle 积分、Dunford 值 `f(a)`、代数同态、谱映射、谱投影或
连续函数演算；这些分别属于复分析的公共 Banach 值路径积分 carrier 或后续 F6.6b2 / F8 窗口。
-/

namespace SandronesLibrary.FunctionalAnalysis

open Set MeasureTheory
open scoped Ring Topology

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]

/-! ## 预解恒等式与乘法次序 -/

/-- 第一预解恒等式：同一元素 `a` 在两个谱参数 `z`、`w` 处的预解元之差等于
`(w - z) • (resolvent a z * resolvent a w)`。

Mathlib 只有不同元素在同一谱参数处的第二预解恒等式 `spectrum.resolvent_sub_resolvent`；
这里补上同一元素在两个谱参数处的第一预解恒等式，它由 `Ring.inverse_sub_inverse` 直接给出。

> **Entry**: functional-analysis.functional-calculus.resolvent-integrand-/
theorem resolvent_sub_resolvent_same (a : A) {z w : ℂ}
    (hz : z ∈ resolventSet ℂ a) (hw : w ∈ resolventSet ℂ a) :
    resolvent a z - resolvent a w =
      (w - z) • (resolvent a z * resolvent a w) := by
  have hunit : IsUnit (algebraMap ℂ A z - a) ↔ IsUnit (algebraMap ℂ A w - a) :=
    ⟨fun _ => hw, fun _ => hz⟩
  have hsub : (algebraMap ℂ A w - a) - (algebraMap ℂ A z - a) = (w - z) • (1 : A) := by
    rw [show (algebraMap ℂ A w - a) - (algebraMap ℂ A z - a) =
        algebraMap ℂ A w - algebraMap ℂ A z by abel]
    rw [← map_sub, Algebra.algebraMap_eq_smul_one]
  calc resolvent a z - resolvent a w
      = (algebraMap ℂ A z - a)⁻¹ʳ - (algebraMap ℂ A w - a)⁻¹ʳ := rfl
    _ = (algebraMap ℂ A z - a)⁻¹ʳ *
          ((algebraMap ℂ A w - a) - (algebraMap ℂ A z - a)) *
          (algebraMap ℂ A w - a)⁻¹ʳ := Ring.inverse_sub_inverse hunit
    _ = (w - z) •
          ((algebraMap ℂ A z - a)⁻¹ʳ * (algebraMap ℂ A w - a)⁻¹ʳ) := by
          simp only [hsub, mul_smul_comm, mul_one, smul_mul_assoc]
    _ = (w - z) • (resolvent a z * resolvent a w) := rfl

/-- 同一元素在两个谱参数处的预解元乘法交换。这里不需要预解集假设：`Ring.inverse` 把
不可逆元的逆约定为零，而 `z·1-a` 与 `w·1-a` 总交换，故交换性无条件成立。-/
theorem resolvent_mul_comm (a : A) (z w : ℂ) :
    resolvent a z * resolvent a w = resolvent a w * resolvent a z := by
  have hx : Commute (algebraMap ℂ A z) a := Algebra.commute_algebraMap_left z a
  have hy : Commute (algebraMap ℂ A w) a := Algebra.commute_algebraMap_left w a
  have hxy : Commute (algebraMap ℂ A z) (algebraMap ℂ A w) :=
    Algebra.commute_algebraMap_left z (algebraMap ℂ A w)
  have h : Commute (algebraMap ℂ A z - a) (algebraMap ℂ A w - a) :=
    (hxy.sub_right hx).sub_left (hy.symm.sub_right (Commute.refl a))
  exact (commute_iff_eq _ _).mp h.ringInverse_ringInverse

/-- 第一预解恒等式的交换次序形式：乘积写成 `resolvent a w * resolvent a z`。-/
theorem resolvent_sub_resolvent_same_mul_comm (a : A) {z w : ℂ}
    (hz : z ∈ resolventSet ℂ a) (hw : w ∈ resolventSet ℂ a) :
    resolvent a z - resolvent a w =
      (w - z) • (resolvent a w * resolvent a z) := by
  rw [resolvent_sub_resolvent_same a hz hw, resolvent_mul_comm a z w]

variable [CompleteSpace A]

/-! ## 预解映射的复可微性与全纯性 -/

/-- 预解映射在预解集上复可微；证明直接消费 Mathlib 的
`spectrum.hasDerivAt_resolvent_const_left`。-/
theorem differentiableOn_resolvent (a : A) :
    DifferentiableOn ℂ (resolvent a) (resolventSet ℂ a) :=
  fun _ hz =>
    (spectrum.hasDerivAt_resolvent_const_left hz).differentiableAt.differentiableWithinAt

/-- 预解集内每一点处预解映射复可微。-/
theorem differentiableAt_resolvent {a : A} {z : ℂ} (hz : z ∈ resolventSet ℂ a) :
    DifferentiableAt ℂ (resolvent a) z :=
  (spectrum.hasDerivAt_resolvent_const_left hz).differentiableAt

/-- 预解映射在预解集上全纯（作为开集上的解析函数）。-/
theorem analyticOnNhd_resolvent (a : A) :
    AnalyticOnNhd ℂ (resolvent a) (resolventSet ℂ a) :=
  (differentiableOn_resolvent a).analyticOnNhd (spectrum.isOpen_resolventSet a)

/-- 预解映射在预解集上连续。-/
theorem continuousOn_resolvent (a : A) :
    ContinuousOn (resolvent a) (resolventSet ℂ a) :=
  (differentiableOn_resolvent a).continuousOn

/-! ## Dunford 被积函数 -/

/-- Dunford 被积函数 `fun z ↦ f z • resolvent a z`。

它只组装标量函数与预解映射，本身不含 cycle、路径或积分；后续 F6.6b2 会在复分析提供公共
Banach 值路径积分 carrier 后对它积分。

> **Entry**: functional-analysis.functional-calculus.resolvent-integrand-/
noncomputable def resolventIntegrand (a : A) (f : ℂ → ℂ) : ℂ → A :=
  f • resolvent a

/-- 若 `f` 在开集 `U` 上复可微，则 Dunford 被积函数在共同有效开集 `U ∩ resolventSet ℂ a`
上复可微。-/
theorem differentiableOn_resolventIntegrand (a : A) {f : ℂ → ℂ} {U : Set ℂ}
    (hf : DifferentiableOn ℂ f U) :
    DifferentiableOn ℂ (resolventIntegrand a f) (U ∩ resolventSet ℂ a) :=
  (hf.mono inter_subset_left).smul
    ((differentiableOn_resolvent a).mono inter_subset_right)

/-- 同一共同有效开集上 Dunford 被积函数连续；由复可微性推出。-/
theorem continuousOn_resolventIntegrand (a : A) {f : ℂ → ℂ} {U : Set ℂ}
    (hf : DifferentiableOn ℂ f U) :
    ContinuousOn (resolventIntegrand a f) (U ∩ resolventSet ℂ a) :=
  (differentiableOn_resolventIntegrand a hf).continuousOn

/-- 对谱邻域全纯函数，存在见证开邻域 `U`，Dunford 被积函数在 `U ∩ resolventSet ℂ a`
上复可微。此处真实复用本库的 `HolomorphicOnNhdSpectrum`。-/
theorem HolomorphicOnNhdSpectrum.resolventIntegrand_differentiableOn {a : A} {f : ℂ → ℂ}
    (hf : HolomorphicOnNhdSpectrum a f) :
    ∃ U : Set ℂ, IsOpen U ∧ spectrum ℂ a ⊆ U ∧
      DifferentiableOn ℂ (resolventIntegrand a f) (U ∩ resolventSet ℂ a) := by
  obtain ⟨U, hU, haU, hfU⟩ := hf
  exact ⟨U, hU, haU, differentiableOn_resolventIntegrand a hfU⟩

/-- 对谱邻域全纯函数，Dunford 被积函数在共同有效开集上连续。-/
theorem HolomorphicOnNhdSpectrum.resolventIntegrand_continuousOn {a : A} {f : ℂ → ℂ}
    (hf : HolomorphicOnNhdSpectrum a f) :
    ∃ U : Set ℂ, IsOpen U ∧ spectrum ℂ a ⊆ U ∧
      ContinuousOn (resolventIntegrand a f) (U ∩ resolventSet ℂ a) := by
  obtain ⟨U, hU, haU, hfU⟩ := hf
  exact ⟨U, hU, haU, continuousOn_resolventIntegrand a hfU⟩

/-- 紧集上的 Bochner 可积性：若紧集 `K` 同时含于 `f` 的复可微开集 `U` 与预解集，
则 Dunford 被积函数在 `K` 上可积。这是后续沿紧路径积分真正需要的可积性引理，只使用
Mathlib 现有的 Banach 值 Bochner 积分接口。-/
theorem integrableOn_resolventIntegrand_compact (a : A) {f : ℂ → ℂ} {U K : Set ℂ}
    (hK : IsCompact K) (hKU : K ⊆ U) (hKV : K ⊆ resolventSet ℂ a)
    (hf : DifferentiableOn ℂ f U) :
    IntegrableOn (resolventIntegrand a f) K volume :=
  ((hf.mono hKU).continuousOn.smul ((continuousOn_resolvent a).mono hKV)).integrableOn_compact hK

end SandronesLibrary.FunctionalAnalysis
