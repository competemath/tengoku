/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.RealAnalysis.Riemann
import Tengoku.Seed.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Riemann 积分的代数、序性质与中值定理

本模块处理闭区间连续函数的教材型 Riemann 积分性质。核心策略不是重新展开
Darboux 上下和，而是调用 `riemannIntegral_eq_interval`：该定理已经证明自建
Riemann 积分值与 Mathlib 区间积分值相等，因此可在区间积分侧完成代数运算，
再把结论转回 `riemannIntegral`。

这里仍然得到的是本库自建 Riemann 积分的定理；Mathlib 只承担等值桥梁之后的
积分计算，不提供 Riemann 积分定义。文件末尾进一步收录积分中值定理以及连续
周期函数在一个完整周期上的积分不依赖起点这一应用。
-/

namespace SandronesLibrary.RealAnalysis.Riemann

open MeasureTheory
open scoped ENNReal Interval BigOperators

/-- 常值函数在非退化闭区间上黎曼可积。
> **Entry**: real-analysis.riemann.algebra-/
theorem riemannIntegrable_const_lt {a b c : ℝ} (hab : a < b) :
    RiemannIntegrable (fun _ : ℝ => c) a b := by
  exact continuous_on_riemannIntegrable_lt hab continuousOn_const

/-- 常值函数的黎曼积分等于常数乘区间长度。-/
theorem riemannIntegral_const {a b c : ℝ} (hab : a < b) :
    riemannIntegral (fun _ : ℝ => c) a b = c * (b - a) := by
  rw [riemannIntegral_eq_interval hab continuousOn_const]
  rw [integral_const]
  simp [hab.le, mul_comm]

/-- 连续函数之和的黎曼积分满足线性。-/
theorem riemannIntegral_add {f g : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b)) (hg : ContinuousOn g (Set.Icc a b)) :
    riemannIntegral (fun x => f x + g x) a b =
      riemannIntegral f a b + riemannIntegral g a b := by
  rw [riemannIntegral_eq_interval (f := fun x => f x + g x) hab (hf.add hg),
    riemannIntegral_eq_interval hab hf, riemannIntegral_eq_interval hab hg]
  have hfi := continuous_intervalIntegrable hab.le hf
  have hgi := continuous_intervalIntegrable hab.le hg
  simpa only [intervalIntegral.integral_of_le hab.le] using
    intervalIntegral.integral_add hfi hgi

/-- 连续函数之差的黎曼积分满足线性。-/
theorem riemannIntegral_sub {f g : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b)) (hg : ContinuousOn g (Set.Icc a b)) :
    riemannIntegral (fun x => f x - g x) a b =
      riemannIntegral f a b - riemannIntegral g a b := by
  rw [riemannIntegral_eq_interval (f := fun x => f x - g x) hab (hf.sub hg),
    riemannIntegral_eq_interval hab hf, riemannIntegral_eq_interval hab hg]
  have hfi := continuous_intervalIntegrable hab.le hf
  have hgi := continuous_intervalIntegrable hab.le hg
  simpa only [intervalIntegral.integral_of_le hab.le] using
    intervalIntegral.integral_sub hfi hgi

/-- 连续函数乘常数后，常数可提出黎曼积分号。-/
theorem riemannIntegral_const_mul {f : ℝ → ℝ} {a b c : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b)) :
    riemannIntegral (fun x => c * f x) a b = c * riemannIntegral f a b := by
  rw [riemannIntegral_eq_interval (f := fun x => c * f x) hab (continuousOn_const.mul hf),
    riemannIntegral_eq_interval hab hf]
  simpa only [intervalIntegral.integral_of_le hab.le] using
    intervalIntegral.integral_const_mul c f (a := a) (b := b) (μ := volume)

/-- 区间上非负的连续函数具有非负黎曼积分。-/
theorem riemannIntegral_nonneg {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b)) (h0 : ∀ x ∈ Set.Icc a b, 0 ≤ f x) :
    0 ≤ riemannIntegral f a b := by
  rw [riemannIntegral_eq_interval hab hf, ← intervalIntegral.integral_of_le hab.le]
  exact intervalIntegral.integral_nonneg hab.le h0

/-- 连续函数逐点有序时，其黎曼积分保持该顺序。-/
theorem riemannIntegral_mono {f g : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b)) (hg : ContinuousOn g (Set.Icc a b))
    (hfg : ∀ x ∈ Set.Icc a b, f x ≤ g x) :
    riemannIntegral f a b ≤ riemannIntegral g a b := by
  rw [riemannIntegral_eq_interval hab hf, riemannIntegral_eq_interval hab hg,
    ← intervalIntegral.integral_of_le hab.le, ← intervalIntegral.integral_of_le hab.le]
  exact intervalIntegral.integral_mono_on hab.le
    (continuous_intervalIntegrable hab.le hf) (continuous_intervalIntegrable hab.le hg) hfg

/-- 连续函数黎曼积分的绝对值不超过其绝对值函数的黎曼积分。-/
theorem abs_riemannIntegral_le_riemannIntegral_abs {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b)) :
    |riemannIntegral f a b| ≤ riemannIntegral (fun x => |f x|) a b := by
  rw [riemannIntegral_eq_interval hab hf,
    riemannIntegral_eq_interval hab hf.abs,
    ← intervalIntegral.integral_of_le hab.le, ← intervalIntegral.integral_of_le hab.le]
  exact intervalIntegral.abs_integral_le_integral_abs hab.le

/-- 连续函数的黎曼积分对相邻区间可加。-/
theorem riemannIntegral_add_adjacent {f : ℝ → ℝ} {a b c : ℝ}
    (hab : a < b) (hbc : b < c) (hf : ContinuousOn f (Set.Icc a c)) :
    riemannIntegral f a b + riemannIntegral f b c = riemannIntegral f a c := by
  have hac : a < c := hab.trans hbc
  have hfab : ContinuousOn f (Set.Icc a b) :=
    hf.mono (Set.Icc_subset_Icc_right hbc.le)
  have hfbc : ContinuousOn f (Set.Icc b c) :=
    hf.mono (Set.Icc_subset_Icc_left hab.le)
  rw [riemannIntegral_eq_interval hab hfab, riemannIntegral_eq_interval hbc hfbc,
    riemannIntegral_eq_interval hac hf,
    ← intervalIntegral.integral_of_le hab.le, ← intervalIntegral.integral_of_le hbc.le,
    ← intervalIntegral.integral_of_le hac.le]
  exact intervalIntegral.integral_add_adjacent_intervals
    (continuous_intervalIntegrable hab.le hfab) (continuous_intervalIntegrable hbc.le hfbc)

/-! ## 积分中值定理与周期积分 -/

/-- 第一积分中值定理：连续函数的积分等于某个函数值乘以区间长度。

> **Entry**: real-analysis.riemann.mean-value-/
theorem riemannIntegral_mean_value {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b)) :
    ∃ ξ ∈ Set.Icc a b, riemannIntegral f a b = f ξ * (b - a) := by
  obtain ⟨xm, hxm, hm⟩ :=
    SandronesLibrary.Analysis.Continuity.exists_isLeast_on_Icc hab.le hf
  obtain ⟨xM, hxM, hM⟩ :=
    SandronesLibrary.Analysis.Continuity.exists_isGreatest_on_Icc hab.le hf
  have hlower : f xm * (b - a) ≤ riemannIntegral f a b := by
    rw [← riemannIntegral_const (a := a) (b := b) (c := f xm) hab]
    exact riemannIntegral_mono hab continuousOn_const hf hm
  have hupper : riemannIntegral f a b ≤ f xM * (b - a) := by
    rw [← riemannIntegral_const (a := a) (b := b) (c := f xM) hab]
    exact riemannIntegral_mono hab hf continuousOn_const hM
  let A := riemannIntegral f a b / (b - a)
  have hA_lower : f xm ≤ A := by
    dsimp [A]
    exact (le_div_iff₀ (sub_pos.mpr hab)).mpr hlower
  have hA_upper : A ≤ f xM := by
    dsimp [A]
    exact (div_le_iff₀ (sub_pos.mpr hab)).mpr hupper
  have hxmM : f xm ≤ f xM := hm xM hxM
  have hsub : Set.uIcc xm xM ⊆ Set.Icc a b := Set.uIcc_subset_Icc hxm hxM
  have hA_mem : A ∈ Set.uIcc (f xm) (f xM) := by
    rw [Set.uIcc_of_le hxmM]
    exact ⟨hA_lower, hA_upper⟩
  obtain ⟨ξ, hξ, hξA⟩ := intermediate_value_uIcc (hf.mono hsub) hA_mem
  refine ⟨ξ, hsub hξ, ?_⟩
  rw [hξA]
  dsimp [A]
  rw [div_mul_cancel₀ _ (ne_of_gt (sub_pos.mpr hab))]

/-- 连续周期函数在任意一个完整周期上的黎曼积分与起点无关。-/
theorem riemannIntegral_periodic_one_period {f : ℝ → ℝ} {T : ℝ}
    (hT : 0 < T) (hfcont : Continuous f) (hfper : Function.Periodic f T) (s t : ℝ) :
    riemannIntegral f t (t + T) = riemannIntegral f s (s + T) := by
  rw [riemannIntegral_eq_interval (lt_add_of_pos_right t hT) hfcont.continuousOn,
    riemannIntegral_eq_interval (lt_add_of_pos_right s hT) hfcont.continuousOn,
    ← intervalIntegral.integral_of_le (le_add_of_nonneg_right hT.le),
    ← intervalIntegral.integral_of_le (le_add_of_nonneg_right hT.le)]
  exact hfper.intervalIntegral_add_eq t s

end SandronesLibrary.RealAnalysis.Riemann
