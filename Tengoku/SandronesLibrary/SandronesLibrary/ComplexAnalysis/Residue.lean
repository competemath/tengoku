/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.ComplexAnalysis.CauchyFormula
import Tengoku.Seed.Analysis.SpecialFunctions.ImproperIntegrals

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 圆周残数基础接口

Mathlib 目前没有一般 Laurent 系数意义的复残数 API。本文件只定义指定圆周上的
正规化积分，并证明单极点 `g(z)/(z-a)` 和 Cauchy 核的公式。这些是 foundation 或
special-case 结果，不声称已实现一般残数定理。
-/

namespace SandronesLibrary.ComplexAnalysis

open Metric

/-- `f` 关于以 `a` 为圆心、`R` 为半径的正向圆周之正规化积分。

> **Entry**: complex-analysis.residue.circle-foundation-/
noncomputable def circleResidue (f : ℂ → ℂ) (a : ℂ) (R : ℝ) : ℂ :=
  (2 * Real.pi * Complex.I)⁻¹ * (∮ z in C(a, R), f z)

/-- `circleResidue` 的定义展开。

> **Entry**: complex-analysis.residue.circle-foundation
@isnad1 id=eq.0h3v.s6.09e1eb434843 from=translated src=- shape=1ba51e73 vocab=be35d49c
-/
theorem circleResidue_eq_normalized_circleIntegral (f : ℂ → ℂ) (a : ℂ) (R : ℝ) :
    circleResidue f a R = (2 * Real.pi * Complex.I)⁻¹ * (∮ z in C(a, R), f z) := rfl

/-- 单极点特例：若 `g` 在闭圆盘附近全纯，则 `g(z)/(z-a)` 的圆周残数是 `g(a)`。

> **Entry**: complex-analysis.residue.simple-pole
@isnad1 id=eq.2h3v.s6.a686377f4572 from=translated src=- shape=41625ab2 vocab=cd9e258b
-/
theorem circleResidue_div_sub {g : ℂ → ℂ} {a : ℂ} {R : ℝ}
    (hg : HolomorphicOnTextbook g (closedBall a R)) (hR : 0 < R) :
    circleResidue (fun z => g z / (z - a)) a R = g a := by
  rw [circleResidue, cauchy_integral_formula hg (mem_ball_self hR)]
  field_simp

/-- 圆周积分与它的正规化圆周残数之间的恒等式。

> **Entry**: complex-analysis.residue.circle-foundation
@isnad1 id=eq.0h3v.s6.e4655036ee66 from=translated src=- shape=9e4a464e vocab=ac87647f
-/
theorem circleIntegral_eq_two_pi_I_mul_circleResidue (f : ℂ → ℂ) (a : ℂ) {R : ℝ} :
    (∮ z in C(a, R), f z) = 2 * Real.pi * Complex.I * circleResidue f a R := by
  rw [circleResidue]
  field_simp

/-- Cauchy 核 `(z-a)⁻¹` 关于任意非退化中心圆的圆周残数为 `1`。

> **Entry**: complex-analysis.residue.simple-pole
@isnad1 id=eq.1h2v.s5.63bd86f432df from=translated src=- shape=0f20c72f vocab=75d2cc2b
-/
theorem circleResidue_sub_center_inv (a : ℂ) {R : ℝ} (hR : R ≠ 0) :
    circleResidue (fun z => (z - a)⁻¹) a R = 1 := by
  rw [circleResidue, circleIntegral.integral_sub_center_inv a hR]
  field_simp

/-- 实积分例题：`∫_ℝ 1/(1+x²) dx = π`。这里准确复用 Mathlib 的广义积分后端，
不将它伪称为一般残数计算定理。

> **Entry**: complex-analysis.residue.real-integral-example
@isnad1 id=eq.0h0v.s5.2ded07e6f049 from=translated src=- shape=17ff72c3 vocab=9863e834
-/
theorem real_integral_inv_one_add_sq :
    (∫ x : ℝ, (1 + x ^ 2)⁻¹) = Real.pi := by
  exact integral_univ_inv_one_add_sq

end SandronesLibrary.ComplexAnalysis
