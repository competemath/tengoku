/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.ComplexAnalysis.Residue
import Tengoku.Seed.Analysis.Calculus.LogDeriv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 辐角积分与 Rouché 比较的线性特例

Mathlib 目前没有一般复路径绕数、辐角原理或 Rouché 定理。本文件只形式化线性
情形：`z-c` 的对数导数圆周积分计数为 `1`，以及常数扰动下的边界不等式和唯一零点。
-/

namespace SandronesLibrary.ComplexAnalysis

open Metric

/-- 对数导数在指定圆周上的正规化积分。

> **Entry**: complex-analysis.argument-principle.linear-special-case-/
noncomputable def circleArgumentIntegral (f : ℂ → ℂ) (c : ℂ) (R : ℝ) : ℂ :=
  (2 * Real.pi * Complex.I)⁻¹ * (∮ z in C(c, R), logDeriv f z)

/-- 线性函数 `z-c` 的对数导数是 `(z-c)⁻¹`。

> **Entry**: complex-analysis.argument-principle.linear-special-case
@isnad1 id=eq.0h2v.s5.a7a84bff5a4d from=translated src=- shape=515ce273 vocab=fcfbc9ae
-/
theorem logDeriv_sub_const (c z : ℂ) :
    logDeriv (fun w : ℂ => w - c) z = (z - c)⁻¹ := by
  simp [logDeriv]

/-- 辐角原理的线性特例：`z-c` 沿以 `c` 为中心的非退化正向圆周计数为 `1`。

> **Entry**: complex-analysis.argument-principle.linear-special-case
@isnad1 id=eq.1h2v.s5.606125ae6876 from=translated src=- shape=d5e76011 vocab=ad38da13
-/
theorem argumentPrinciple_linear (c : ℂ) {R : ℝ} (hR : R ≠ 0) :
    circleArgumentIntegral (fun z => z - c) c R = 1 := by
  rw [circleArgumentIntegral]
  simp_rw [logDeriv_sub_const]
  rw [circleIntegral.integral_sub_center_inv c hR]
  field_simp

/-- Rouché 的线性常数扰动特例：若 `‖b‖<R`，则边界上 `b` 严格小于 `z-c`，
而 `(z-c)+b` 在圆内恰有零点 `c-b`。

> **Entry**: complex-analysis.argument-principle.linear-special-case
@isnad1 id=and.1h3v.s6.238c874b47fa from=translated src=- shape=d2e3dd32 vocab=64fe3d1d
-/
theorem rouche_linear_constant {c b : ℂ} {R : ℝ} (hb : ‖b‖ < R) :
    (∀ z ∈ sphere c R, ‖b‖ < ‖z - c‖) ∧
      (c - b ∈ ball c R) ∧
      (∀ z : ℂ, (z - c) + b = 0 ↔ z = c - b) := by
  constructor
  · intro z hz
    simpa [mem_sphere_iff_norm.mp hz] using hb
  constructor
  · simpa [mem_ball, dist_eq_norm, norm_neg] using hb
  · intro z
    constructor <;> intro h
    · linear_combination h
    · rw [h]
      ring

end SandronesLibrary.ComplexAnalysis
