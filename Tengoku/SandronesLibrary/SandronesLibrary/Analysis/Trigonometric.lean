/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Analysis / Trigonometric —— 高中教材层三角函数基本性质

本模块先整理三角函数的奇偶性、`2π` 周期性和基本有界性。
和差、倍角、积化和差等恒等式在后续批次中继续纳入。
-/

namespace SandronesLibrary
namespace Analysis.Trigonometric

/-- 正弦函数是奇函数。-/
theorem sin_neg (x : ℝ) : Real.sin (-x) = -Real.sin x := by
  exact Real.sin_neg x

/-- 余弦函数是偶函数。-/
theorem cos_neg (x : ℝ) : Real.cos (-x) = Real.cos x := by
  exact Real.cos_neg x

/-- 正弦函数的周期为 `2π`。
> **Entry**: analysis.trigonometric.basic-identities-/
theorem sin_add_two_pi (x : ℝ) : Real.sin (x + 2 * Real.pi) = Real.sin x := by
  exact Real.sin_add_two_pi x

/-- 余弦函数的周期为 `2π`。-/
theorem cos_add_two_pi (x : ℝ) : Real.cos (x + 2 * Real.pi) = Real.cos x := by
  exact Real.cos_add_two_pi x

/-- 正弦函数的绝对值不超过 `1`。-/
theorem sin_bound (x : ℝ) : |Real.sin x| ≤ 1 := by
  exact abs_le.2 ⟨Real.neg_one_le_sin x, Real.sin_le_one x⟩

/-- 余弦函数的绝对值不超过 `1`。-/
theorem cos_bound (x : ℝ) : |Real.cos x| ≤ 1 := by
  exact abs_le.2 ⟨Real.neg_one_le_cos x, Real.cos_le_one x⟩

/-! ### 正弦与余弦的和差公式 -/

/-- 正弦和角公式。-/
theorem sin_add (x y : ℝ) :
    Real.sin (x + y) = Real.sin x * Real.cos y + Real.cos x * Real.sin y := by
  exact Real.sin_add x y

/-- 正弦差角公式。-/
theorem sin_sub (x y : ℝ) :
    Real.sin (x - y) = Real.sin x * Real.cos y - Real.cos x * Real.sin y := by
  exact Real.sin_sub x y

/-- 余弦和角公式。-/
theorem cos_add (x y : ℝ) :
    Real.cos (x + y) = Real.cos x * Real.cos y - Real.sin x * Real.sin y := by
  exact Real.cos_add x y

/-- 余弦差角公式。
> **Entry**: analysis.trigonometric.add-sub-/
theorem cos_sub (x y : ℝ) :
    Real.cos (x - y) = Real.cos x * Real.cos y + Real.sin x * Real.sin y := by
  exact Real.cos_sub x y

/-! ### 倍角、降幂与平方恒等式 -/

/-- 正弦倍角公式。-/
theorem sin_two_mul (x : ℝ) :
    Real.sin (2 * x) = 2 * Real.sin x * Real.cos x := by
  exact Real.sin_two_mul x

/-- 余弦倍角公式。-/
theorem cos_two_mul (x : ℝ) :
    Real.cos (2 * x) = 2 * Real.cos x ^ 2 - 1 := by
  exact Real.cos_two_mul x

/-- 正弦降幂公式。-/
theorem sin_sq_eq_half_sub (x : ℝ) :
    Real.sin x ^ 2 = 1 / 2 - Real.cos (2 * x) / 2 := by
  exact Real.sin_sq_eq_half_sub x

/-- 余弦降幂公式。-/
theorem cos_sq (x : ℝ) :
    Real.cos x ^ 2 = 1 / 2 + Real.cos (2 * x) / 2 := by
  exact Real.cos_sq x

/-- 正弦余弦平方和恒等式。
> **Entry**: analysis.trigonometric.double-half-/
theorem sin_sq_add_cos_sq (x : ℝ) :
    Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := by
  exact Real.sin_sq_add_cos_sq x

/-! ### 积化和差公式 -/

/-- 正弦乘正弦的积化和差公式。-/
theorem sin_mul_sin (x y : ℝ) :
    Real.sin x * Real.sin y =
      (Real.cos (x - y) - Real.cos (x + y)) / 2 := by
  rw [Real.cos_sub, Real.cos_add]
  ring

/-- 余弦乘余弦的积化和差公式。-/
theorem cos_mul_cos (x y : ℝ) :
    Real.cos x * Real.cos y =
      (Real.cos (x - y) + Real.cos (x + y)) / 2 := by
  rw [Real.cos_sub, Real.cos_add]
  ring

/-- 正弦乘余弦的积化和差公式。
> **Entry**: analysis.trigonometric.product-sum-/
theorem sin_mul_cos (x y : ℝ) :
    Real.sin x * Real.cos y =
      (Real.sin (x + y) + Real.sin (x - y)) / 2 := by
  rw [Real.sin_add, Real.sin_sub]
  ring

/-! ### 和差化积公式 -/

/-- 正弦和化积公式。-/
theorem sin_add_sin (x y : ℝ) :
    Real.sin x + Real.sin y =
      2 * Real.sin ((x + y) / 2) * Real.cos ((x - y) / 2) := by
  let u : ℝ := (x + y) / 2
  let v : ℝ := (x - y) / 2
  have hux : u + v = x := by dsimp [u, v]; ring
  have huy : u - v = y := by dsimp [u, v]; ring
  rw [← hux, ← huy, Real.sin_add, Real.sin_sub]
  ring

/-- 正弦差化积公式。-/
theorem sin_sub_sin (x y : ℝ) :
    Real.sin x - Real.sin y =
      2 * Real.cos ((x + y) / 2) * Real.sin ((x - y) / 2) := by
  let u : ℝ := (x + y) / 2
  let v : ℝ := (x - y) / 2
  have hux : u + v = x := by dsimp [u, v]; ring
  have huy : u - v = y := by dsimp [u, v]; ring
  rw [← hux, ← huy, Real.sin_add, Real.sin_sub]
  ring

/-- 余弦和化积公式。-/
theorem cos_add_cos (x y : ℝ) :
    Real.cos x + Real.cos y =
      2 * Real.cos ((x + y) / 2) * Real.cos ((x - y) / 2) := by
  let u : ℝ := (x + y) / 2
  let v : ℝ := (x - y) / 2
  have hux : u + v = x := by dsimp [u, v]; ring
  have huy : u - v = y := by dsimp [u, v]; ring
  rw [← hux, ← huy, Real.cos_add, Real.cos_sub]
  ring

/-- 余弦差化积公式。
> **Entry**: analysis.trigonometric.sum-product-/
theorem cos_sub_cos (x y : ℝ) :
    Real.cos x - Real.cos y =
      -2 * Real.sin ((x + y) / 2) * Real.sin ((x - y) / 2) := by
  let u : ℝ := (x + y) / 2
  let v : ℝ := (x - y) / 2
  have hux : u + v = x := by dsimp [u, v]; ring
  have huy : u - v = y := by dsimp [u, v]; ring
  rw [← hux, ← huy, Real.cos_add, Real.cos_sub]
  ring

/-! ### 高中常用特殊角 -/

/-- `π/6` 的正弦值。-/
theorem sin_pi_div_six : Real.sin (Real.pi / 6) = 1 / 2 := by
  exact Real.sin_pi_div_six

/-- `π/6` 的余弦值。-/
theorem cos_pi_div_six : Real.cos (Real.pi / 6) = √3 / 2 := by
  exact Real.cos_pi_div_six

/-- `π/6` 的正切值。-/
theorem tan_pi_div_six : Real.tan (Real.pi / 6) = 1 / √3 := by
  exact Real.tan_pi_div_six

/-- `π/4` 的正弦值。-/
theorem sin_pi_div_four : Real.sin (Real.pi / 4) = √2 / 2 := by
  exact Real.sin_pi_div_four

/-- `π/4` 的余弦值。-/
theorem cos_pi_div_four : Real.cos (Real.pi / 4) = √2 / 2 := by
  exact Real.cos_pi_div_four

/-- `π/4` 的正切值。-/
theorem tan_pi_div_four : Real.tan (Real.pi / 4) = 1 := by
  exact Real.tan_pi_div_four

/-- `π/3` 的正弦值。-/
theorem sin_pi_div_three : Real.sin (Real.pi / 3) = √3 / 2 := by
  exact Real.sin_pi_div_three

/-- `π/3` 的余弦值。-/
theorem cos_pi_div_three : Real.cos (Real.pi / 3) = 1 / 2 := by
  exact Real.cos_pi_div_three

/-- `π/3` 的正切值。
> **Entry**: analysis.trigonometric.special-angles-/
theorem tan_pi_div_three : Real.tan (Real.pi / 3) = √3 := by
  exact Real.tan_pi_div_three

/-! ### 正切的和差与倍角公式 -/

/-- 正切和角公式；假设两角同时避开正切的极点，或两角同时为极点。-/
theorem tan_add {x y : ℝ} (h :
    ((∀ k : ℤ, x ≠ (2 * (k : ℝ) + 1) * Real.pi / 2) ∧
      ∀ l : ℤ, y ≠ (2 * (l : ℝ) + 1) * Real.pi / 2) ∨
      ((∃ k : ℤ, x = (2 * (k : ℝ) + 1) * Real.pi / 2) ∧
        ∃ l : ℤ, y = (2 * (l : ℝ) + 1) * Real.pi / 2)) :
    Real.tan (x + y) = (Real.tan x + Real.tan y) /
      (1 - Real.tan x * Real.tan y) := by
  exact Real.tan_add h

/-- 正切差角公式；极点条件与正切和角公式相同。-/
theorem tan_sub {x y : ℝ} (h :
    ((∀ k : ℤ, x ≠ (2 * (k : ℝ) + 1) * Real.pi / 2) ∧
      ∀ l : ℤ, y ≠ (2 * (l : ℝ) + 1) * Real.pi / 2) ∨
      ((∃ k : ℤ, x = (2 * (k : ℝ) + 1) * Real.pi / 2) ∧
        ∃ l : ℤ, y = (2 * (l : ℝ) + 1) * Real.pi / 2)) :
    Real.tan (x - y) = (Real.tan x - Real.tan y) /
      (1 + Real.tan x * Real.tan y) := by
  exact Real.tan_sub h

/-- 正切倍角公式。
> **Entry**: analysis.trigonometric.tan-identities-/
theorem tan_two_mul (x : ℝ) :
    Real.tan (2 * x) = 2 * Real.tan x / (1 - Real.tan x ^ 2) := by
  exact Real.tan_two_mul

/-! ### 半角平方根公式 -/

/-- 正弦半角平方根的绝对值公式。-/
theorem abs_sin_half (x : ℝ) :
    |Real.sin (x / 2)| = Real.sqrt ((1 - Real.cos x) / 2) := by
  exact Real.abs_sin_half x

/-- 余弦半角平方根公式。-/
theorem abs_cos_half (x : ℝ) :
    |Real.cos (x / 2)| = Real.sqrt ((1 + Real.cos x) / 2) := by
  have h := Real.cos_sq (x / 2)
  rw [show 2 * (x / 2) = x by ring] at h
  rw [← Real.sqrt_sq_eq_abs]
  convert congrArg Real.sqrt h using 1 <;> ring

/-- 在 `0 ≤ x ≤ π` 上，正弦半角平方根公式可以去掉绝对值。-/
theorem sin_half_root {x : ℝ} (hx₀ : 0 ≤ x) (hxπ : x ≤ Real.pi) :
    Real.sin (x / 2) = Real.sqrt ((1 - Real.cos x) / 2) := by
  have h := Real.abs_sin_half x
  rw [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith))] at h
  exact h

/-- 在 `-π ≤ x ≤ π` 上，余弦半角平方根公式可以去掉绝对值。
> **Entry**: analysis.trigonometric.half-root-/
theorem cos_half_root {x : ℝ} (hnegπ : -Real.pi ≤ x) (hxπ : x ≤ Real.pi) :
    Real.cos (x / 2) = Real.sqrt ((1 + Real.cos x) / 2) := by
  have h := abs_cos_half x
  rw [abs_of_nonneg] at h
  · exact h
  · apply Real.cos_nonneg_of_mem_Icc
    constructor <;> linarith

end Analysis.Trigonometric
end SandronesLibrary
