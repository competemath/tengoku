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

/-- 正弦函数是奇函数。
@isnad1 id=eq.0h1v.s3.ca0c19098269 from=translated src=- shape=c7188113 vocab=ce2a453f
-/
theorem sin_neg (x : ℝ) : Real.sin (-x) = -Real.sin x := by
  exact Real.sin_neg x

/-- 余弦函数是偶函数。
@isnad1 id=eq.0h1v.s3.2d2c9be0dd6a from=translated src=- shape=cd419dad vocab=578a4691
-/
theorem cos_neg (x : ℝ) : Real.cos (-x) = Real.cos x := by
  exact Real.cos_neg x

/-- 正弦函数的周期为 `2π`。
> **Entry**: analysis.trigonometric.basic-identities
@isnad1 id=eq.0h1v.s4.9b7a39440229 from=translated src=- shape=783740fd vocab=fc91a797
-/
theorem sin_add_two_pi (x : ℝ) : Real.sin (x + 2 * Real.pi) = Real.sin x := by
  exact Real.sin_add_two_pi x

/-- 余弦函数的周期为 `2π`。
@isnad1 id=eq.0h1v.s4.374c691bb043 from=translated src=- shape=783740fd vocab=cf3f9ca4
-/
theorem cos_add_two_pi (x : ℝ) : Real.cos (x + 2 * Real.pi) = Real.cos x := by
  exact Real.cos_add_two_pi x

/-- 正弦函数的绝对值不超过 `1`。
@isnad1 id=le.0h1v.s4.7c2405578d69 from=translated src=- shape=38becc55 vocab=5e6507b6
-/
theorem sin_bound (x : ℝ) : |Real.sin x| ≤ 1 := by
  exact abs_le.2 ⟨Real.neg_one_le_sin x, Real.sin_le_one x⟩

/-- 余弦函数的绝对值不超过 `1`。
@isnad1 id=le.0h1v.s4.a4d9462e3704 from=translated src=- shape=38becc55 vocab=f7f39727
-/
theorem cos_bound (x : ℝ) : |Real.cos x| ≤ 1 := by
  exact abs_le.2 ⟨Real.neg_one_le_cos x, Real.cos_le_one x⟩

/-! ### 正弦与余弦的和差公式 -/

/-- 正弦和角公式。
@isnad1 id=eq.0h2v.s5.9552ebbf5c1f from=translated src=- shape=2106c094 vocab=0200b25b
-/
theorem sin_add (x y : ℝ) :
    Real.sin (x + y) = Real.sin x * Real.cos y + Real.cos x * Real.sin y := by
  exact Real.sin_add x y

/-- 正弦差角公式。
@isnad1 id=eq.0h2v.s5.2414e139fb92 from=translated src=- shape=2106c094 vocab=826d1cb1
-/
theorem sin_sub (x y : ℝ) :
    Real.sin (x - y) = Real.sin x * Real.cos y - Real.cos x * Real.sin y := by
  exact Real.sin_sub x y

/-- 余弦和角公式。
@isnad1 id=eq.0h2v.s5.05d497b4f9cd from=translated src=- shape=bec385d9 vocab=d14a56b2
-/
theorem cos_add (x y : ℝ) :
    Real.cos (x + y) = Real.cos x * Real.cos y - Real.sin x * Real.sin y := by
  exact Real.cos_add x y

/-- 余弦差角公式。
> **Entry**: analysis.trigonometric.add-sub
@isnad1 id=eq.0h2v.s5.aa264ec51fdc from=translated src=- shape=bec385d9 vocab=d14a56b2
-/
theorem cos_sub (x y : ℝ) :
    Real.cos (x - y) = Real.cos x * Real.cos y + Real.sin x * Real.sin y := by
  exact Real.cos_sub x y

/-! ### 倍角、降幂与平方恒等式 -/

/-- 正弦倍角公式。
@isnad1 id=eq.0h1v.s5.91edcefdfa51 from=translated src=- shape=1ddba068 vocab=56d84344
-/
theorem sin_two_mul (x : ℝ) :
    Real.sin (2 * x) = 2 * Real.sin x * Real.cos x := by
  exact Real.sin_two_mul x

/-- 余弦倍角公式。
@isnad1 id=eq.0h1v.s6.13ef19dcffea from=translated src=- shape=664d66b6 vocab=af78b8ab
-/
theorem cos_two_mul (x : ℝ) :
    Real.cos (2 * x) = 2 * Real.cos x ^ 2 - 1 := by
  exact Real.cos_two_mul x

/-- 正弦降幂公式。
@isnad1 id=eq.0h1v.s6.80a2397950b6 from=translated src=- shape=5f1ef3af vocab=200b6f86
-/
theorem sin_sq_eq_half_sub (x : ℝ) :
    Real.sin x ^ 2 = 1 / 2 - Real.cos (2 * x) / 2 := by
  exact Real.sin_sq_eq_half_sub x

/-- 余弦降幂公式。
@isnad1 id=eq.0h1v.s6.89579ec3060b from=translated src=- shape=3826f904 vocab=8992cfa2
-/
theorem cos_sq (x : ℝ) :
    Real.cos x ^ 2 = 1 / 2 + Real.cos (2 * x) / 2 := by
  exact Real.cos_sq x

/-- 正弦余弦平方和恒等式。
> **Entry**: analysis.trigonometric.double-half
@isnad1 id=eq.0h1v.s5.a76798981816 from=translated src=- shape=e936802f vocab=99327791
-/
theorem sin_sq_add_cos_sq (x : ℝ) :
    Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := by
  exact Real.sin_sq_add_cos_sq x

/-! ### 积化和差公式 -/

/-- 正弦乘正弦的积化和差公式。
@isnad1 id=eq.0h2v.s5.617f171bbcd4 from=translated src=- shape=ec2cf945 vocab=9e0cc594
-/
theorem sin_mul_sin (x y : ℝ) :
    Real.sin x * Real.sin y =
      (Real.cos (x - y) - Real.cos (x + y)) / 2 := by
  rw [Real.cos_sub, Real.cos_add]
  ring

/-- 余弦乘余弦的积化和差公式。
@isnad1 id=eq.0h2v.s5.6581748bb0e6 from=translated src=- shape=d8b5ac74 vocab=016fe65a
-/
theorem cos_mul_cos (x y : ℝ) :
    Real.cos x * Real.cos y =
      (Real.cos (x - y) + Real.cos (x + y)) / 2 := by
  rw [Real.cos_sub, Real.cos_add]
  ring

/-- 正弦乘余弦的积化和差公式。
> **Entry**: analysis.trigonometric.product-sum
@isnad1 id=eq.0h2v.s5.66266a2d9470 from=translated src=- shape=1c2c2d69 vocab=9e0cc594
-/
theorem sin_mul_cos (x y : ℝ) :
    Real.sin x * Real.cos y =
      (Real.sin (x + y) + Real.sin (x - y)) / 2 := by
  rw [Real.sin_add, Real.sin_sub]
  ring

/-! ### 和差化积公式 -/

/-- 正弦和化积公式。
@isnad1 id=eq.0h2v.s6.096aa841fbd1 from=translated src=- shape=5f754f50 vocab=9e0cc594
-/
theorem sin_add_sin (x y : ℝ) :
    Real.sin x + Real.sin y =
      2 * Real.sin ((x + y) / 2) * Real.cos ((x - y) / 2) := by
  let u : ℝ := (x + y) / 2
  let v : ℝ := (x - y) / 2
  have hux : u + v = x := by dsimp [u, v]; ring
  have huy : u - v = y := by dsimp [u, v]; ring
  rw [← hux, ← huy, Real.sin_add, Real.sin_sub]
  ring

/-- 正弦差化积公式。
@isnad1 id=eq.0h2v.s6.c4f4ca7fab99 from=translated src=- shape=3a7e3af7 vocab=9e0cc594
-/
theorem sin_sub_sin (x y : ℝ) :
    Real.sin x - Real.sin y =
      2 * Real.cos ((x + y) / 2) * Real.sin ((x - y) / 2) := by
  let u : ℝ := (x + y) / 2
  let v : ℝ := (x - y) / 2
  have hux : u + v = x := by dsimp [u, v]; ring
  have huy : u - v = y := by dsimp [u, v]; ring
  rw [← hux, ← huy, Real.sin_add, Real.sin_sub]
  ring

/-- 余弦和化积公式。
@isnad1 id=eq.0h2v.s6.2c9d80a1909c from=translated src=- shape=b8795d5a vocab=016fe65a
-/
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
> **Entry**: analysis.trigonometric.sum-product
@isnad1 id=eq.0h2v.s6.f68e0de5dc44 from=translated src=- shape=5e087c57 vocab=bfad0e00
-/
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

/-- `π/6` 的正弦值。
@isnad1 id=eq.0h0v.s5.ef063516e75a from=translated src=- shape=598af2eb vocab=74a5bcd6
-/
theorem sin_pi_div_six : Real.sin (Real.pi / 6) = 1 / 2 := by
  exact Real.sin_pi_div_six

/-- `π/6` 的余弦值。
@isnad1 id=eq.0h0v.s5.56b42c4610ec from=translated src=- shape=456a662f vocab=bafbb882
-/
theorem cos_pi_div_six : Real.cos (Real.pi / 6) = √3 / 2 := by
  exact Real.cos_pi_div_six

/-- `π/6` 的正切值。
@isnad1 id=eq.0h0v.s5.add94c49cabf from=translated src=- shape=f233268a vocab=b883a094
-/
theorem tan_pi_div_six : Real.tan (Real.pi / 6) = 1 / √3 := by
  exact Real.tan_pi_div_six

/-- `π/4` 的正弦值。
@isnad1 id=eq.0h0v.s5.4fa109a15071 from=translated src=- shape=456a662f vocab=2e73f9e5
-/
theorem sin_pi_div_four : Real.sin (Real.pi / 4) = √2 / 2 := by
  exact Real.sin_pi_div_four

/-- `π/4` 的余弦值。
@isnad1 id=eq.0h0v.s5.e9eec4cedcc6 from=translated src=- shape=456a662f vocab=bafbb882
-/
theorem cos_pi_div_four : Real.cos (Real.pi / 4) = √2 / 2 := by
  exact Real.cos_pi_div_four

/-- `π/4` 的正切值。
@isnad1 id=eq.0h0v.s4.181430c9de21 from=translated src=- shape=15fd1593 vocab=0b4dc4d3
-/
theorem tan_pi_div_four : Real.tan (Real.pi / 4) = 1 := by
  exact Real.tan_pi_div_four

/-- `π/3` 的正弦值。
@isnad1 id=eq.0h0v.s5.0135a7e49632 from=translated src=- shape=456a662f vocab=2e73f9e5
-/
theorem sin_pi_div_three : Real.sin (Real.pi / 3) = √3 / 2 := by
  exact Real.sin_pi_div_three

/-- `π/3` 的余弦值。
@isnad1 id=eq.0h0v.s5.ee61a3add6d6 from=translated src=- shape=598af2eb vocab=5d5e6df5
-/
theorem cos_pi_div_three : Real.cos (Real.pi / 3) = 1 / 2 := by
  exact Real.cos_pi_div_three

/-- `π/3` 的正切值。
> **Entry**: analysis.trigonometric.special-angles
@isnad1 id=eq.0h0v.s4.b12e9cb72ded from=translated src=- shape=68c60b0d vocab=b883a094
-/
theorem tan_pi_div_three : Real.tan (Real.pi / 3) = √3 := by
  exact Real.tan_pi_div_three

/-! ### 正切的和差与倍角公式 -/

/-- 正切和角公式；假设两角同时避开正切的极点，或两角同时为极点。
@isnad1 id=eq.1h2v.s8.774d9214d846 from=translated src=- shape=8376e49d vocab=eac43850
-/
theorem tan_add {x y : ℝ} (h :
    ((∀ k : ℤ, x ≠ (2 * (k : ℝ) + 1) * Real.pi / 2) ∧
      ∀ l : ℤ, y ≠ (2 * (l : ℝ) + 1) * Real.pi / 2) ∨
      ((∃ k : ℤ, x = (2 * (k : ℝ) + 1) * Real.pi / 2) ∧
        ∃ l : ℤ, y = (2 * (l : ℝ) + 1) * Real.pi / 2)) :
    Real.tan (x + y) = (Real.tan x + Real.tan y) /
      (1 - Real.tan x * Real.tan y) := by
  exact Real.tan_add h

/-- 正切差角公式；极点条件与正切和角公式相同。
@isnad1 id=eq.1h2v.s8.a0a7d2e06c13 from=translated src=- shape=dda941d9 vocab=eac43850
-/
theorem tan_sub {x y : ℝ} (h :
    ((∀ k : ℤ, x ≠ (2 * (k : ℝ) + 1) * Real.pi / 2) ∧
      ∀ l : ℤ, y ≠ (2 * (l : ℝ) + 1) * Real.pi / 2) ∨
      ((∃ k : ℤ, x = (2 * (k : ℝ) + 1) * Real.pi / 2) ∧
        ∃ l : ℤ, y = (2 * (l : ℝ) + 1) * Real.pi / 2)) :
    Real.tan (x - y) = (Real.tan x - Real.tan y) /
      (1 + Real.tan x * Real.tan y) := by
  exact Real.tan_sub h

/-- 正切倍角公式。
> **Entry**: analysis.trigonometric.tan-identities
@isnad1 id=eq.0h1v.s6.07d2c68106c9 from=translated src=- shape=0a9b1fd2 vocab=e14f78bd
-/
theorem tan_two_mul (x : ℝ) :
    Real.tan (2 * x) = 2 * Real.tan x / (1 - Real.tan x ^ 2) := by
  exact Real.tan_two_mul

/-! ### 半角平方根公式 -/

/-- 正弦半角平方根的绝对值公式。
@isnad1 id=eq.0h1v.s5.b14af587e4dc from=translated src=- shape=be0f8a0d vocab=9fb72a47
-/
theorem abs_sin_half (x : ℝ) :
    |Real.sin (x / 2)| = Real.sqrt ((1 - Real.cos x) / 2) := by
  exact Real.abs_sin_half x

/-- 余弦半角平方根公式。
@isnad1 id=eq.0h1v.s5.76d35d70b3f0 from=translated src=- shape=64eea03a vocab=e888f3cc
-/
theorem abs_cos_half (x : ℝ) :
    |Real.cos (x / 2)| = Real.sqrt ((1 + Real.cos x) / 2) := by
  have h := Real.cos_sq (x / 2)
  rw [show 2 * (x / 2) = x by ring] at h
  rw [← Real.sqrt_sq_eq_abs]
  convert congrArg Real.sqrt h using 1 <;> ring

/-- 在 `0 ≤ x ≤ π` 上，正弦半角平方根公式可以去掉绝对值。
@isnad1 id=eq.2h1v.s6.6cb46e22a970 from=translated src=- shape=b62a9fb9 vocab=c3be1356
-/
theorem sin_half_root {x : ℝ} (hx₀ : 0 ≤ x) (hxπ : x ≤ Real.pi) :
    Real.sin (x / 2) = Real.sqrt ((1 - Real.cos x) / 2) := by
  have h := Real.abs_sin_half x
  rw [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith))] at h
  exact h

/-- 在 `-π ≤ x ≤ π` 上，余弦半角平方根公式可以去掉绝对值。
> **Entry**: analysis.trigonometric.half-root
@isnad1 id=eq.2h1v.s6.a134333ae419 from=translated src=- shape=4ee0729c vocab=fedb99ea
-/
theorem cos_half_root {x : ℝ} (hnegπ : -Real.pi ≤ x) (hxπ : x ≤ Real.pi) :
    Real.cos (x / 2) = Real.sqrt ((1 + Real.cos x) / 2) := by
  have h := abs_cos_half x
  rw [abs_of_nonneg] at h
  · exact h
  · apply Real.cos_nonneg_of_mem_Icc
    constructor <;> linarith

end Analysis.Trigonometric
end SandronesLibrary
