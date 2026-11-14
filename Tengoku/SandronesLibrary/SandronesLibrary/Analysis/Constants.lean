/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku
import Tengoku.Seed.Analysis.Real.Pi.Irrational

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Analysis / Constants —— 重要数学常数

本模块整理自然常数 `e`、圆周率 `π` 以及常见无理数的教材层接口。除了基本
数值性质，还给出两个常数的无理性：`e` 使用指数级数的阶乘尾项估计，`π`
则转接 Mathlib 中已形式化的 Cartwright 积分证明。
-/

namespace SandronesLibrary
namespace Analysis.Constants

/-- 自然常数 `e` 的定义：指数函数在 `1` 点的值。-/
noncomputable def e : ℝ := Real.exp 1

/-- `e` 展开为指数函数在 `1` 点的值。
> **Entry**: analysis.constants.e-definition-/
theorem e_eq_exp_one : e = Real.exp 1 := by
  rfl

/-- 自然常数 `e` 为正。-/
theorem e_pos : 0 < e := by
  rw [e_eq_exp_one]
  exact Real.exp_pos 1

/-- 自然常数 `e` 严格大于 `2`。-/
theorem e_gt_two : 2 < e := by
  rw [e_eq_exp_one]
  exact Real.exp_one_gt_two

/-- 自然常数 `e` 严格小于 `3`。-/
theorem e_lt_three : e < 3 := by
  rw [e_eq_exp_one]
  exact Real.exp_one_lt_three

/-- 自然对数在 `e` 点的值为 `1`。-/
theorem log_e : Real.log e = 1 := by
  rw [e_eq_exp_one]
  exact Real.log_exp 1

/-! ### 自然常数 `e` 的无理性 -/

/-- 把指数级数截断到第 `n` 项并乘以 `n!`，所得数是整数。

对每个 `k ≤ n`，`k! ∣ n!`，所以 `n!/k!` 是自然数。这个引理负责经典证明中
“有限和部分乘以公分母后为整数”的算术步骤。-/
private lemma factorial_mul_partial_sum_is_int (n : ℕ) :
    ∃ z : ℤ, (n.factorial : ℝ) *
      (∑ k ∈ Finset.range (n + 1), (1 : ℝ) / k.factorial) = z := by
  refine ⟨∑ k ∈ Finset.range (n + 1), ((n.factorial / k.factorial : ℕ) : ℤ), ?_⟩
  rw [Finset.mul_sum]
  simp only [Int.cast_sum, Int.cast_natCast]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hdvd : k.factorial ∣ n.factorial := Nat.factorial_dvd_factorial hkn
  rw [Nat.cast_div hdvd (by positivity)]
  field_simp

/-- 若 `q` 是有理数，则以其分母 `q.den` 的阶乘相乘后得到整数。

约分后的分母本身整除其阶乘；这个表述恰好与无理性定义中出现的任意有理数
代表元对接。-/
private lemma factorial_mul_rational_is_int (q : ℚ) :
    ∃ z : ℤ, (q.den.factorial : ℝ) * (q : ℝ) = z := by
  obtain ⟨c, hc⟩ := Nat.dvd_factorial q.pos (le_refl q.den)
  refine ⟨q.num * c, ?_⟩
  rw [Rat.cast_def, Int.cast_mul, Int.cast_natCast]
  rw [hc]
  field_simp
  push_cast
  ring

/-- 指数级数的任意有限截断都严格小于 `exp 1`。

先补上严格为正的下一项，再用指数级数有限和不超过指数函数的标准估计。-/
private lemma exp_one_partial_sum_lt (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), (1 : ℝ) / k.factorial) < Real.exp 1 := by
  calc
    (∑ k ∈ Finset.range (n + 1), (1 : ℝ) / k.factorial) <
        (∑ k ∈ Finset.range (n + 1), (1 : ℝ) / k.factorial) +
          1 / ↑(n + 1).factorial :=
      lt_add_of_pos_right _ (by positivity)
    _ = ∑ k ∈ Finset.range (n + 2), (1 : ℝ) / k.factorial := by
      simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (Finset.sum_range_succ (f := fun k => (1 : ℝ) / k.factorial) (n + 1)).symm
    _ ≤ Real.exp 1 := by
      simpa using Real.sum_le_exp_of_nonneg (x := (1 : ℝ)) zero_le_one (n + 2)

/-- 当 `n > 0` 时，指数级数尾项乘以 `n!` 后严格小于 `1`。

在 `Real.exp_bound` 中取截断长度 `n+1`，再利用 `(n+1)!=(n+1)n!`，便把
上界化为 `(n+2)/(n+1)² < 1`。-/
private lemma factorial_mul_exp_one_sub_partial_sum_lt_one (n : ℕ) (hn : 0 < n) :
    (n.factorial : ℝ) *
      (Real.exp 1 - ∑ k ∈ Finset.range (n + 1), (1 : ℝ) / k.factorial) < 1 := by
  have hb := Real.exp_bound (x := (1 : ℝ)) (n := n + 1) (by simp) (by omega)
  have hnonneg : 0 ≤ Real.exp 1 -
      ∑ k ∈ Finset.range (n + 1), (1 : ℝ) / k.factorial := by
    apply sub_nonneg.mpr
    simpa only [one_pow] using
      Real.sum_le_exp_of_nonneg (x := (1 : ℝ)) zero_le_one (n + 1)
  have hb' : Real.exp 1 - ∑ k ∈ Finset.range (n + 1), (1 : ℝ) / k.factorial ≤
      (n + 1).succ / (((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ)) := by
    simpa only [one_pow, abs_one, one_mul, abs_of_nonneg hnonneg] using hb
  have hfac : (0 : ℝ) < n.factorial := by positivity
  calc
    (n.factorial : ℝ) *
        (Real.exp 1 - ∑ k ∈ Finset.range (n + 1), (1 : ℝ) / k.factorial)
        ≤ (n.factorial : ℝ) *
          ((n + 1).succ / (((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ))) :=
      mul_le_mul_of_nonneg_left hb' hfac.le
    _ < 1 := by
      have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
      rw [Nat.factorial_succ]
      push_cast
      field_simp
      nlinarith

/-- 自然常数 `e = exp 1` 是无理数。

若 `e=q∈ℚ`，取 `n=q.den`。上面的两个整数性引理说明
`n!e-n!∑ₖ₌₀ⁿ1/k!` 是整数；两个尾项引理却说明它严格位于 `0` 与 `1`
之间，矛盾。
> **Entry**: analysis.constants.e-irrational-/
theorem e_irrational : Irrational e := by
  rw [e_eq_exp_one]
  rintro ⟨q, hq⟩
  let n := q.den
  have hn : 0 < n := q.pos
  obtain ⟨u, hu⟩ := factorial_mul_rational_is_int q
  obtain ⟨v, hv⟩ := factorial_mul_partial_sum_is_int n
  have hq' : (q : ℝ) = Real.exp 1 := hq
  have hpos : (0 : ℝ) < (u - v : ℤ) := by
    rw [Int.cast_sub, ← hu, ← hv, hq']
    rw [← mul_sub]
    exact mul_pos (by positivity) (sub_pos.mpr (exp_one_partial_sum_lt n))
  have hlt : ((u - v : ℤ) : ℝ) < 1 := by
    rw [Int.cast_sub, ← hu, ← hv, hq', ← mul_sub]
    exact factorial_mul_exp_one_sub_partial_sum_lt_one n hn
  have hpos' : (0 : ℤ) < u - v := by exact_mod_cast hpos
  have hlt' : u - v < (1 : ℤ) := by exact_mod_cast hlt
  omega

/-! ### 圆周率 `π` 的基本接口 -/

/-- 圆周率 `π` 的教材层命名接口。-/
noncomputable def pi : ℝ := Real.pi

/-- 本库的 `π` 接口就是 Mathlib 的实圆周率。
> **Entry**: analysis.constants.pi-definition-/
theorem pi_eq_real_pi : pi = Real.pi := by
  rfl

/-- 圆周率为正。-/
theorem pi_pos : 0 < pi := by
  rw [pi_eq_real_pi]
  exact Real.pi_pos

/-- 圆周率非零。-/
theorem pi_ne_zero : pi ≠ 0 := by
  rw [pi_eq_real_pi]
  exact Real.pi_ne_zero

/-- `sin π = 0`。-/
theorem sin_pi : Real.sin pi = 0 := by
  rw [pi_eq_real_pi]
  exact Real.sin_pi

/-- `cos π = -1`。-/
theorem cos_pi : Real.cos pi = -1 := by
  rw [pi_eq_real_pi]
  exact Real.cos_pi

/-- 周期量 `2π` 为正。-/
theorem two_pi_pos : 0 < 2 * pi := by
  rw [pi_eq_real_pi]
  exact Real.two_pi_pos

/-- 圆周率 `π` 是无理数。

本库的 `pi` 按定义就是 `Real.pi`，因此该结论直接继承 Mathlib 中 Cartwright
积分法的完整形式化证明。
> **Entry**: analysis.constants.pi-irrational-/
theorem pi_irrational : Irrational pi := by
  rw [pi_eq_real_pi]
  exact irrational_pi

/-! ### 初等函数的常用特殊值 -/

/-- 指数函数在零点的值。-/
theorem exp_zero : Real.exp 0 = 1 := by
  exact Real.exp_zero

/-- 指数函数在一点的值就是自然常数 `e`。-/
theorem exp_one : Real.exp 1 = e := by
  rfl

/-- 自然对数在 `1` 点的值。-/
theorem log_one : Real.log 1 = 0 := by
  exact Real.log_one

/-- 正弦函数在零点的值。-/
theorem sin_zero : Real.sin 0 = 0 := by
  exact Real.sin_zero

/-- 余弦函数在零点的值。-/
theorem cos_zero : Real.cos 0 = 1 := by
  exact Real.cos_zero

/-- 正弦函数在 `π/2` 点的值。
> **Entry**: analysis.constants.special-values-/
theorem sin_pi_div_two : Real.sin (Real.pi / 2) = 1 := by
  exact Real.sin_pi_div_two

/-- 余弦函数在 `π/2` 点的值。-/
theorem cos_pi_div_two : Real.cos (Real.pi / 2) = 0 := by
  exact Real.cos_pi_div_two

/-- 正弦函数在 `π` 点的值。-/
theorem sin_pi_value : Real.sin Real.pi = 0 := by
  exact Real.sin_pi

/-- 余弦函数在 `π` 点的值。-/
theorem cos_pi_value : Real.cos Real.pi = -1 := by
  exact Real.cos_pi

/-! ### 非完全幂的整数根无理性 -/

/-- 若实数的正整数次幂是整数，但该整数不是整数的同次幂，则该实数无理。
> **Entry**: analysis.constants.nth-root-irrational-/
theorem irrational_nth_root_of_not_perfect {x : ℝ} {n : ℕ} {m : ℤ}
    (hpow : x ^ n = (m : ℝ))
    (hnot : ¬ ∃ z : ℤ, (z : ℝ) ^ n = (m : ℝ))
    (hnpos : 0 < n) : Irrational x := by
  apply irrational_nrt_of_notint_nrt n m hpow ?_ hnpos
  rintro ⟨z, hz⟩
  apply hnot
  refine ⟨z, ?_⟩
  rw [← hz]
  exact hpow

end Analysis.Constants
end SandronesLibrary
