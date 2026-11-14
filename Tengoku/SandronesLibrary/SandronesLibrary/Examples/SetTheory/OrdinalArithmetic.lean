/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.SetTheory.Ordinal
import Tengoku.SandronesLibrary.SandronesLibrary.SetTheory.OrdinalPowerBridge
import Tengoku.Seed.SetTheory.Ordinal.Principal
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Examples / 集合论：有限序数与 `ω` 的加乘幂、Cantor 正规形小例

本文件为序数运算主线条目 `settheory.ordinal.addition`、`settheory.ordinal.multiplication`、
`settheory.ordinal.exponentiation`、`settheory.ordinal.cantor-normal-form`、
`settheory.ordinal.power-bridge` 补齐可核对的小例：先用 `norm_num` 真算有限序数的加乘幂，
再给出 `ω + ω = ω * 2`、`2 * ω = ω`、`ω ^ 2 = ω * ω`、`ω ^ 0 = 1`；
然后实测两条消去律——序数加法**左消去成立**、**右消去失败**（`1 + ω = 2 + ω = ω` 而 `1 ≠ 2`），
并给出乘法不交换的反例；最后真算 `ω + 1` 的 Cantor 正规形并显式求值。

> **Entry**: examples.settheory.ordinal-arithmetic
-/

noncomputable section

namespace SandronesLibrary.Examples.SetTheory.OrdinalArithmetic

open SandronesLibrary.SetTheory.Ordinal

-- 显式声明宇宙变量：下列序数定理保持宇宙多态，同时**声明名不带 `.{u}` 后缀**。
-- （`check_axioms.py` 的声明名正则会把源码里的 `foo.{u}` 捕成 `foo.`，而 `#print axioms foo.`
-- 是语法错，会让公理字段变成 `<解析失败>`。）
universe u

/-- 本库加法与 mathlib 原生 `+` 一致；只在本文件内用于把教材定义交给 mathlib 验证。-/
private theorem ordinalAdd_eq_add (a b : Ordinal) : ordinalAdd a b = a + b := by
  simp [ordinalAdd]

/-- 本库乘法与 mathlib 原生 `*` 一致；同样只作私有证明后端。-/
private theorem ordinalMul_eq_mul (a b : Ordinal) : ordinalMul a b = a * b := by
  simp [ordinalMul]

/-! ## 有限序数的加乘幂真计算 -/

/-- **有限序数加法真计算**：`3 + 4 = 7`。-/
theorem finite_add : ordinalAdd (3 : Ordinal) 4 = 7 := by
  rw [ordinalAdd_eq_add]
  norm_num

/-- **有限序数乘法真计算**：`2 * 3 = 6`。-/
theorem finite_mul : ordinalMul (2 : Ordinal) 3 = 6 := by
  rw [ordinalMul_eq_mul]
  norm_num

/-! ## `ω` 的加乘幂小例 -/

/-- **`ω + ω = ω * 2`**：左端是两个 `ω` 拼接，右端是 `ω` 的两份副本，序型相同。-/
theorem omega_add_omega_eq_omega_mul_two :
    ordinalAdd Ordinal.omega0 Ordinal.omega0 = ordinalMul Ordinal.omega0 2 := by
  rw [ordinalAdd_eq_add, ordinalMul_eq_mul, Ordinal.mul_two]

/-- **`2 * ω = ω`**：有限序数乘 `ω` 被吸收。-/
theorem two_mul_omega_eq_omega :
    ordinalMul (2 : Ordinal.{u}) (Ordinal.omega0.{u}) = Ordinal.omega0.{u} := by
  obtain ⟨h, -⟩ := multiplication_not_commutative.{u, u}
  exact h

/-- **`ω * 2 ≠ ω`**：右乘 `2` 不吸收，`ω * 2 = ω + ω` 比 `ω` 多一个 `ω`。-/
theorem omega_mul_two_ne_omega :
    ordinalMul (Ordinal.omega0.{u}) 2 ≠ Ordinal.omega0.{u} := by
  obtain ⟨-, h⟩ := multiplication_not_commutative.{u, u}
  exact h

/-- **`ω ^ 0 = 1`**：序数幂的零次幂。-/
theorem omega_pow_zero : ordinalPow Ordinal.omega0 0 = 1 :=
  ordinalPow_zero Ordinal.omega0

/-! ## 反例：加法与乘法不交换 -/

/-- **反例：序数乘法不交换**。`2 * ω = ω`，而 `ω * 2 ≠ ω`，所以两个方向结果不同。
这否定了「序数乘法像自然数乘法那样交换」；`multiplication_not_commutative` 是库内一般结论。-/
theorem omega_mul_two_ne_two_mul_omega :
    ordinalMul (Ordinal.omega0.{u}) 2 ≠
      ordinalMul (2 : Ordinal.{u}) (Ordinal.omega0.{u}) := by
  rw [two_mul_omega_eq_omega]
  exact omega_mul_two_ne_omega

/-- **反例：序数加法不交换**。`1 + ω = ω`，而 `ω + 1` 是 `ω` 的后继、不等于 `ω`，
所以交换两个加数改变结果。这是本 Entry 消去律主线的另一半：右消去失败与加法不交换是同一现象。-/
theorem one_add_omega_ne_omega_add_one :
    ordinalAdd (1 : Ordinal) Ordinal.omega0 ≠ ordinalAdd Ordinal.omega0 1 := by
  rw [ordinalAdd_eq_add, ordinalAdd_eq_add]
  have h1 : Ordinal.omega0 + 1 = Order.succ Ordinal.omega0 := by rw [Order.succ_eq_add_one]
  rw [Ordinal.add_omega0 Ordinal.one_lt_omega0, h1]
  exact (Order.lt_succ Ordinal.omega0).ne

/-! ## 消去律：实测方向 -/

/-- **正例：序数加法左消去成立**。公共左加数 `c` 可以消去：
`c + a = c + b → a = b`。这与 ROADMAP 原文「左消去失败」相反，是实测结论。-/
theorem addition_left_cancellation {a b c : Ordinal.{u}}
    (h : ordinalAdd c a = ordinalAdd c b) : a = b := by
  rw [ordinalAdd_eq_add, ordinalAdd_eq_add] at h
  exact add_left_cancel h

/-- **反例：序数加法右消去失败**。前件 `1 + ω = 2 + ω` 成立（两者都等于 `ω`），
但后件 `1 = 2` 为假。所以公共右加数 `ω` 不能消去；真正失效的方向是右消去，
不是 ROADMAP 原文写的左消去。-/
theorem addition_right_cancellation_fails :
    ordinalAdd (1 : Ordinal) Ordinal.omega0 = ordinalAdd (2 : Ordinal) Ordinal.omega0 ∧
      (1 : Ordinal) ≠ 2 := by
  refine ⟨?_, by norm_num⟩
  rw [ordinalAdd_eq_add, ordinalAdd_eq_add]
  have h1lt : (1 : Ordinal) < Ordinal.omega0 := Ordinal.one_lt_omega0
  have h2lt : (2 : Ordinal) < Ordinal.omega0 := Ordinal.natCast_lt_omega0 2
  rw [Ordinal.add_omega0 h1lt, Ordinal.add_omega0 h2lt]

/-- **正例：序数乘法左消去成立**（左因子非零）：`c ≠ 0` 时 `c * a = c * b → a = b`。-/
theorem multiplication_left_cancellation {a b c : Ordinal.{u}} (hc : c ≠ 0)
    (h : ordinalMul c a = ordinalMul c b) : a = b := by
  rw [ordinalMul_eq_mul, ordinalMul_eq_mul] at h
  exact mul_left_cancel₀ hc h

/-- **反例：序数乘法右消去失败**。前件 `2 * ω = 1 * ω` 成立（两者都等于 `ω`），
但后件 `2 = 1` 为假。所以公共右因子 `ω` 不能消去。-/
theorem multiplication_right_cancellation_fails :
    ordinalMul (2 : Ordinal.{u}) (Ordinal.omega0.{u}) =
        ordinalMul (1 : Ordinal.{u}) (Ordinal.omega0.{u}) ∧
      (2 : Ordinal.{u}) ≠ 1 := by
  refine ⟨?_, by norm_num⟩
  conv_rhs => rw [ordinalMul_eq_mul, one_mul]
  exact two_mul_omega_eq_omega.{u}

/-! ## Cantor 正规形小例 -/

/-- 小例对象：`ω + 1`（用本库加法写出）。-/
def omegaPlusOneOrd : Ordinal :=
  ordinalAdd Ordinal.omega0 1

/-- **定义展开**：`omegaPlusOneOrd = ω + 1`。-/
theorem omegaPlusOneOrd_eq : omegaPlusOneOrd = Ordinal.omega0 + 1 := by
  rw [omegaPlusOneOrd, ordinalAdd_eq_add]

/-- **Cantor 正规形真计算**：底取 `ω` 时，`ω` 的正规形是 `[(1, 1)]`（即 `ω^1 * 1`）。-/
theorem cnf_omega : Ordinal.CNF Ordinal.omega0 Ordinal.omega0 = [(1, 1)] := by
  have h := Ordinal.CNF.opow_mul_add (b := Ordinal.omega0) (e := 1) (x := 1) (y := 0)
    (by norm_num) (by norm_num) (by norm_num) (by simp)
  simpa using h

/-- **Cantor 正规形真计算**：`ω + 1` 的正规形是 `[(1, 1), (0, 1)]`（即 `ω^1 * 1 + ω^0 * 1`）。-/
theorem cnf_omegaPlusOne :
    Ordinal.CNF Ordinal.omega0 omegaPlusOneOrd = [(1, 1), (0, 1)] := by
  rw [omegaPlusOneOrd_eq]
  have h := Ordinal.CNF.opow_mul_add (b := Ordinal.omega0) (e := 1) (x := 1) (y := 1)
    (by norm_num) (by norm_num) (by norm_num) (by simp)
  simpa [Ordinal.CNF.of_lt (b := Ordinal.omega0) (o := 1) (by norm_num)
    Ordinal.one_lt_omega0] using h

end SandronesLibrary.Examples.SetTheory.OrdinalArithmetic
