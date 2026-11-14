/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.NumberTheory.Elementary.Pell

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 正 Pell 方程全体正解的分类

本文件补上 `Pell.lean` 中 Brahmagupta 复合所缺的另一半：复合只说明“基本解的幂仍然是解”，
这里反过来证明**每个正解都是基本解的幂**，从而给出全体正解的完整分类。

公开接口仍然只用整数坐标 `(x, y)` 与 `PellSolution.comp`。Mathlib 中把解打包成 `ℤ√d` 的单位元
再使用群论分类的路线，只在证明内部作为后端出现，不进入本文件的公开陈述。

分类的精确边界：本文件处理的是第二坐标非负的解。带符号的完整分类（允许取相反数）等价于
Mathlib 的 `Pell.IsFundamental.eq_zpow_or_neg_zpow`，需要整数次幂，本文件不重述它；
负 Pell 方程 `x² - d y² = -1` 与本文件无关，本文件不对它作任何断言。

## 本文件条目

* `number-theory.elementary.pell-all-positive`
-/

namespace SandronesLibrary.NumberTheory.Elementary

/-- 把本库用整数坐标表示的 Pell 解送到 Mathlib 的 `Pell.Solution₁`。

这是一个只用于证明的桥：`Pell.Solution₁ d` 把解实现为二次整数环 `ℤ√d` 中范数为 `1` 的单位元，
从而自带交换群结构；本库的教材接口刻意不暴露这一层。桥本身是双射（见
`PellSolution.toMathlib_injective`），所以两边的分类结论可以互相搬运。

> **Entry**: number-theory.elementary.pell-all-positive-/
def PellSolution.toMathlib {d : ℤ} (a : PellSolution d) : Pell.Solution₁ d :=
  Pell.Solution₁.mk a.x a.y a.equation

/-- 桥保持第一坐标。
@isnad1 id=eq.0h2v.s3.0263ff3dd10b from=translated src=- shape=74148a6e vocab=16302710
-/
@[simp]
theorem PellSolution.toMathlib_x {d : ℤ} (a : PellSolution d) :
    a.toMathlib.x = a.x := rfl

/-- 桥保持第二坐标。
@isnad1 id=eq.0h2v.s3.357f7873b570 from=translated src=- shape=74148a6e vocab=c3761f3e
-/
@[simp]
theorem PellSolution.toMathlib_y {d : ℤ} (a : PellSolution d) :
    a.toMathlib.y = a.y := rfl

/-- 桥 `PellSolution.toMathlib` 是单射：两个解只要有相同的整数坐标就相等。

因此 Mathlib 侧关于 `Pell.Solution₁` 的等式可以搬回本库的整数坐标陈述。

> **Entry**: number-theory.elementary.pell-all-positive
@isnad1 id=injectiv.0h1v.s3.6ad49b4e1b80 from=translated src=- shape=ca92e646 vocab=36e5f2c0
-/
theorem PellSolution.toMathlib_injective {d : ℤ} :
    Function.Injective (PellSolution.toMathlib (d := d)) := by
  intro a b h
  have hx : a.x = b.x := by simpa using congrArg Pell.Solution₁.x h
  have hy : a.y = b.y := by simpa using congrArg Pell.Solution₁.y h
  cases a; cases b; simp_all

/-- 桥把平凡解 `(1, 0)` 送到群的单位元。
@isnad1 id=eq.0h1v.s5.d80653891884 from=translated src=- shape=ec1778f2 vocab=cd8af94b
-/
theorem PellSolution.toMathlib_one (d : ℤ) :
    (PellSolution.one d).toMathlib = 1 := by
  apply Pell.Solution₁.ext <;> simp [PellSolution.one]

/-- 桥把 Brahmagupta 复合送到 Mathlib 侧的乘法。

本库的 `PellSolution.comp` 与 `Pell.Solution₁` 的乘法逐坐标给出同一个公式
`(x₁x₂ + d y₁y₂, x₁y₂ + y₁x₂)`，所以教材接口上的“复合”就是二次整数环中的乘法。

> **Entry**: number-theory.elementary.pell-all-positive
@isnad1 id=eq.0h3v.s5.dc9acfd6439d from=translated src=- shape=649dce7d vocab=73a1da91
-/
theorem PellSolution.toMathlib_comp {d : ℤ} (a b : PellSolution d) :
    (a.comp b).toMathlib = a.toMathlib * b.toMathlib := by
  apply Pell.Solution₁.ext <;> simp [PellSolution.comp]

/-- Pell 解的 `n` 次幂：Brahmagupta 复合的迭代，`a.pow 0` 取平凡解 `(1, 0)`。

之所以要单独定义而不是直接借用 `^`，是因为本库的 `PellSolution` 只是携带方程证明的数对，
没有被包装成群；把幂写成复合的迭代，读者只需要理解复合，不需要理解群。

> **Entry**: number-theory.elementary.pell-all-positive-/
def PellSolution.pow {d : ℤ} (a : PellSolution d) : ℕ → PellSolution d
  | 0 => PellSolution.one d
  | n + 1 => (PellSolution.pow a n).comp a

/-- 第零次幂是平凡解。
@isnad1 id=eq.0h2v.s4.e62b2f3baa2f from=translated src=- shape=ce150b78 vocab=a792eab9
-/
@[simp]
theorem PellSolution.pow_zero {d : ℤ} (a : PellSolution d) :
    a.pow 0 = PellSolution.one d := rfl

/-- 幂的递推：`a^(n+1) = a^n ∘ a`。
@isnad1 id=eq.0h3v.s5.8515e82e5236 from=translated src=- shape=a3d77dca vocab=56b826be
-/
@[simp]
theorem PellSolution.pow_succ {d : ℤ} (a : PellSolution d) (n : ℕ) :
    a.pow (n + 1) = (a.pow n).comp a := rfl

/-- 桥把本库的幂送到 Mathlib 侧的幂。
@isnad1 id=eq.0h3v.s5.c9c85e9c78d1 from=translated src=- shape=edcc5553 vocab=5aa98f2c
-/
theorem PellSolution.toMathlib_pow {d : ℤ} (a : PellSolution d) (n : ℕ) :
    (a.pow n).toMathlib = a.toMathlib ^ n := by
  induction n with
  | zero => simp [PellSolution.toMathlib_one]
  | succ n ih => rw [PellSolution.pow_succ, PellSolution.toMathlib_comp, ih, _root_.pow_succ]

/-- 桥把本库的基本解送到 Mathlib 的基本解。

两个“基本”定义逐字相同：`1 < x`、`0 < y`，且第一坐标在所有 `x > 1` 的解中最小。

> **Entry**: number-theory.elementary.pell-all-positive
@isnad1 id=isfundam.1h2v.s3.8e9f339d1f76 from=translated src=- shape=08ded1e7 vocab=6531284b
-/
theorem PellSolution.isFundamental_toMathlib {d : ℤ} {a : PellSolution d}
    (ha : IsFundamentalPellSolution a) : Pell.IsFundamental a.toMathlib := by
  refine ⟨?_, ?_, ?_⟩
  · simpa using ha.1
  · simpa using ha.2.1
  · intro b hb
    exact ha.2.2 ⟨b.x, b.y, b.prop⟩ (by simpa using hb)

/-- 基本解至多有一个。

证明走桥：Mathlib 已经证明基本解唯一，搬回整数坐标即可。这条定理说明“分类”里的“基本解”
是良定义的，也说明上一条单射桥确实在两类结论之间双向搬运。

> **Entry**: number-theory.elementary.pell-all-positive
@isnad1 id=eq.2h3v.s4.ecf17493b2e6 from=translated src=- shape=13b462d4 vocab=5c64cea7
-/
theorem IsFundamentalPellSolution.subsingleton {d : ℤ} {a b : PellSolution d}
    (ha : IsFundamentalPellSolution a) (hb : IsFundamentalPellSolution b) : a = b := by
  apply PellSolution.toMathlib_injective
  exact Pell.IsFundamental.subsingleton (PellSolution.isFundamental_toMathlib ha)
    (PellSolution.isFundamental_toMathlib hb)

/-- **全体正解的分类（非负坐标形式）。** 设 `a` 是基本解，则每个满足 `0 < x`、`0 ≤ y` 的解
都是 `a` 的某个自然数次幂。

这正是 Brahmagupta 复合单独给不出的那一半：复合只说“基本解的幂仍是解”，本定理反过来说
“每个正解都落在幂序列上”，两者合起来才是完整的分类。证明把解搬到 Mathlib 的
`Pell.Solution₁`，调用已经形式化的 `Pell.IsFundamental.eq_pow_of_nonneg`，再用单射桥搬回。

> **Entry**: number-theory.elementary.pell-all-positive
@isnad1 id=ex.3h3v.s5.9f882d9152bb from=translated src=- shape=3b15ef16 vocab=031325f0
-/
theorem exists_pow_eq_of_fundamental {d : ℤ} {a : PellSolution d}
    (ha : IsFundamentalPellSolution a) {b : PellSolution d} (hx : 0 < b.x) (hy : 0 ≤ b.y) :
    ∃ n : ℕ, b = a.pow n := by
  obtain ⟨n, hn⟩ := Pell.IsFundamental.eq_pow_of_nonneg (a := b.toMathlib)
    (PellSolution.isFundamental_toMathlib ha) (by simpa using hx) (by simpa using hy)
  refine ⟨n, ?_⟩
  apply PellSolution.toMathlib_injective
  rw [PellSolution.toMathlib_pow]
  exact hn

/-- **分类的双向形式。** 以基本解 `a` 为底，`b` 是“坐标非负的正解”当且仅当 `b` 是 `a` 的幂。

向左是上一条定理；向右只需要注意基本解的坐标严格为正，而复合保持坐标为正，所以幂的坐标
仍然非负。

> **Entry**: number-theory.elementary.pell-all-positive
@isnad1 id=iff.1h3v.s5.b267622082e8 from=translated src=- shape=28d61921 vocab=031325f0
-/
theorem pos_iff_exists_pow {d : ℤ} {a : PellSolution d} (ha : IsFundamentalPellSolution a)
    (b : PellSolution d) : (0 < b.x ∧ 0 ≤ b.y) ↔ ∃ n : ℕ, b = a.pow n := by
  constructor
  · rintro ⟨hx, hy⟩
    exact exists_pow_eq_of_fundamental ha hx hy
  · rintro ⟨n, rfl⟩
    have hax : 0 < a.toMathlib.x := by simpa using (zero_lt_one.trans ha.1)
    have hay : 0 < a.toMathlib.y := by simpa using ha.2.1
    have hx' : (a.pow n).x = (a.toMathlib ^ n).x := by
      simpa using congrArg Pell.Solution₁.x (PellSolution.toMathlib_pow a n)
    have hy' : (a.pow n).y = (a.toMathlib ^ n).y := by
      simpa using congrArg Pell.Solution₁.y (PellSolution.toMathlib_pow a n)
    constructor
    · rw [hx']; exact Pell.Solution₁.x_pow_pos hax n
    · rw [hy']
      cases n with
      | zero => simp
      | succ k => exact (Pell.Solution₁.y_pow_succ_pos hax hay k).le

/-- 教材意义下的“非平凡正解”（`1 < x`、`0 < y`）一定是基本解的正数次幂。

与 `exists_pow_eq_of_fundamental` 相比，这里把结论中的指数加强为 `0 < n`：指数为零只会给出
平凡解 `(1, 0)`，与 `1 < x` 矛盾。

> **Entry**: number-theory.elementary.pell-all-positive
@isnad1 id=ex.3h3v.s5.b4d78eac1c45 from=translated src=- shape=66883163 vocab=67bffe94
-/
theorem exists_pos_pow_eq_of_fundamental {d : ℤ} {a : PellSolution d}
    (ha : IsFundamentalPellSolution a) {b : PellSolution d} (hx : 1 < b.x) (hy : 0 < b.y) :
    ∃ n : ℕ, 0 < n ∧ b = a.pow n := by
  obtain ⟨n, hn⟩ := exists_pow_eq_of_fundamental ha (zero_lt_one.trans hx) hy.le
  refine ⟨n, ?_, hn⟩
  rcases Nat.eq_zero_or_pos n with h | h
  · rw [h, PellSolution.pow_zero] at hn
    rw [hn] at hx
    simp [PellSolution.one] at hx
  · exact h

/-- **分类的收口形式。** 正的非平方整数参数存在基本解 `a`，使得该参数的全体非负坐标正解
恰好是 `a` 的自然数次幂。

这条把 `Pell.lean` 里的存在性（`exists_fundamentalPellSolution`）与上面的全称分类拼在一起，
是本条目对“全体正解由基本解幂生成”的完整陈述。注意它只谈正方程 `x² - d y² = 1`：
负 Pell 的可解性是另一条独立的边界，不由本定理暗示。

> **Entry**: number-theory.elementary.pell-all-positive
@isnad1 id=ex.2h1v.s6.4f345acd953f from=translated src=- shape=cdca0c51 vocab=24011b29
-/
theorem exists_fundamental_pellSolution_pow_classification {d : ℤ} (hd : 0 < d)
    (hns : ¬IsSquare d) :
    ∃ a : PellSolution d, IsFundamentalPellSolution a ∧
      ∀ b : PellSolution d, (0 < b.x ∧ 0 ≤ b.y) ↔ ∃ n : ℕ, b = a.pow n := by
  obtain ⟨a, ha⟩ := exists_fundamentalPellSolution hd hns
  exact ⟨a, ha, fun b => pos_iff_exists_pow ha b⟩

end SandronesLibrary.NumberTheory.Elementary
