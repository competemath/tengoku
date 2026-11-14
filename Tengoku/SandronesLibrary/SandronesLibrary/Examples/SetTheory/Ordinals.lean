/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.SetTheory.Ordinal
import Tengoku.Seed.SetTheory.Ordinal.Principal
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Examples / 集合论：序数 `0,1,2,ω,ω+1` 的序关系与后继／极限辨析

本文件为序数 ST1 条目 `settheory.ordinal.order-type`、`settheory.ordinal.addition`、
`settheory.ordinal.successor-limit` 补齐最小的可核对实例：把 `ω + 1` 命名出来，证明它就是
`ω` 的后继，从而得到序关系链 `0 < 1 < 2 < ω < ω + 1`；再区分极限序数 `ω` 与后继序数 `ω + 1`；
最后用 `1 + ω = ω` 而 `ω + 1 ≠ ω` 这一对具体事实，给出「序数加法不交换」的精确反例。

> **Entry**: examples.settheory.ordinals
-/

noncomputable section

namespace SandronesLibrary.Examples.SetTheory.Ordinals

open SandronesLibrary.SetTheory.Ordinal

-- 显式声明宇宙变量：下列序数定理保持宇宙多态，同时**声明名不带 `.{u}` 后缀**。
-- （`check_axioms.py` 的声明名正则会把源码里的 `foo.{u}` 捕成 `foo.`，而 `#print axioms foo.`
-- 是语法错，会让公理字段变成 `<解析失败>`。）
universe u

/-- `ω + 1`：把 `1` 接在 `ω` 后面的序数，即本库加法 `ordinalAdd ω 1`。-/
def omegaPlusOne : Ordinal :=
  ordinalAdd Ordinal.omega0 1

/-- **定义展开**：`omegaPlusOne` 就是 `ordinalAdd ω 1`。-/
theorem omegaPlusOne_def : omegaPlusOne = ordinalAdd Ordinal.omega0 1 := rfl

/-- **`ω + 1` 是 `ω` 的后继**：`1 = succ 0`，再用加法在后继处的递推式。-/
theorem omegaPlusOne_eq_succ_omega : omegaPlusOne = Order.succ Ordinal.omega0 := by
  rw [omegaPlusOne_def]
  have h1 : Order.succ (0 : Ordinal) = 1 := by rw [Order.succ_eq_add_one, zero_add]
  rw [← h1, ordinalAdd_succ, ordinalAdd_zero]

/-- **后继严格更大**：`ω < ω + 1`，因为 `ω + 1 = succ ω` 而后继严格大于原序数。-/
theorem omega_lt_omegaPlusOne : Ordinal.omega0 < omegaPlusOne := by
  rw [omegaPlusOne_eq_succ_omega]
  exact Order.lt_succ Ordinal.omega0

/-- **序关系链**：`0 < 1 < 2 < ω < ω + 1`。前两项由 `norm_num` 在序数上真算，
`2 < ω` 用「每个自然数序数都小于 `ω`」，最后一项是上一句。-/
theorem zero_lt_one_lt_two_lt_omega_lt_omegaPlusOne :
    (0 : Ordinal) < 1 ∧ (1 : Ordinal) < 2 ∧ (2 : Ordinal) < Ordinal.omega0 ∧
      Ordinal.omega0 < omegaPlusOne :=
  ⟨by norm_num, by norm_num, Ordinal.natCast_lt_omega0 2, omega_lt_omegaPlusOne⟩

/-- **`ω` 是极限序数**：取本库 `successor_and_limit` 的第三个合取项。-/
theorem omega_is_limit : Order.IsSuccLimit (Ordinal.omega0.{u}) := by
  obtain ⟨-, -, h⟩ := successor_and_limit.{u, u} (0 : Ordinal.{u})
  exact h

/-- **后继序数不是极限序数**：对任意序数 `a`，`succ a` 都不满足 `IsSuccLimit`。-/
theorem succ_not_limit (a : Ordinal) : ¬ Order.IsSuccLimit (Order.succ a) :=
  Order.not_isSuccLimit_succ a

/-- **后继紧邻原序数**：`a < succ a`，且没有序数严格落在两者之间。-/
theorem succ_is_immediate (a : Ordinal.{u}) :
    a < Order.succ a ∧ ∀ b : Ordinal.{u}, a < b → ¬ b < Order.succ a := by
  obtain ⟨h1, h2, -⟩ := successor_and_limit.{u, u} a
  exact ⟨h1, h2⟩

/-- **后继／极限辨析的具体实例**：`ω` 是极限序数，而 `ω + 1` 是后继序数、不是极限序数。-/
theorem omega_limit_but_omegaPlusOne_not :
    Order.IsSuccLimit Ordinal.omega0 ∧ ¬ Order.IsSuccLimit omegaPlusOne := by
  refine ⟨omega_is_limit, ?_⟩
  rw [omegaPlusOne_eq_succ_omega]
  exact Order.not_isSuccLimit_succ Ordinal.omega0

/-- **`ω + 1` 确实是后继序数**：存在原序数 `ω` 使 `ω + 1 = succ ω`。-/
theorem omegaPlusOne_is_successor : ∃ a : Ordinal, omegaPlusOne = Order.succ a :=
  ⟨Ordinal.omega0, omegaPlusOne_eq_succ_omega⟩

/-- **左加 `ω` 的吸收**：`1 + ω = ω`（把 `1` 接在 `ω` 前面不改变序型）。-/
theorem one_add_omega_eq_omega :
    ordinalAdd (1 : Ordinal.{u}) (Ordinal.omega0.{u}) = Ordinal.omega0.{u} := by
  obtain ⟨h, -⟩ := addition_not_commutative.{u, u}
  exact h

/-- **右加 `1` 不是吸收**：`ω + 1 ≠ ω`，由 `ω < ω + 1` 直接得到。-/
theorem omega_add_one_ne_omega : omegaPlusOne ≠ Ordinal.omega0 :=
  ne_of_gt omega_lt_omegaPlusOne

/-- **反例：序数加法不交换**。交换两个加数得到不同结果：
`1 + ω = ω`，而 `ω + 1 ≠ ω`，所以 `1 + ω ≠ ω + 1`。
这否定了「序数加法像自然数加法那样交换」这一误认；`addition_not_commutative` 是本库给出的
一般性结论，本定理是它在 `(1, ω)` 这一对具体序数上的实例。-/
theorem one_add_omega_ne_omega_add_one :
    ordinalAdd (1 : Ordinal) Ordinal.omega0 ≠ omegaPlusOne := by
  rw [one_add_omega_eq_omega]
  exact fun h => omega_add_one_ne_omega h.symm

end SandronesLibrary.Examples.SetTheory.Ordinals
