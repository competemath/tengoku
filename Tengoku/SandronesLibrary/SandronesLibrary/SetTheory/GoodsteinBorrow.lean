/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.SetTheory.GoodsteinNoBorrow

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# SetTheory / GoodsteinBorrow —— 从底数一次幂借位

本文件处理第一个真正需要借位的复合形式：`head + B¹`。将底数从 `b`
提高到 `b+1` 后再减一，最后的 `B¹` 被显式展开为新底数下的数字 `b`。
该局部展开不是任意指数、任意系数或连锁借位定理。
-/

namespace SandronesLibrary.SetTheory.Googology

open SandronesLibrary.SetTheory.Ordinal

noncomputable section

/--
底数一次幂末项的借位形：底数至少为二，并且头部遗传表达式在当前
底数下合法。-/
structure BasePowerOneTailBorrowForm (base : ℕ) where
  base_ge_two : 2 ≤ base
  head : HereditaryBaseExpr
  head_valid : head.Valid base

/-- 借位前的表达式 `head + B¹`。-/
def BasePowerOneTailBorrowForm.expression {base : ℕ}
    (f : BasePowerOneTailBorrowForm base) : HereditaryBaseExpr :=
  .add f.head (.basePow (.digit 1))

/--
在新底数 `base+1` 下，`B¹-1` 展开成数字 `base`；头部的语法树不变。-/
def BasePowerOneTailBorrowForm.borrowedExpression {base : ℕ}
    (f : BasePowerOneTailBorrowForm base) : HereditaryBaseExpr :=
  .add f.head (.digit base)

private theorem HereditaryBaseExpr.valid_at_next_base {e : HereditaryBaseExpr}
    {base : ℕ} (hvalid : e.Valid base) : e.Valid (base + 1) := by
  induction e with
  | zero => trivial
  | digit n => exact lt_trans hvalid (Nat.lt_succ_self base)
  | add left right leftIH rightIH =>
      exact ⟨leftIH hvalid.1, rightIH hvalid.2⟩
  | mul left right leftIH rightIH =>
      exact ⟨leftIH hvalid.1, rightIH hvalid.2⟩
  | basePow exponent exponentIH => exact exponentIH hvalid

private theorem ordinalPow_omega_one :
    ordinalPow Ordinal.omega0 ((1 : ℕ) : Ordinal) = Ordinal.omega0 := by
  change ordinalPow Ordinal.omega0 (Order.succ 0) = Ordinal.omega0
  rw [ordinalPow_succ, ordinalPow_zero]
  simp [ordinalMul]

/--
> **Entry**: settheory.googology.goodstein-base-power-one-borrow
> **一句话**: `head + B¹` 换底减一后可借位展开为 `head + base`，且 `ω` 度量从末项 `ω` 严格降到有限末项。
> **依赖**: `settheory.googology.goodstein-positive-tail-no-borrow`、
>   `settheory.googology.goodstein-ordinal-measure`
> **mathlib**: `Ordinal.natCast_lt_omega0`、`add_lt_add_iff_left`-/
theorem basePowerOneTail_goodstein_borrow_descent {base : ℕ}
    (f : BasePowerOneTailBorrowForm base) :
    f.expression.Valid base ∧
      goodsteinStep base f.expression = f.head.eval (base + 1) + base ∧
      f.borrowedExpression.Valid (base + 1) ∧
      f.borrowedExpression.eval (base + 1) = goodsteinStep base f.expression ∧
      f.borrowedExpression.omegaValue < f.expression.omegaValue := by
  have hone_lt_base : 1 < base := lt_of_lt_of_le Nat.one_lt_two f.base_ge_two
  have hhead_next : f.head.Valid (base + 1) :=
    HereditaryBaseExpr.valid_at_next_base f.head_valid
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨f.head_valid, hone_lt_base⟩
  · simp [goodsteinStep, hereditaryBaseChangeValue,
      BasePowerOneTailBorrowForm.expression, HereditaryBaseExpr.eval]
  · exact ⟨hhead_next, Nat.lt_succ_self base⟩
  · simp [BasePowerOneTailBorrowForm.borrowedExpression,
      BasePowerOneTailBorrowForm.expression, goodsteinStep,
      hereditaryBaseChangeValue, HereditaryBaseExpr.eval]
  · simp only [BasePowerOneTailBorrowForm.borrowedExpression,
      BasePowerOneTailBorrowForm.expression, HereditaryBaseExpr.omegaValue,
      ordinalPow_omega_one]
    rw [show ordinalAdd f.head.omegaValue base = f.head.omegaValue + base by
        simp [ordinalAdd],
      show ordinalAdd f.head.omegaValue Ordinal.omega0 =
          f.head.omegaValue + Ordinal.omega0 by simp [ordinalAdd]]
    exact (add_lt_add_iff_left f.head.omegaValue).2
      (Ordinal.natCast_lt_omega0 base)

end

end SandronesLibrary.SetTheory.Googology
