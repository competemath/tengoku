/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.SetTheory.GoodsteinDescent

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# SetTheory / GoodsteinNoBorrow —— 正末位复合式的无借位下降

本文件只处理形如 `prefix + digit` 的遗传表达式，其中最后的数字严格为正。
因为减一只需把这个最后数字减一，所以可以给出显式重编码并证明 `ω` 度量
严格下降。这里不包含末位为零时的任何借位。
-/

namespace SandronesLibrary.SetTheory.Googology

open SandronesLibrary.SetTheory.Ordinal

noncomputable section

/--
正末位无借位形：一个在当前底数下合法的前缀，加上一个合法的正数字末项。
前缀本身可以是复合遗传表达式。-/
structure PositiveTailNoBorrowForm (base : ℕ) where
  head : HereditaryBaseExpr
  head_valid : head.Valid base
  digit : ℕ
  digit_positive : 0 < digit
  digit_valid : digit < base

/-- 将正末位形嵌入通用遗传表达式。-/
def PositiveTailNoBorrowForm.expression {base : ℕ}
    (f : PositiveTailNoBorrowForm base) : HereditaryBaseExpr :=
  .add f.head (.digit f.digit)

/-- 无借位减一后的显式重编码：前缀不变，只将正末位减一。-/
def PositiveTailNoBorrowForm.predecessorExpression {base : ℕ}
    (f : PositiveTailNoBorrowForm base) : HereditaryBaseExpr :=
  .add f.head (.digit (f.digit - 1))

private theorem HereditaryBaseExpr.valid_of_base_le {e : HereditaryBaseExpr}
    {oldBase newBase : ℕ} (hvalid : e.Valid oldBase) (hbase : oldBase ≤ newBase) :
    e.Valid newBase := by
  induction e with
  | zero => trivial
  | digit n => exact lt_of_lt_of_le hvalid hbase
  | add left right leftIH rightIH =>
      exact ⟨leftIH hvalid.1, rightIH hvalid.2⟩
  | mul left right leftIH rightIH =>
      exact ⟨leftIH hvalid.1, rightIH hvalid.2⟩
  | basePow exponent exponentIH => exact exponentIH hvalid

/--
> **Entry**: settheory.googology.goodstein-positive-tail-no-borrow
> **一句话**: 对“合法复合前缀加正数字末项”，Goodstein 减一无需借位，显式重编码的 `ω` 度量严格下降。
> **依赖**: `settheory.googology.goodstein-positive-digit-descent`、
>   `settheory.googology.goodstein-ordinal-measure`
> **mathlib**: `Nat.add_sub_assoc`、`Order.lt_succ`-/
theorem positiveTail_goodstein_descent {base : ℕ}
    (f : PositiveTailNoBorrowForm base) :
    goodsteinStep base f.expression =
        f.head.eval (base + 1) + (f.digit - 1) ∧
      f.predecessorExpression.Valid (base + 1) ∧
      f.predecessorExpression.eval (base + 1) = goodsteinStep base f.expression ∧
      f.predecessorExpression.omegaValue < f.expression.omegaValue := by
  have hpred_lt : f.digit - 1 < f.digit :=
    Nat.sub_one_lt (Nat.ne_of_gt f.digit_positive)
  have hpred_succ : f.digit - 1 + 1 = f.digit :=
    Nat.sub_add_cancel (Nat.succ_le_iff.mpr f.digit_positive)
  have hprefix_valid : f.head.Valid (base + 1) :=
    HereditaryBaseExpr.valid_of_base_le f.head_valid (Nat.le_succ base)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [goodsteinStep, hereditaryBaseChangeValue,
      PositiveTailNoBorrowForm.expression, HereditaryBaseExpr.eval]
    omega
  · simp only [PositiveTailNoBorrowForm.predecessorExpression,
      HereditaryBaseExpr.Valid]
    exact ⟨hprefix_valid, lt_trans hpred_lt (lt_trans f.digit_valid (Nat.lt_succ_self base))⟩
  · simp only [PositiveTailNoBorrowForm.predecessorExpression,
      HereditaryBaseExpr.eval]
    rw [show goodsteinStep base f.expression =
      f.head.eval (base + 1) + (f.digit - 1) by
        simp only [goodsteinStep, hereditaryBaseChangeValue,
          PositiveTailNoBorrowForm.expression, HereditaryBaseExpr.eval]
        omega]
  · simp only [PositiveTailNoBorrowForm.predecessorExpression,
      PositiveTailNoBorrowForm.expression, HereditaryBaseExpr.omegaValue]
    have hcast : ((f.digit : ℕ) : Ordinal) =
        Order.succ ((f.digit - 1 : ℕ) : Ordinal) := by
      rw [Order.succ_eq_add_one]
      exact_mod_cast hpred_succ.symm
    rw [hcast, ordinalAdd_succ]
    exact Order.lt_succ _

end

end SandronesLibrary.SetTheory.Googology
