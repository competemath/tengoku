/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.SetTheory.GoodsteinBorrow

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# SetTheory / GoodsteinHigherBorrow —— 底数平方的显式借位

本文件处理 `head + B²` 这一个确定的高幂借位形。为了让指数叶子 `2`
本身是合法数字，证书明确要求底数至少为三。升底后令 `q=base+1`，
将 `q²-1` 展开为 `q·base+base`。本结果不涵盖任意指数或连锁借位。
-/

namespace SandronesLibrary.SetTheory.Googology

open SandronesLibrary.SetTheory.Ordinal

noncomputable section

/--
底数平方末项的带证书借位形。底数下界 `3 ≤ base` 保证指数数字 `2`
在原底数下合法。-/
structure BasePowerTwoTailBorrowForm (base : ℕ) where
  base_ge_three : 3 ≤ base
  head : HereditaryBaseExpr
  head_valid : head.Valid base

/-- 借位前的表达式 `head + B²`。-/
def BasePowerTwoTailBorrowForm.expression {base : ℕ}
    (f : BasePowerTwoTailBorrowForm base) : HereditaryBaseExpr :=
  .add f.head (.basePow (.digit 2))

/--
在新底数 `base+1` 下将 `B²-1` 展开为 `B·base+base`，其中两个
`base` 都是新底数下的合法数字。-/
def BasePowerTwoTailBorrowForm.borrowedExpression {base : ℕ}
    (f : BasePowerTwoTailBorrowForm base) : HereditaryBaseExpr :=
  .add f.head
    (.add (.mul (.basePow (.digit 1)) (.digit base)) (.digit base))

private theorem HereditaryBaseExpr.valid_at_successor_base {e : HereditaryBaseExpr}
    {base : ℕ} (hvalid : e.Valid base) : e.Valid (base + 1) := by
  induction e with
  | zero => trivial
  | digit n => exact lt_trans hvalid (Nat.lt_succ_self base)
  | add left right leftIH rightIH =>
      exact ⟨leftIH hvalid.1, rightIH hvalid.2⟩
  | mul left right leftIH rightIH =>
      exact ⟨leftIH hvalid.1, rightIH hvalid.2⟩
  | basePow exponent exponentIH => exact exponentIH hvalid

private theorem ordinalPow_omega_two :
    ordinalPow Ordinal.omega0 ((2 : ℕ) : Ordinal) =
      Ordinal.omega0 * Ordinal.omega0 := by
  change ordinalPow Ordinal.omega0 (Order.succ ((1 : ℕ) : Ordinal)) = _
  rw [ordinalPow_succ]
  have hone : ordinalPow Ordinal.omega0 ((1 : ℕ) : Ordinal) =
      Ordinal.omega0 := by
    change ordinalPow Ordinal.omega0 (Order.succ 0) = _
    rw [ordinalPow_succ, ordinalPow_zero]
    simp [ordinalMul]
  rw [hone]
  simp [ordinalMul]

private theorem omega_mul_nat_add_nat_lt_omega_squared (base : ℕ) :
    Ordinal.omega0 * base + base < Ordinal.omega0 * Ordinal.omega0 := by
  have hfirst : Ordinal.omega0 * base + base <
      Ordinal.omega0 * base + Ordinal.omega0 :=
    (add_lt_add_iff_left (Ordinal.omega0 * base)).2
      (Ordinal.natCast_lt_omega0 base)
  rw [← Ordinal.mul_succ] at hfirst
  exact hfirst.trans (mul_lt_mul_of_pos_left
    (show Order.succ (base : Ordinal) < Ordinal.omega0 by
      rw [Order.succ_eq_add_one, ← Nat.cast_one, ← Nat.cast_add]
      exact Ordinal.natCast_lt_omega0 (base + 1)) Ordinal.omega0_pos)

/--
> **Entry**: settheory.googology.goodstein-base-power-two-borrow
> **一句话**: `head + B²` 换底减一后可显式展开为 `head + (B·base + base)`，且展开后的 `ω` 度量严格下降。
> **依赖**: `settheory.googology.goodstein-base-power-one-borrow`、
>   `settheory.googology.goodstein-ordinal-measure`
> **mathlib**: `Ordinal.mul_succ`、`Ordinal.natCast_lt_omega0`、
>   `mul_lt_mul_of_pos_left`
@isnad1 id=and.0h2v.s7.696521583935 from=translated src=- shape=418d3c25 vocab=13744f5a
-/
theorem basePowerTwoTail_goodstein_borrow_descent {base : ℕ}
    (f : BasePowerTwoTailBorrowForm base) :
    f.expression.Valid base ∧
      goodsteinStep base f.expression =
        f.head.eval (base + 1) + ((base + 1) * base + base) ∧
      f.borrowedExpression.Valid (base + 1) ∧
      f.borrowedExpression.eval (base + 1) = goodsteinStep base f.expression ∧
      f.borrowedExpression.omegaValue < f.expression.omegaValue := by
  have htwo_lt_base : 2 < base := f.base_ge_three
  have hone_lt_next : 1 < base + 1 := by omega
  have hsquare : (base + 1) ^ 2 =
      ((base + 1) * base + base) + 1 := by
    simp [pow_two, Nat.add_mul, Nat.mul_add, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm]
  have hhead_next : f.head.Valid (base + 1) :=
    HereditaryBaseExpr.valid_at_successor_base f.head_valid
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨f.head_valid, htwo_lt_base⟩
  · simp only [goodsteinStep, hereditaryBaseChangeValue,
      BasePowerTwoTailBorrowForm.expression, HereditaryBaseExpr.eval]
    rw [hsquare]
    omega
  · exact ⟨hhead_next, ⟨⟨hone_lt_next, Nat.lt_succ_self base⟩,
      Nat.lt_succ_self base⟩⟩
  · simp only [BasePowerTwoTailBorrowForm.borrowedExpression,
      BasePowerTwoTailBorrowForm.expression, goodsteinStep,
      hereditaryBaseChangeValue, HereditaryBaseExpr.eval]
    simp only [pow_one]
    rw [hsquare]
    omega
  · simp only [BasePowerTwoTailBorrowForm.borrowedExpression,
      BasePowerTwoTailBorrowForm.expression, HereditaryBaseExpr.omegaValue,
      ordinalPow_omega_two]
    have hone : ordinalPow Ordinal.omega0 ((1 : ℕ) : Ordinal) =
        Ordinal.omega0 := by
      change ordinalPow Ordinal.omega0 (Order.succ 0) = _
      rw [ordinalPow_succ, ordinalPow_zero]
      simp [ordinalMul]
    rw [hone]
    have htail : ordinalAdd (ordinalMul Ordinal.omega0 base) base =
        Ordinal.omega0 * base + base := by
      rw [show ordinalMul Ordinal.omega0 base =
        Ordinal.omega0 * base by simp [ordinalMul]]
      simp [ordinalAdd]
    rw [htail,
      show ordinalAdd f.head.omegaValue
          (Ordinal.omega0 * base + base) =
          f.head.omegaValue + (Ordinal.omega0 * base + base) by simp [ordinalAdd],
      show ordinalAdd f.head.omegaValue
          (Ordinal.omega0 * Ordinal.omega0) =
          f.head.omegaValue + (Ordinal.omega0 * Ordinal.omega0) by simp [ordinalAdd]]
    exact (add_lt_add_iff_left f.head.omegaValue).2
      (omega_mul_nat_add_nat_lt_omega_squared base)

end

end SandronesLibrary.SetTheory.Googology
