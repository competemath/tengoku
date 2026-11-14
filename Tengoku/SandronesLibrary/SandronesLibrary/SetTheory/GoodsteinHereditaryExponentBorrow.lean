/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.SetTheory.GoodsteinFinitePowerBorrow

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# SetTheory / GoodsteinHereditaryExponentBorrow —— 底数自身作为指数

本文件从数字指数 `k` 推进到真正嵌套的指数族 `B^(B¹)`。它不是
一个固定数值算例：底数和前缀均为参数。升底后，内层 `B¹` 的值是
`q=base+1`，因而复用有限幂递归展开来编码 `q^q-1`。
-/

namespace SandronesLibrary.SetTheory.Googology

open SandronesLibrary.SetTheory.Ordinal

noncomputable section

/--
遗传指数 `B¹` 的带证书正规子类。底数至少为二，所以内层指数数字
`1` 在当前底数下合法。-/
structure BaseExponentOneNormalForm (base : ℕ) where
  base_ge_two : 2 ≤ base

/-- 指数表达式 `B¹`；它将作为另一个底数幂的指数子树。-/
def BaseExponentOneNormalForm.expression {base : ℕ}
    (_ : BaseExponentOneNormalForm base) : HereditaryBaseExpr :=
  .basePow (.digit 1)

/--
指数协议的三项基本事实：它在原底数下合法，在新底数下求值为
`base+1`，并且把底数换成 `ω` 后的序数值为 `ω`。
@isnad1 id=and.1h1v.s5.f9a7cca791bb from=translated src=- shape=d07d1b9c vocab=4a31b1c7
-/
theorem BaseExponentOneNormalForm.protocol {base : ℕ}
    (e : BaseExponentOneNormalForm base) :
    e.expression.Valid base ∧
      e.expression.eval (base + 1) = base + 1 ∧
      e.expression.omegaValue = Ordinal.omega0 := by
  have hone_lt_base : 1 < base := lt_of_lt_of_le Nat.one_lt_two e.base_ge_two
  refine ⟨hone_lt_base, by simp [BaseExponentOneNormalForm.expression,
    HereditaryBaseExpr.eval], ?_⟩
  simp only [BaseExponentOneNormalForm.expression, HereditaryBaseExpr.omegaValue]
  change ordinalPow Ordinal.omega0 (Order.succ 0) = Ordinal.omega0
  rw [ordinalPow_succ, ordinalPow_zero]
  simp [ordinalMul]

/--
外层借位形 `head + B^(B¹)`。指数不是数字叶子，而是一棵包含底数幂的
遗传表达式。-/
structure HereditaryBaseExponentTailBorrowForm (base : ℕ) where
  exponent : BaseExponentOneNormalForm base
  head : HereditaryBaseExpr
  head_valid : head.Valid base

/-- 借位前的真正嵌套表达式 `head + B^(B¹)`。-/
def HereditaryBaseExponentTailBorrowForm.expression {base : ℕ}
    (f : HereditaryBaseExponentTailBorrowForm base) : HereditaryBaseExpr :=
  .add f.head (.basePow f.exponent.expression)

/--
升底后内层指数求值为 `base+1`，因此用有限幂递归展开编码
`(base+1)^(base+1)-1`。-/
def HereditaryBaseExponentTailBorrowForm.borrowedExpression {base : ℕ}
    (f : HereditaryBaseExponentTailBorrowForm base) : HereditaryBaseExpr :=
  .add f.head (finitePowerBorrowExpansion base (base + 1))

end

end SandronesLibrary.SetTheory.Googology
