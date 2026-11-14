/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.SetTheory.Goodstein

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# SetTheory / GoodsteinDescent —— 数字正规形的下降桥

本文件只处理表示为单个非零数字的 Goodstein 状态。在这个子类中，换底不改变
自然数值，减一后仍有显式正规表示，因而可以严格证明 `ω` 度量下降。这不是任意遗传基
表示的借位引理，更不是 Goodstein 定理。
-/

namespace SandronesLibrary.SetTheory.Googology

open SandronesLibrary.SetTheory.Ordinal

noncomputable section

/--
底数 `base` 下的非零数字正规形。`positive` 排除无法严格下降的零，`valid` 记录
该数字确实小于底数。-/
structure PositiveDigitNormalForm (base : ℕ) where
  digit : ℕ
  positive : 0 < digit
  valid : digit < base

/-- 把数字正规形嵌入通用遗传基表达式。-/
def PositiveDigitNormalForm.expression {base : ℕ}
    (d : PositiveDigitNormalForm base) : HereditaryBaseExpr :=
  .digit d.digit

/-- 非零数字减一后的显式重编码。-/
def PositiveDigitNormalForm.predecessorExpression {base : ℕ}
    (d : PositiveDigitNormalForm base) : HereditaryBaseExpr :=
  .digit (d.digit - 1)

/--
> **Entry**: settheory.googology.goodstein-positive-digit-descent
> **一句话**: 非零数字正规形换底减一后可显式重编码，且其 `ω` 度量严格下降。
> **依赖**: `settheory.googology.goodstein-step`、`settheory.googology.goodstein-ordinal-measure`
> **mathlib**: `Nat.sub_one_lt`
@isnad1 id=and.0h2v.s6.febce02af5b7 from=translated src=- shape=6a896b29 vocab=9a83bd61
-/
theorem positiveDigit_goodstein_descent {base : ℕ}
    (d : PositiveDigitNormalForm base) :
    goodsteinStep base d.expression = d.digit - 1 ∧
      d.predecessorExpression.Valid (base + 1) ∧
      d.predecessorExpression.eval (base + 1) = goodsteinStep base d.expression ∧
      d.predecessorExpression.omegaValue < d.expression.omegaValue := by
  have hpred_lt : d.digit - 1 < d.digit :=
    Nat.sub_one_lt (Nat.ne_of_gt d.positive)
  refine ⟨by simp [goodsteinStep, hereditaryBaseChangeValue,
      PositiveDigitNormalForm.expression, HereditaryBaseExpr.eval], ?_, ?_, ?_⟩
  · simp only [PositiveDigitNormalForm.predecessorExpression, HereditaryBaseExpr.Valid]
    exact lt_trans hpred_lt (lt_trans d.valid (Nat.lt_succ_self base))
  · simp [PositiveDigitNormalForm.predecessorExpression, HereditaryBaseExpr.eval,
      goodsteinStep, hereditaryBaseChangeValue, PositiveDigitNormalForm.expression]
  · simp only [PositiveDigitNormalForm.predecessorExpression,
      PositiveDigitNormalForm.expression, HereditaryBaseExpr.omegaValue]
    exact_mod_cast hpred_lt

end

end SandronesLibrary.SetTheory.Googology
