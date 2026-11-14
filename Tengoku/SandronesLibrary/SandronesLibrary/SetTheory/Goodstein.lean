/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.SetTheory.Googology
import Tengoku.SandronesLibrary.SandronesLibrary.SetTheory.Ordinal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# SetTheory / Goodstein —— 带表示证书的 Goodstein 状态

本文件不假设已经实现“任意自然数的唯一遗传正规形”。每个状态显式携带底数、数值、
遗传表达式及其合法性与求值证书。因此一步迁移不会在“减一后如何重新编码”处偷换概念。
-/

namespace SandronesLibrary.SetTheory.Googology

open SandronesLibrary.SetTheory.Ordinal

noncomputable section

/--
Goodstein 过程的带证书状态。表达式在当前底数下必须合法，且求值必须等于记录的自然数。-/
structure CertifiedGoodsteinState where
  base : ℕ
  base_ge_two : 2 ≤ base
  value : ℕ
  expression : HereditaryBaseExpr
  expression_valid : expression.Valid base
  expression_evaluates : expression.eval base = value

/--
> **Entry**: settheory.googology.goodstein-certified-state
> **一句话**: Goodstein 状态同时保存自然数值与对该数值的合法遗传基表示证书。
> **依赖**: `settheory.googology.hereditary-base`
> **mathlib**: 无（本库显式证书结构）-/
theorem certifiedGoodsteinState_specification (s : CertifiedGoodsteinState) :
    2 ≤ s.base ∧ s.expression.Valid s.base ∧
      s.expression.eval s.base = s.value := by
  exact ⟨s.base_ge_two, s.expression_valid, s.expression_evaluates⟩

/--
从 `s` 到 `t` 的重编码单步。目标状态自带合法表示证书；关系只额外要求底数加一，
以及目标数值确实是源表达式“换底后减一”的结果。-/
def GoodsteinReencodingStep (s t : CertifiedGoodsteinState) : Prop :=
  t.base = s.base + 1 ∧ t.value = goodsteinStep s.base s.expression

/-- 一条带证书的 Goodstein 序列，就是相邻状态每次都满足重编码单步关系。-/
def IsCertifiedGoodsteinSequence (states : ℕ → CertifiedGoodsteinState) : Prop :=
  ∀ n, GoodsteinReencodingStep (states n) (states (n + 1))

/--
> **Entry**: settheory.googology.goodstein-reencoding
> **一句话**: 完整 Goodstein 单步不仅换底减一，还要为新数值携带下一底数下的新合法表示。
> **依赖**: `settheory.googology.goodstein-certified-state`、`settheory.googology.goodstein-step`
> **mathlib**: 无（本库显式迁移关系）-/
theorem goodsteinReencodingStep_specification {s t : CertifiedGoodsteinState}
    (h : GoodsteinReencodingStep s t) :
    t.base = s.base + 1 ∧
      t.expression.eval t.base = goodsteinStep s.base s.expression := by
  exact ⟨h.1, t.expression_evaluates.trans h.2⟩

/--
> **Entry**: settheory.googology.goodstein-sequence
> **一句话**: 带证书 Goodstein 序列把“每步重编码”表达为所有相邻状态都满足同一迁移关系。
> **依赖**: `settheory.googology.goodstein-reencoding`
> **mathlib**: 无-/
theorem certifiedGoodsteinSequence_step {states : ℕ → CertifiedGoodsteinState}
    (h : IsCertifiedGoodsteinSequence states) (n : ℕ) :
    (states (n + 1)).base = (states n).base + 1 ∧
      (states (n + 1)).value = goodsteinStep (states n).base (states n).expression := by
  exact h n

/-- 把遗传表达式中的有限底数统一换成 `ω`，而数字、加法和乘法的树结构保持不变。-/
def HereditaryBaseExpr.omegaValue : HereditaryBaseExpr → Ordinal
  | .zero => 0
  | .digit n => n
  | .add left right => ordinalAdd left.omegaValue right.omegaValue
  | .mul left right => ordinalMul left.omegaValue right.omegaValue
  | .basePow exponent => ordinalPow Ordinal.omega0 exponent.omegaValue

/-- 一个带证书状态的序数度量，由它当前携带的遗传表达式决定。-/
def CertifiedGoodsteinState.ordinalMeasure (s : CertifiedGoodsteinState) : Ordinal :=
  s.expression.omegaValue

/--
> **Entry**: settheory.googology.goodstein-ordinal-measure
> **一句话**: 将遗传表达式中每个底数位置换成 `ω`，得到后续下降论证所需的序数度量。
> **依赖**: `settheory.googology.goodstein-certified-state`、`settheory.ordinal.exponentiation`
> **mathlib**: `Ordinal.omega0`-/
theorem omegaValue_equations (left right exponent : HereditaryBaseExpr) (n : ℕ) :
    HereditaryBaseExpr.zero.omegaValue = 0 ∧
      (HereditaryBaseExpr.digit n).omegaValue = n ∧
      (HereditaryBaseExpr.add left right).omegaValue =
        ordinalAdd left.omegaValue right.omegaValue ∧
      (HereditaryBaseExpr.mul left right).omegaValue =
        ordinalMul left.omegaValue right.omegaValue ∧
      (HereditaryBaseExpr.basePow exponent).omegaValue =
        ordinalPow Ordinal.omega0 exponent.omegaValue := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem equal_expressions_have_equal_ordinalMeasure {s t : CertifiedGoodsteinState}
    (h : s.expression = t.expression) : s.ordinalMeasure = t.ordinalMeasure := by
  simp only [CertifiedGoodsteinState.ordinalMeasure, h]

end

end SandronesLibrary.SetTheory.Googology
