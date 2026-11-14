/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.SetTheory.HereditaryNatEncodingOrder

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # 规范 Goodstein 状态

本文件去掉 Goodstein 状态中任意挑选表达式的自由：状态携带的表达式按定义就是其数值在当前底数
下的遗传自然数编码。换底并减一之后，再在后继底数下重新编码所得数值。

本文件刻意不声称无条件序数下降。它把尚缺的正规化桥明确命名，并且只在给出这条桥和正值前提时
证明下降。
-/

namespace SandronesLibrary.SetTheory.Googology

open SandronesLibrary.SetTheory.Ordinal

noncomputable section

/-
证明清单：
1. 规范表达式从 `hereditaryNatEncode_valid_eval` 继承合法性和求值证书。
2. 后继底数状态在新底数下继承同样两份证书。
3. 显式提供尚缺的正规化桥后，由严格单调性推出条件式序数下降。
-/

/--
> **Entry**: settheory.googology.canonical-goodstein-state
> **一句话**: 规范 Goodstein 状态由底数和值唯一生成遗传编码；一步换底减一后，会在新底数下重新生成合法且求值正确的规范编码。
> **依赖**: `settheory.googology.hereditary-natural-encoding`、
> `settheory.googology.hereditary-natural-encoding-strict-order`
> **mathlib**: 无（本库显式状态与编码器）

规范 Goodstein 状态只记录底数和值；遗传表达式由本库固定编码器计算，而不是作为额外证书任意选择。-/
structure CanonicalGoodsteinState where
  base : ℕ
  base_ge_two : 2 ≤ base
  value : ℕ

/-- 规范状态所指定的遗传表达式。-/
def CanonicalGoodsteinState.expression (s : CanonicalGoodsteinState) :
    HereditaryBaseExpr :=
  hereditaryNatEncode s.base s.base_ge_two s.value

theorem CanonicalGoodsteinState.expression_valid (s : CanonicalGoodsteinState) :
    s.expression.Valid s.base :=
  (hereditaryNatEncode_valid_eval s.base s.base_ge_two s.value).1

theorem CanonicalGoodsteinState.expression_evaluates (s : CanonicalGoodsteinState) :
    s.expression.eval s.base = s.value :=
  (hereditaryNatEncode_valid_eval s.base s.base_ge_two s.value).2

/-- 升高底数，在新底数下求旧规范树的值并减一，再于新底数下规范编码所得自然数。-/
def canonicalGoodsteinStep (s : CanonicalGoodsteinState) : CanonicalGoodsteinState where
  base := s.base + 1
  base_ge_two := s.base_ge_two.trans (Nat.le_succ s.base)
  value := goodsteinStep s.base s.expression

/-- 规范一步的新底数、表达式合法性与求值正确性规格。-/
theorem canonicalGoodsteinStep_specification (s : CanonicalGoodsteinState) :
    (canonicalGoodsteinStep s).base = s.base + 1 ∧
      (canonicalGoodsteinStep s).expression.Valid (s.base + 1) ∧
      (canonicalGoodsteinStep s).expression.eval (s.base + 1) =
        goodsteinStep s.base s.expression := by
  exact ⟨rfl, (canonicalGoodsteinStep s).expression_valid,
    (canonicalGoodsteinStep s).expression_evaluates⟩

/-- 规范状态在固定宇宙中的序数度量。-/
def CanonicalGoodsteinState.ordinalMeasure (s : CanonicalGoodsteinState) : Ordinal.{0} :=
  s.expression.omegaValue

/-- 在后继底数下重新编码旧树于该底数的求值，再于 `ω` 处读取新树；这单独刻画换底的正规化一侧。-/
def CanonicalGoodsteinState.baseChangeReencodingMeasure
    (s : CanonicalGoodsteinState) : Ordinal.{0} :=
  (hereditaryNatEncode (s.base + 1) (s.base_ge_two.trans (Nat.le_succ s.base))
    (s.expression.eval (s.base + 1))).omegaValue

/-- 无条件一步序数下降仍需要的精确正规化桥；这是一个命名义务，不是本模块已经证明的定理。-/
def CanonicalBaseChangeOmegaCompatible (s : CanonicalGoodsteinState) : Prop :=
  s.baseChangeReencodingMeasure = s.ordinalMeasure

/-- 一旦换底正规化保持旧序数树，从正的新底数值减一便严格降低序数度量。兼容性前提被刻意保留
在定理陈述中，因为它尚未对所有规范状态得到证明。-/
theorem canonicalGoodsteinStep_omega_lt_of_compatible
    (s : CanonicalGoodsteinState)
    (hpositive : 0 < s.expression.eval (s.base + 1))
    (hcompatible : CanonicalBaseChangeOmegaCompatible s) :
    (canonicalGoodsteinStep s).ordinalMeasure < s.ordinalMeasure := by
  have hstep : goodsteinStep s.base s.expression < s.expression.eval (s.base + 1) := by
    simp only [goodsteinStep, hereditaryBaseChangeValue]
    exact Nat.sub_lt hpositive (by decide)
  have hbase : 2 ≤ s.base + 1 := s.base_ge_two.trans (Nat.le_succ s.base)
  have hmono := hereditaryNatEncode_omega_strictMono (s.base + 1) hbase hstep
  change (hereditaryNatEncode (s.base + 1) _
      (goodsteinStep s.base s.expression)).omegaValue < s.expression.omegaValue
  exact hmono.trans_le hcompatible.le

end
end SandronesLibrary.SetTheory.Googology
