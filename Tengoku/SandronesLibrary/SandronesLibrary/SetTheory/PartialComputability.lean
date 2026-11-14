/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.SetTheory.ComputabilityFoundations

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# SetTheory / PartialComputability —— 部分函数与通用解释器抽象规格

部分自然数函数用单值的输入输出关系表示：某个输入没有相关输出就表示发散。现有机器解释器诱导
具体的停机输出关系；本文件证明它单值，并把总可计算性和谓词判定嵌入这套关系语言。

最后只声明通用解释器要满足的结构字段，不构造实例，不声称已有机器能够自解释。
-/

namespace SandronesLibrary.SetTheory.PartialComputability

open ComputabilityFoundations

/-- 程序在某个有限时刻停机并输出给定自然数。-/
def ProgramOutput (program : NatProgram) (input output : ℕ) : Prop :=
  ∃ fuel, interpretWithin program fuel input = some output

/-- 二元关系是单值的：同一输入至多对应一个输出。-/
def SingleValued (graph : ℕ → ℕ → Prop) : Prop :=
  ∀ ⦃input x y⦄, graph input x → graph input y → x = y

/-- 程序计算部分函数图像：关系成立恰好意味着程序最终停机并给出该输出。-/
def ComputesPartialFunction (program : NatProgram) (graph : ℕ → ℕ → Prop) : Prop :=
  ∀ input output, graph input output ↔ ProgramOutput program input output

/-- 单值关系部分可计算，当且仅当某份有限程序精确实现其停机输出关系。-/
def PartialNatComputable (graph : ℕ → ℕ → Prop) : Prop :=
  SingleValued graph ∧ ∃ program, ComputesPartialFunction program graph

/-- 具体确定程序的停机输出关系必定单值。
@isnad1 id=singleva.0h1v.s2.0335131e1ca2 from=translated src=- shape=76a08d12 vocab=82c8edd9
-/
theorem programOutput_singleValued (program : NatProgram) :
    SingleValued (ProgramOutput program) := by
  intro input x y hx hy
  rcases hx with ⟨fuelX, houtX⟩
  rcases hy with ⟨fuelY, houtY⟩
  exact interpretWithin_output_unique houtX houtY

/-- 总函数 `f` 对应的图像关系。-/
def totalFunctionGraph (f : ℕ → ℕ) (input output : ℕ) : Prop :=
  output = f input

/--
> **Entry**: settheory.computability.partial-nat-computable
> **一句话**: 部分可计算函数是由程序停机输出精确实现的单值输入输出关系，未停机输入没有输出。
> **依赖**: `settheory.computability.nat-computable`
> **mathlib**: 无（本库解释器诱导的关系）
@isnad1 id=partialn.1h1v.s3.e8f76a68240c from=translated src=- shape=aef97f5f vocab=014f39fe
-/
theorem natComputable_implies_partial {f : ℕ → ℕ} :
    NatComputable f → PartialNatComputable (totalFunctionGraph f) := by
  rintro ⟨program, hprogram⟩
  refine ⟨?_, program, ?_⟩
  · intro input x y hx hy
    exact hx.trans hy.symm
  · intro input output
    constructor
    · intro hout
      subst output
      exact hprogram input
    · rintro ⟨fuel, hout⟩
      rcases hprogram input with ⟨correctFuel, hcorrect⟩
      exact interpretWithin_output_unique hout hcorrect

/-- 谓词的零一关系，不要求在定义处选择真假分支。-/
def PredicateCharacteristicGraph (P : ℕ → Prop) (input output : ℕ) : Prop :=
  (P input ∧ output = 1) ∨ (¬P input ∧ output = 0)

/-- 一份程序判定 `P`，当且仅当它精确计算 `P` 的零一部分函数图像。
@isnad1 id=iff.0h2v.s3.4d930b470bcb from=translated src=- shape=ec0c023b vocab=d99225a4
-/
theorem decidesPredicate_iff_computesPartial (program : NatProgram) (P : ℕ → Prop) :
    DecidesPredicate program P ↔
      ComputesPartialFunction program (PredicateCharacteristicGraph P) := by
  constructor
  · intro hdec input output
    constructor
    · rintro (⟨hP, rfl⟩ | ⟨hP, rfl⟩)
      · rcases hdec input with ⟨_, hone⟩ | ⟨hnot, _⟩
        · exact hone
        · exact False.elim (hnot hP)
      · rcases hdec input with ⟨hyes, _⟩ | ⟨_, hzero⟩
        · exact False.elim (hP hyes)
        · exact hzero
    · intro hout
      rcases hdec input with ⟨hP, hone⟩ | ⟨hP, hzero⟩
      · left
        refine ⟨hP, ?_⟩
        exact programOutput_singleValued program hout hone
      · right
        refine ⟨hP, ?_⟩
        exact programOutput_singleValued program hout hzero
  · intro hcompute input
    by_cases hP : P input
    · left
      exact ⟨hP, (hcompute input 1).mp (Or.inl ⟨hP, rfl⟩)⟩
    · right
      exact ⟨hP, (hcompute input 0).mp (Or.inr ⟨hP, rfl⟩)⟩

/--
通用自然数解释器所需的抽象数据。`encode` 把每份程序编码成自然数；`eval` 按编码、燃料和输入
运行；`encode_injective` 防止不同程序共用编码；`simulate` 要求编码后的逐燃料行为与现有
`interpretWithin` 完全一致。

这是规格结构，不代表本库已经构造出一个 inhabitant。-/
structure UniversalNatInterpreter where
  encode : NatProgram → ℕ
  encode_injective : Function.Injective encode
  eval : ℕ → ℕ → ℕ → Option ℕ
  simulate : ∀ program fuel input,
    eval (encode program) fuel input = interpretWithin program fuel input

/-- 通用解释器在某编码和输入上最终产生输出的关系。-/
def UniversalNatInterpreter.Outputs (universal : UniversalNatInterpreter)
    (code input output : ℕ) : Prop :=
  ∃ fuel, universal.eval code fuel input = some output

/--
> **Entry**: settheory.computability.universal-interpreter-spec
> **一句话**: 通用解释器必须为程序提供单射自然数编码，并逐燃料精确模拟本库现有解释器。
> **依赖**: `settheory.computability.partial-nat-computable`
> **mathlib**: `Function.Injective`
@isnad1 id=iff.0h4v.s4.a470cbd87477 from=translated src=- shape=9176bff4 vocab=dc417cf0
-/
theorem universal_outputs_encode_iff (universal : UniversalNatInterpreter)
    (program : NatProgram) (input output : ℕ) :
    universal.Outputs (universal.encode program) input output ↔
      ProgramOutput program input output := by
  constructor <;> rintro ⟨fuel, hout⟩ <;> refine ⟨fuel, ?_⟩
  · rwa [universal.simulate] at hout
  · rwa [universal.simulate]

end SandronesLibrary.SetTheory.PartialComputability
