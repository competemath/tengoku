/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.SetTheory.PartialComputability

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# SetTheory / ComputabilityDiagonal —— 条件式自应用对角矛盾

本文件冻结自然数配对、可由程序实现的通用解释器，以及判定器到翻转程序的编译闭包规格。在这些
尚待构造的接口被显式给定时，证明自应用停机谓词不可能由程序总判定。

结论是条件式的；本文件没有无条件证明现有机器模型的停机不可判定，也没有讨论 Busy Beaver
不可计算性。
-/

namespace SandronesLibrary.SetTheory.ComputabilityDiagonal

open ComputabilityFoundations PartialComputability

/--
自然数配对编码的教材规格：`pair` 把两个自然数组成一个代码，两个投影必须在配对代码上还原输入。-/
structure PairingCode where
  pair : ℕ → ℕ → ℕ
  left : ℕ → ℕ
  right : ℕ → ℕ
  left_pair : ∀ x y, left (pair x y) = x
  right_pair : ∀ x y, right (pair x y) = y

/-- 配对函数由两个投影可还原，因而对有序对是单射。
@isnad1 id=injectiv.0h1v.s4.ccdea4146fac from=translated src=- shape=43f219db vocab=b96ecb9d
-/
theorem PairingCode.pair_injective (coding : PairingCode) :
    Function.Injective (fun p : ℕ × ℕ => coding.pair p.1 p.2) := by
  rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ hp
  change coding.pair x₁ y₁ = coding.pair x₂ y₂ at hp
  have hx : x₁ = x₂ := by
    rw [← coding.left_pair x₁ y₁, ← coding.left_pair x₂ y₂, hp]
  have hy : y₁ = y₂ := by
    rw [← coding.right_pair x₁ y₁, ← coding.right_pair x₂ y₂, hp]
  exact Prod.ext hx hy

/--
> **Entry**: settheory.computability.pairing-code
> **一句话**: 自然数配对编码必须能由两个投影恢复左右分量，因此可以安全承载“程序代码、输入”。
> **依赖**: `settheory.computability.universal-interpreter-spec`
> **mathlib**: `Function.Injective`
@isnad1 id=eq.0h3v.s4.3d719d1745b8 from=translated src=- shape=d1831fa2 vocab=c7f8d22d
-/
theorem PairingCode.recover (coding : PairingCode) (x y : ℕ) :
    (coding.left (coding.pair x y), coding.right (coding.pair x y)) = (x, y) := by
  rw [coding.left_pair, coding.right_pair]

/--
可执行通用解释器的加强规格。除了抽象通用解释器，还必须给出配对编码和一份 `runner` 程序；
`runner_spec` 要求该程序在配对输入 `(code,input)` 上的最终输出，恰好等于抽象解释器的输出。-/
structure ExecutableUniversalInterpreter where
  universal : UniversalNatInterpreter
  coding : PairingCode
  runner : NatProgram
  runner_spec : ∀ code input output,
    ProgramOutput runner (coding.pair code input) output ↔
      universal.Outputs code input output

/-- 编码程序经通用 runner 运行，与该程序自身运行具有相同的最终输出关系。
@isnad1 id=iff.0h4v.s4.819032197f24 from=translated src=- shape=58ba5746 vocab=ced5fca6
-/
theorem runner_encode_iff (executable : ExecutableUniversalInterpreter)
    (program : NatProgram) (input output : ℕ) :
    ProgramOutput executable.runner
        (executable.coding.pair (executable.universal.encode program) input) output ↔
      ProgramOutput program input output := by
  rw [executable.runner_spec, universal_outputs_encode_iff]

/--
> **Entry**: settheory.computability.executable-universal-spec
> **一句话**: 通用解释器若可由本机器模型实现，必须有一台 runner 在配对代码输入上精确模拟原程序。
> **依赖**: `settheory.computability.pairing-code`
> **mathlib**: 无（显式实现门）
@isnad1 id=iff.0h4v.s4.819032197f24 from=translated src=- shape=58ba5746 vocab=ced5fca6
-/
theorem executable_runner_specification (executable : ExecutableUniversalInterpreter) :
    ∀ program input output,
      ProgramOutput executable.runner
          (executable.coding.pair (executable.universal.encode program) input) output ↔
        ProgramOutput program input output := by
  exact runner_encode_iff executable

/-- 程序代码在以自身代码为输入时，是否由通用解释器产生某个输出。-/
def SelfHalts (universal : UniversalNatInterpreter) (code : ℕ) : Prop :=
  ∃ output, universal.Outputs code code output

/--
对角翻转编译闭包。若 `decider` 总判定 `SelfHalts`，`flip decider` 必须在输入 `code` 上恰好于
`SelfHalts code` 为假时停机，并且唯一允许的输出是零。

这是一项待实现的编译器规格，不代表这样的闭包已经为当前机器模型构造出来。-/
structure DiagonalFlipClosure (universal : UniversalNatInterpreter) where
  flip : NatProgram → NatProgram
  flip_spec : ∀ decider,
    DecidesPredicate decider (SelfHalts universal) →
      ∀ code output,
        ProgramOutput (flip decider) code output ↔
          output = 0 ∧ ¬ SelfHalts universal code

/--
> **Entry**: settheory.computability.conditional-diagonal
> **一句话**: 若通用模拟和对角翻转编译闭包都已实现，则不存在总判定程序判断代码在自身输入上是否停机。
> **依赖**: `settheory.computability.executable-universal-spec`,
> `settheory.computability.machine-decidable`
> **mathlib**: 无（条件式自应用对角论证）
@isnad1 id=not.0h2v.s4.0939879e03c6 from=translated src=- shape=793c8ec7 vocab=e013ecdf
-/
theorem no_program_decides_selfHalts
    (executable : ExecutableUniversalInterpreter)
    (closure : DiagonalFlipClosure executable.universal) :
    ¬∃ decider, DecidesPredicate decider (SelfHalts executable.universal) := by
  rintro ⟨decider, hdecider⟩
  let diagonal := closure.flip decider
  let diagonalCode := executable.universal.encode diagonal
  have hself_iff : SelfHalts executable.universal diagonalCode ↔
      ∃ output, ProgramOutput diagonal diagonalCode output := by
    unfold SelfHalts diagonalCode diagonal
    constructor <;> rintro ⟨output, hout⟩ <;> refine ⟨output, ?_⟩
    · exact (universal_outputs_encode_iff executable.universal
        (closure.flip decider) diagonalCode output).mp hout
    · exact (universal_outputs_encode_iff executable.universal
        (closure.flip decider) diagonalCode output).mpr hout
  have hdiagonal_iff : (∃ output, ProgramOutput diagonal diagonalCode output) ↔
      ¬SelfHalts executable.universal diagonalCode := by
    constructor
    · rintro ⟨output, hout⟩
      exact ((closure.flip_spec decider hdecider diagonalCode output).mp hout).2
    · intro hnot
      exact ⟨0, (closure.flip_spec decider hdecider diagonalCode 0).mpr ⟨rfl, hnot⟩⟩
  by_cases hself : SelfHalts executable.universal diagonalCode
  · exact (hdiagonal_iff.mp (hself_iff.mp hself)) hself
  · exact hself (hself_iff.mpr (hdiagonal_iff.mpr hself))

end SandronesLibrary.SetTheory.ComputabilityDiagonal
