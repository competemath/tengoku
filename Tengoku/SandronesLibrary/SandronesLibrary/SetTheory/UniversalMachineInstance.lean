/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.SetTheory.PartialComputability
import Tengoku.SandronesLibrary.SandronesLibrary.SetTheory.BinaryMachineCoding
import Tengoku.Seed.Data.Nat.Pairing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# SetTheory / UniversalMachineInstance —— 现有机器模型的通用 runner 实例

`PartialComputability` 只用结构字段声明了通用解释器应满足的规格 `UniversalNatInterpreter`，
但没有给出实例。本文件为现有 `NatProgram`（状态数 + 有限机器表）**构造一个真实 inhabitant**：
用自然数配对把状态偏移与固定状态数机器代码拼成一个自然数编码，解码后调用现有
`interpretWithin` 执行。

这里的编码和解码都依赖 mathlib 的非可计算有限枚举 `Finite.equivFin`，因此是 `noncomputable`
的元层 runner，而不是本库 `NatProgram` 自身；它不产生自解释器、停机判定算法或不可判定性结论。
-/

namespace SandronesLibrary.SetTheory.UniversalMachineInstance

open PartialComputability
open BinaryMachineCoding
open ComputabilityFoundations
open GoogologyComputability

/-- 越界代码的兜底程序：状态偏移零，单状态且立即停机。-/
private def fallbackNatProgram : NatProgram :=
  ⟨0, fun _ _ => ⟨false, HeadMove.right, none⟩⟩

/--
> **Entry**: settheory.computability.universal-machine-instance
> **一句话**: 为现有 `NatProgram` 构造通用 runner：将程序经 `Nat.pair` 编码为自然数，
> 解码回程序后调用本库解释器，从而给出 `UniversalNatInterpreter` 规格的一个真实实例。
> **依赖**: `settheory.computability.universal-interpreter-spec`,
> `settheory.computability.binary-machine-coding`
> **mathlib**: `Nat.pair`, `Nat.unpair`, `Function.Injective`-/
noncomputable def encodeNatProgram (program : NatProgram) : ℕ :=
  Nat.pair program.stateOffset (encodeMachine program.machine).val

/-- 按状态偏移与代码索引解码机器，再组装为程序；越界时返回兜底程序。-/
private noncomputable def decodeProgramPair (offset index : ℕ) : NatProgram :=
  match decodeMachineNat offset index with
  | some machine => ⟨offset, machine⟩
  | none => fallbackNatProgram

/-- 通用解码：先拆自然数配对，再按偏移解码机器。-/
noncomputable def decodeNatProgram (code : ℕ) : NatProgram :=
  decodeProgramPair code.unpair.1 code.unpair.2

/-- 配对拆分后解码得到原程序，所以解码是编码的左逆。
@isnad1 id=eq.0h2v.s7.26ae08c11a65 from=translated src=- shape=72ce6bd8 vocab=70682aaf
-/
theorem decodeNatProgram_pair (offset : ℕ) (machine : BinaryMachine (offset + 1)) :
    decodeNatProgram (Nat.pair offset (encodeMachine machine).val) = ⟨offset, machine⟩ := by
  have h : Nat.unpair (Nat.pair offset (encodeMachine machine).val) =
      (offset, (encodeMachine machine).val) := Nat.unpair_pair _ _
  unfold decodeNatProgram
  rw [h]
  simp only [decodeProgramPair, decodeMachineNat_encodeMachine]

/-- 先编码再解码得到原程序。
@isnad1 id=eq.0h1v.s3.4b17a33bf730 from=translated src=- shape=47dcad53 vocab=28e951c8
-/
theorem decodeNatProgram_encodeNatProgram (program : NatProgram) :
    decodeNatProgram (encodeNatProgram program) = program := by
  obtain ⟨offset, machine⟩ := program
  exact decodeNatProgram_pair offset machine

/-- 编码是单射：它由自然数配对与机器代码的有限编码复合而成。
@isnad1 id=injectiv.0h0v.s2.f0d8d1c42c1d from=translated src=- shape=54c8eceb vocab=11a7a40a
-/
theorem encodeNatProgram_injective : Function.Injective encodeNatProgram := by
  intro p q hp
  rw [← decodeNatProgram_encodeNatProgram p, hp, decodeNatProgram_encodeNatProgram q]

/-- 通用解释器实例：编码、单射、按解码程序求值，以及逐燃料模拟定律。-/
noncomputable def universalNatInterpreter : UniversalNatInterpreter where
  encode := encodeNatProgram
  encode_injective := encodeNatProgram_injective
  eval := fun code fuel input => interpretWithin (decodeNatProgram code) fuel input
  simulate := by
    intro program fuel input
    simp only [decodeNatProgram_encodeNatProgram]

/-- 实例在每个编码后的程序上产生的输出关系，与原程序的停机输出关系完全一致。
@isnad1 id=iff.0h3v.s4.b0863ddc7040 from=translated src=- shape=5e5d20f5 vocab=0dcbc4c6
-/
theorem universalNatInterpreter_outputs_encode_iff (program : NatProgram)
    (input output : ℕ) :
    universalNatInterpreter.Outputs (encodeNatProgram program) input output ↔
      ProgramOutput program input output :=
  universal_outputs_encode_iff universalNatInterpreter program input output

end SandronesLibrary.SetTheory.UniversalMachineInstance
