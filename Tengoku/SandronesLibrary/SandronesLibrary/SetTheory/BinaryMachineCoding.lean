/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.SetTheory.GoogologyComputability

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# SetTheory / BinaryMachineCoding —— 固定状态数机器的有限代码

固定 `n` 后，`BinaryMachine (n+1)` 是有限类型。本文件用其规范 `Fintype.equivFin` 枚举建立本库
机器代码、编码、解码和自然数边界检查接口。

该有限枚举依赖 mathlib 的非可计算规范等价；它只冻结定义层索引，不是通用机器或可执行编译器。
-/

namespace SandronesLibrary.SetTheory.BinaryMachineCoding

open GoogologyComputability

/-- 固定 `n+1` 个工作状态时，机器代码是机器总数范围内的有限索引。-/
abbrev MachineCode (n : ℕ) := Fin (Fintype.card (BinaryMachine (n + 1)))

/-- 由 mathlib 的规范有限枚举把机器编码成有限索引。-/
noncomputable def encodeMachine (machine : BinaryMachine (n + 1)) : MachineCode n :=
  Fintype.equivFin _ machine

/-- 由同一个有限等价把合法索引解码回机器。-/
noncomputable def decodeMachine (code : MachineCode n) : BinaryMachine (n + 1) :=
  (Fintype.equivFin _).symm code

/-- 先编码再解码得到原机器。
@isnad1 id=eq.0h2v.s5.866b8f599353 from=translated src=- shape=75b65a1b vocab=745caa51
-/
theorem decodeMachine_encodeMachine (machine : BinaryMachine (n + 1)) :
    decodeMachine (encodeMachine machine) = machine := by
  exact Equiv.symm_apply_apply (Fintype.equivFin _) machine

/-- 先解码再编码得到原合法代码。
@isnad1 id=eq.0h2v.s3.f99089bd10ad from=translated src=- shape=6ddf6d3e vocab=33c03f8e
-/
theorem encodeMachine_decodeMachine (code : MachineCode n) :
    encodeMachine (decodeMachine code) = code := by
  exact Equiv.apply_symm_apply (Fintype.equivFin _) code

/-- 每台固定状态数机器都由唯一一个 `MachineCode` 解码得到。
@isnad1 id=existsun.0h2v.s5.5cf0216a09a7 from=translated src=- shape=6ddbdea2 vocab=cf045187
-/
theorem exists_unique_machineCode (machine : BinaryMachine (n + 1)) :
    ∃! code : MachineCode n, decodeMachine code = machine := by
  refine ⟨encodeMachine machine, decodeMachine_encodeMachine machine, ?_⟩
  intro code hcode
  calc
    code = encodeMachine (decodeMachine code) := (encodeMachine_decodeMachine code).symm
    _ = encodeMachine machine := congrArg encodeMachine hcode

/--
将任意自然数作边界检查：在机器总数范围内就解码，越界则返回 `none`。-/
noncomputable def decodeMachineNat (n code : ℕ) : Option (BinaryMachine (n + 1)) :=
  if h : code < Fintype.card (BinaryMachine (n + 1)) then
    some (decodeMachine ⟨code, h⟩)
  else none

/-- 有限代码的自然数值通过边界检查后解码为原机器。
@isnad1 id=eq.0h2v.s7.956b681f7416 from=translated src=- shape=ae86fe1b vocab=7986f8d2
-/
theorem decodeMachineNat_encodeMachine (machine : BinaryMachine (n + 1)) :
    decodeMachineNat n (encodeMachine machine).val = some machine := by
  simp [decodeMachineNat, decodeMachine_encodeMachine]

/-- 自然数代码可成功解码，当且仅当它严格小于固定状态数机器的总数。
@isnad1 id=iff.0h2v.s7.4222755e391a from=translated src=- shape=62a25c10 vocab=762df458
-/
theorem decodeMachineNat_isSome_iff (n code : ℕ) :
    (decodeMachineNat n code).isSome = true ↔
      code < Fintype.card (BinaryMachine (n + 1)) := by
  by_cases h : code < Fintype.card (BinaryMachine (n + 1)) <;>
    simp [decodeMachineNat, h]

/--
> **Entry**: settheory.computability.binary-machine-coding
> **一句话**: 固定状态数的全部有限机器与一个有限代码类型一一对应，并可由自然数边界检查解码。
> **依赖**: `settheory.googology.binary-machine`
> **mathlib**: `Fintype.equivFin`, `Fintype.card`
@isnad1 id=and.0h1v.s5.df90c5ca5989 from=translated src=- shape=43d764e5 vocab=213afe6a
-/
theorem binaryMachine_coding_specification (n : ℕ) :
    (∀ machine : BinaryMachine (n + 1),
      decodeMachine (encodeMachine machine) = machine) ∧
      (∀ code : MachineCode n, encodeMachine (decodeMachine code) = code) := by
  exact ⟨decodeMachine_encodeMachine, encodeMachine_decodeMachine⟩

end SandronesLibrary.SetTheory.BinaryMachineCoding
