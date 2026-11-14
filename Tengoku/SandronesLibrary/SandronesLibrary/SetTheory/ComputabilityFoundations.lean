/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.SetTheory.BusyBeaver

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# SetTheory / ComputabilityFoundations —— 可计算函数与机器判定的教材定义门

本文件为既有二符号有限状态机补上自然数输入约定：输入 `x` 由位置 `0, …, x-1` 上的一元 `1`
编码，停机纸带上的 `1` 数作为自然数输出。由此定义某台封装机器计算函数，以及谓词的机器判定。

这里只建立定义和基础规格，不声称停机不可判定或 Busy Beaver 不可计算。
-/

namespace SandronesLibrary.SetTheory.ComputabilityFoundations

open GoogologyComputability

/-- 一份可执行程序同时记录其正工作状态数及对应的有限机器表。-/
structure NatProgram where
  stateOffset : ℕ
  machine : BinaryMachine (stateOffset + 1)

/-- 把自然数 `input` 编成整数纸带位置 `0, …, input-1` 上的一串 `1`。-/
def unaryTape (input : ℕ) : Finset ℤ :=
  (Finset.range input).map ⟨Int.ofNat, by
    intro a b h
    exact Int.ofNat.inj h⟩

/-- 程序在一元输入上的标准初始配置：状态零、头在原点。-/
def inputStart (program : NatProgram) (input : ℕ) : ExecutionStatus (program.stateOffset + 1) :=
  .running { state := 0, head := 0, ones := unaryTape input }

/--
给程序 `fuel` 步燃料：若它已经停机，返回最终纸带上 `1` 的数量；否则返回 `none`。-/
def interpretWithin (program : NatProgram) (fuel input : ℕ) : Option ℕ :=
  match runSteps program.machine fuel (inputStart program input) with
  | .running _ => none
  | .halted ones => some ones.card

/-- 程序计算总函数 `f`：每个输入都在某个有限但不预先统一限定的时刻输出 `f input`。-/
def ComputesNatFunction (program : NatProgram) (f : ℕ → ℕ) : Prop :=
  ∀ input, ∃ fuel, interpretWithin program fuel input = some (f input)

/-- 自然数函数在本机器模型下可计算，当且仅当存在一份程序计算它。-/
def NatComputable (f : ℕ → ℕ) : Prop :=
  ∃ program, ComputesNatFunction program f

/--
> **Entry**: settheory.computability.nat-computable
> **一句话**: 自然数函数可计算，是指存在一台有限二符号机器在每个一元输入上最终停机并输出函数值。
> **依赖**: `settheory.googology.unbounded-halting-relation`
> **mathlib**: `Finset.range`, `Finset.map`-/
theorem natComputable_iff_exists_program (f : ℕ → ℕ) :
    NatComputable f ↔
      ∃ program : NatProgram, ∀ input, ∃ fuel,
        interpretWithin program fuel input = some (f input) := by
  rfl

private theorem runSteps_add (machine : BinaryMachine n) (first second : ℕ)
    (status : ExecutionStatus n) :
    runSteps machine (first + second) status =
      runSteps machine second (runSteps machine first status) := by
  induction first generalizing status with
  | zero => simp [runSteps]
  | succ first ih =>
      rw [Nat.succ_add, runSteps, ih]
      rfl

private theorem runSteps_halted (machine : BinaryMachine n) (steps : ℕ) (tape : Finset ℤ) :
    runSteps machine steps (.halted tape) = .halted tape := by
  induction steps with
  | zero => rfl
  | succ steps ih => simpa [runSteps, executeStep] using ih

/-- 确定程序在同一输入上若两次观察到输出，则两个自然数输出必相同。-/
theorem interpretWithin_output_unique {program : NatProgram} {input fuel₁ fuel₂ x y : ℕ}
    (hx : interpretWithin program fuel₁ input = some x)
    (hy : interpretWithin program fuel₂ input = some y) : x = y := by
  unfold interpretWithin at hx hy
  cases hrun₁ : runSteps program.machine fuel₁ (inputStart program input) with
  | running config => simp [hrun₁] at hx
  | halted tape₁ =>
      simp only [hrun₁, Option.some.injEq] at hx
      cases hrun₂ : runSteps program.machine fuel₂ (inputStart program input) with
      | running config => simp [hrun₂] at hy
      | halted tape₂ =>
          simp only [hrun₂, Option.some.injEq] at hy
          subst x
          subst y
          by_cases hle : fuel₁ ≤ fuel₂
          · obtain ⟨extra, heq⟩ := Nat.exists_eq_add_of_le hle
            rw [heq, runSteps_add, hrun₁, runSteps_halted] at hrun₂
            exact congrArg Finset.card (ExecutionStatus.halted.inj hrun₂)
          · have hreverse : fuel₂ ≤ fuel₁ := Nat.le_of_lt (Nat.lt_of_not_ge hle)
            obtain ⟨extra, heq⟩ := Nat.exists_eq_add_of_le hreverse
            rw [heq, runSteps_add, hrun₂, runSteps_halted] at hrun₁
            exact congrArg Finset.card (ExecutionStatus.halted.inj hrun₁).symm

/--
程序判定谓词 `P`：每个输入最终停机；`P input` 成立时输出 `1`，不成立时输出 `0`。-/
def DecidesPredicate (program : NatProgram) (P : ℕ → Prop) : Prop :=
  ∀ input,
    (P input ∧ ∃ fuel, interpretWithin program fuel input = some 1) ∨
      (¬P input ∧ ∃ fuel, interpretWithin program fuel input = some 0)

/-- 一个谓词可由本机器模型判定，当且仅当存在程序满足上述真假输出规格。-/
def MachineDecidable (P : ℕ → Prop) : Prop :=
  ∃ program, DecidesPredicate program P

/-- 布尔式特征函数：命题为真取 `1`，为假取 `0`。-/
def characteristicFunction (P : ℕ → Prop) [DecidablePred P] (input : ℕ) : ℕ :=
  if P input then 1 else 0

/--
> **Entry**: settheory.computability.machine-decidable
> **一句话**: 机器判定谓词等价于同一程序计算它的零一特征函数。
> **依赖**: `settheory.computability.nat-computable`
> **mathlib**: 无（本库输入、输出与判定规格）-/
theorem decidesPredicate_iff_computes_characteristic (program : NatProgram)
    (P : ℕ → Prop) [DecidablePred P] :
    DecidesPredicate program P ↔ ComputesNatFunction program (characteristicFunction P) := by
  constructor
  · intro h input
    rcases h input with ⟨hP, fuel, hout⟩ | ⟨hP, fuel, hout⟩
    · exact ⟨fuel, by simpa [characteristicFunction, hP] using hout⟩
    · exact ⟨fuel, by simpa [characteristicFunction, hP] using hout⟩
  · intro h input
    by_cases hP : P input
    · left
      rcases h input with ⟨fuel, hout⟩
      exact ⟨hP, fuel, by simpa [characteristicFunction, hP] using hout⟩
    · right
      rcases h input with ⟨fuel, hout⟩
      exact ⟨hP, fuel, by simpa [characteristicFunction, hP] using hout⟩

end SandronesLibrary.SetTheory.ComputabilityFoundations
