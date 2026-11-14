/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.Seed.Data.Finset.Lattice.Fold
import Tengoku.Seed.Data.Fintype.Basic
import Tengoku.Seed.Data.Fintype.Fin
import Tengoku.Seed.Data.Fintype.Option
import Tengoku.Seed.Data.Fintype.Pi
import Tengoku.Seed.Data.Fintype.Prod
import Tengoku.Seed.Data.Int.Basic
import Tengoku.Seed.Tactic.DeriveFintype

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# SetTheory / GoogologyComputability —— Busy Beaver 的有限机器模型

本文件从二符号、有限状态的确定性图灵机开始，依次定义单步执行、有限步运行、限定步数停机，
以及可穷举的 Busy Beaver 候选值。这里只讨论固定燃料下的有限搜索；没有声称证明停机问题或
Busy Beaver 函数不可计算。
-/

namespace SandronesLibrary.SetTheory.GoogologyComputability

/-- 读写头每一步向左或向右移动一个格子。-/
inductive HeadMove where
  | left
  | right
deriving DecidableEq, Repr

instance : Fintype HeadMove where
  elems := {.left, .right}
  complete := by
    intro direction
    cases direction <;> simp

/--
拥有 `n` 个工作状态的机器指令。机器读到当前符号后，写入一个二进制符号，移动读写头，
再选择一个新工作状态；`nextState = none` 表示执行完本条指令后停机。-/
structure Instruction (n : ℕ) where
  writeOne : Bool
  move : HeadMove
  nextState : Option (Fin n)
deriving DecidableEq, Repr

instance : Fintype (Instruction n) :=
  Fintype.ofEquiv (Bool × HeadMove × Option (Fin n)) {
    toFun := fun data => {
      writeOne := data.1
      move := data.2.1
      nextState := data.2.2
    }
    invFun := fun instruction =>
      (instruction.writeOne, instruction.move, instruction.nextState)
    left_inv := by intro data; cases data; rfl
    right_inv := by intro instruction; cases instruction; rfl
  }

/-- `n` 状态二符号确定性图灵机：每个“状态、当前符号”组合恰有一条指令。-/
abbrev BinaryMachine (n : ℕ) := Fin n → Bool → Instruction n

/--
运行配置。纸带只记录写着 `1` 的位置；不在有限集中的整数位置都解释为 `0`。
从空白纸带开始有限步运行时，这种表示始终足够。-/
structure Configuration (n : ℕ) where
  state : Fin n
  head : ℤ
  ones : Finset ℤ
deriving DecidableEq

/-- 机器或仍在某个配置中运行，或已经停机并留下最终纸带。-/
inductive ExecutionStatus (n : ℕ) where
  | running (config : Configuration n)
  | halted (ones : Finset ℤ)
deriving DecidableEq

/-- 读取当前格：该位置在 `ones` 中恰好表示读到 `1`。-/
def readSymbol (config : Configuration n) : Bool :=
  config.head ∈ config.ones

/-- 按指令覆写当前格。写 `1` 就插入当前位置，写 `0` 就将其删除。-/
def writeSymbol (config : Configuration n) (value : Bool) : Finset ℤ :=
  if value then insert config.head config.ones else config.ones.erase config.head

/-- 按指定方向把读写头移动一格。-/
def moveHead (head : ℤ) : HeadMove → ℤ
  | .left => head - 1
  | .right => head + 1

/--
> **Entry**: settheory.googology.binary-machine
> **一句话**: 二符号有限状态机用有限指令表作用在一条初始全零的双向纸带上。
> **依赖**: 无
> **mathlib**: `Fin`, `Finset`-/
theorem readSymbol_initially_blank (state : Fin n) :
    readSymbol ({ state := state, head := 0, ones := ∅ } : Configuration n) = false := by
  simp [readSymbol]

/-- 执行一条指令；返回 `halted` 时，写入和移动都已完成。-/
def executeStep (machine : BinaryMachine n) : ExecutionStatus n → ExecutionStatus n
  | .halted ones => .halted ones
  | .running config =>
      let instruction := machine config.state (readSymbol config)
      let newOnes := writeSymbol config instruction.writeOne
      match instruction.nextState with
      | none => .halted newOnes
      | some next => .running {
          state := next
          head := moveHead config.head instruction.move
          ones := newOnes
        }

/-- 从给定状态反复执行恰好 `steps` 次；已经停机的结果在余下步数中保持不变。-/
def runSteps (machine : BinaryMachine n) : ℕ → ExecutionStatus n → ExecutionStatus n
  | 0, status => status
  | steps + 1, status => runSteps machine steps (executeStep machine status)

/-- 状态 `0`、头位于原点、纸带全零的标准初始配置。-/
def blankStart (_machine : BinaryMachine (n + 1)) : ExecutionStatus (n + 1) :=
  .running { state := 0, head := 0, ones := ∅ }

/--
> **Entry**: settheory.googology.machine-execution
> **一句话**: 单步执行先读、再写、再移动，并由指令决定进入下一状态还是停机。
> **依赖**: `settheory.googology.binary-machine`
> **mathlib**: 无（本库显式执行器）-/
theorem runSteps_zero_succ (machine : BinaryMachine n) (status : ExecutionStatus n)
    (steps : ℕ) :
    runSteps machine 0 status = status ∧
      runSteps machine (steps + 1) status =
        runSteps machine steps (executeStep machine status) := by
  exact ⟨rfl, rfl⟩

/-- 若状态已经停机，取最终纸带；仍在运行则没有最终纸带。-/
def haltedTape? : ExecutionStatus n → Option (Finset ℤ)
  | .running _ => none
  | .halted ones => some ones

/-- 从空白纸带出发，机器是否在至多 `fuel` 条指令内停机。-/
def HaltsWithin (fuel : ℕ) (machine : BinaryMachine (n + 1)) : Prop :=
  match runSteps machine fuel (blankStart machine) with
  | .running _ => False
  | .halted _ => True

/--
> **Entry**: settheory.googology.bounded-halting
> **一句话**: 限定步数停机只问给定有限燃料是否足以到达停机状态，因此可以判定。
> **依赖**: `settheory.googology.machine-execution`
> **mathlib**: 无（本库显式有限迭代）-/
theorem haltsWithin_iff_exists_tape (fuel : ℕ) (machine : BinaryMachine (n + 1)) :
    HaltsWithin fuel machine ↔
      ∃ tape, haltedTape? (runSteps machine fuel (blankStart machine)) = some tape := by
  unfold HaltsWithin
  cases runSteps machine fuel (blankStart machine) <;> simp [haltedTape?]

/--
机器在燃料耗尽前停机时，返回最终纸带上 `1` 的个数；尚未停机则记为 `0`。
这个约定让固定燃料下的所有机器都得到一个自然数分数。-/
def boundedOnesScore (fuel : ℕ) (machine : BinaryMachine (n + 1)) : ℕ :=
  match runSteps machine fuel (blankStart machine) with
  | .running _ => 0
  | .halted ones => ones.card

/--
固定状态数和燃料的 Busy Beaver 候选值：穷举全部有限指令表，取停机后留下的 `1` 数量的最大值。
它是经典 Busy Beaver 值的有限搜索近似，而不是未加时间界的 Busy Beaver 函数本身。-/
def busyBeaverCandidate (n fuel : ℕ) : ℕ :=
  Finset.univ.sup (boundedOnesScore (n := n) fuel)

/--
> **Entry**: settheory.googology.busy-beaver-candidate
> **一句话**: 固定状态数与搜索步数后，可以穷举全部机器并取得停机输出的最大值。
> **依赖**: `settheory.googology.bounded-halting`
> **mathlib**: `Finset.sup`-/
theorem boundedOnesScore_le_candidate (fuel : ℕ) (machine : BinaryMachine (n + 1)) :
    boundedOnesScore fuel machine ≤ busyBeaverCandidate n fuel := by
  exact Finset.le_sup (s := Finset.univ) (f := boundedOnesScore (n := n) fuel)
    (Finset.mem_univ machine)

end SandronesLibrary.SetTheory.GoogologyComputability
