/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.SetTheory.BusyBeaver

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# SetTheory / BusyBeaverExistence —— 经典 Busy Beaver 值的存在性

本文件直接复用 `BusyBeaver` 模块已经公开的无时间界停机关系、停机输出关系和最大值关系，不再
建立第二套定义。固定状态数后机器表有限；用经典选择读取每台停机机器的唯一输出，再取有限最大值。

这里证明的是值的存在与规格，不包含不可计算性结论。
-/

namespace SandronesLibrary.SetTheory.BusyBeaverExistence

open GoogologyComputability BusyBeaver

/-- 从空白纸带立即停机且不写入 `1` 的机器。-/
def immediateHaltMachine (n : ℕ) : BinaryMachine (n + 1) :=
  fun _ _ => { writeOne := false, move := .right, nextState := none }

theorem immediateHaltMachine_has_zero_score (n : ℕ) :
    HasHaltingOnesScore (immediateHaltMachine n) 0 := by
  refine ⟨1, ∅, ?_, rfl⟩
  simp [runSteps, executeStep, blankStart, immediateHaltMachine, writeSymbol, haltedTape?]

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

/-- 确定机器若最终停机，则不同停机时刻观察到的 `1` 数相同。-/
theorem hasHaltingOnesScore_unique {machine : BinaryMachine (n + 1)} {x y : ℕ}
    (hx : HasHaltingOnesScore machine x) (hy : HasHaltingOnesScore machine y) : x = y := by
  rcases hx with ⟨stepsX, tapeX, hrunX, rfl⟩
  rcases hy with ⟨stepsY, tapeY, hrunY, rfl⟩
  have statusX : runSteps machine stepsX (blankStart machine) = .halted tapeX := by
    cases hstatus : runSteps machine stepsX (blankStart machine) with
    | running config => simp [haltedTape?, hstatus] at hrunX
    | halted tape =>
        have htape : tape = tapeX := by simpa [haltedTape?, hstatus] using hrunX
        exact congrArg ExecutionStatus.halted htape
  have statusY : runSteps machine stepsY (blankStart machine) = .halted tapeY := by
    cases hstatus : runSteps machine stepsY (blankStart machine) with
    | running config => simp [haltedTape?, hstatus] at hrunY
    | halted tape =>
        have htape : tape = tapeY := by simpa [haltedTape?, hstatus] using hrunY
        exact congrArg ExecutionStatus.halted htape
  by_cases hle : stepsX ≤ stepsY
  · obtain ⟨difference, heq⟩ := Nat.exists_eq_add_of_le hle
    rw [heq, runSteps_add, statusX, runSteps_halted] at statusY
    exact congrArg Finset.card (ExecutionStatus.halted.inj statusY)
  · have hYX : stepsY ≤ stepsX := Nat.le_of_lt (Nat.lt_of_not_ge hle)
    obtain ⟨difference, heq⟩ := Nat.exists_eq_add_of_le hYX
    rw [heq, runSteps_add, statusY, runSteps_halted] at statusX
    exact congrArg Finset.card (ExecutionStatus.halted.inj statusX).symm

/--
若机器有停机输出，用经典选择取该输出；没有停机输出则补零。唯一性定理保证停机分支不依赖选择。-/
noncomputable def eventualOnesScore (machine : BinaryMachine (n + 1)) : ℕ := by
  classical
  exact if h : ∃ score, HasHaltingOnesScore machine score then Classical.choose h else 0

private theorem eventualOnesScore_spec {machine : BinaryMachine (n + 1)}
    (h : ∃ score, HasHaltingOnesScore machine score) :
    HasHaltingOnesScore machine (eventualOnesScore machine) := by
  rw [eventualOnesScore, dite_eq_left h]
  exact Classical.choose_spec h

private theorem eventualOnesScore_eq {machine : BinaryMachine (n + 1)} {score : ℕ}
    (h : HasHaltingOnesScore machine score) : eventualOnesScore machine = score := by
  apply hasHaltingOnesScore_unique (eventualOnesScore_spec ⟨score, h⟩) h

/-- 固定状态数时，全部有限机器的经典最终分数（不停止者补零）的最大值。-/
noncomputable def classicalBusyBeaverValue (n : ℕ) : ℕ :=
  Finset.univ.sup (eventualOnesScore (n := n))

/--
> **Entry**: settheory.googology.busy-beaver-existence
> **一句话**: 每个固定正工作状态数的机器类都有一个由停机机器达到的最大最终输出。
> **依赖**: `settheory.googology.unbounded-halting-relation`,
> `settheory.googology.busy-beaver-value-relation`
> **mathlib**: `Finset.sup`, `Classical.choose`-/
theorem exists_isBusyBeaverValue (n : ℕ) : ∃ value, IsBusyBeaverValue n value := by
  let value := classicalBusyBeaverValue n
  have hupper : ∀ machine : BinaryMachine (n + 1), eventualOnesScore machine ≤ value := by
    intro machine
    exact Finset.le_sup (s := Finset.univ) (f := eventualOnesScore (n := n))
      (Finset.mem_univ machine)
  obtain ⟨machine, _, hmax⟩ :=
    Finset.exists_mem_eq_sup (Finset.univ : Finset (BinaryMachine (n + 1)))
      ⟨immediateHaltMachine n, Finset.mem_univ _⟩ (eventualOnesScore (n := n))
  refine ⟨value, ?_, ?_⟩
  · intro candidate score hscore
    rw [← eventualOnesScore_eq hscore]
    exact hupper candidate
  · by_cases hhalts : ∃ score, HasHaltingOnesScore machine score
    · refine ⟨machine, ?_⟩
      change HasHaltingOnesScore machine (classicalBusyBeaverValue n)
      rw [classicalBusyBeaverValue, hmax]
      exact eventualOnesScore_spec hhalts
    · have hscore : eventualOnesScore machine = 0 := by
        simp [eventualOnesScore, hhalts]
      have hvalue : value = 0 := hmax.trans hscore
      rw [hvalue]
      exact ⟨immediateHaltMachine n, immediateHaltMachine_has_zero_score n⟩

/-- 本文件定义的经典值满足 `BusyBeaver` 模块已经公开的最大值关系。-/
theorem classicalBusyBeaverValue_spec (n : ℕ) :
    IsBusyBeaverValue n (classicalBusyBeaverValue n) := by
  obtain ⟨value, hvalue⟩ := exists_isBusyBeaverValue n
  rcases hvalue with ⟨hupper, machine, hattain⟩
  have hchosen_le : classicalBusyBeaverValue n ≤ value := by
    apply Finset.sup_le
    intro candidate _
    by_cases hhalts : ∃ score, HasHaltingOnesScore candidate score
    · exact hupper candidate _ (eventualOnesScore_spec hhalts)
    · simp [eventualOnesScore, hhalts]
  have hvalue_le : value ≤ classicalBusyBeaverValue n := by
    rw [← eventualOnesScore_eq hattain]
    exact Finset.le_sup (s := Finset.univ) (f := eventualOnesScore (n := n))
      (Finset.mem_univ machine)
  have value_eq : value = classicalBusyBeaverValue n :=
    le_antisymm hvalue_le hchosen_le
  rw [← value_eq]
  exact ⟨hupper, machine, hattain⟩

end SandronesLibrary.SetTheory.BusyBeaverExistence
