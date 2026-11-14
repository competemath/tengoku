/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.SetTheory.BusyBeaverTime

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# SetTheory / BusyBeaverTimeHaltingBound —— 最大时间作为统一停机界

停机状态在后续有限执行中保持不变，因此 `HaltedAt` 关于时间单调。固定状态数的经典最大首次停机
时间由此成为统一界：机器最终停机，当且仅当它在该界时已经停机。

给定一个显式自然数界，有限运行检查是可执行的；经典界本身仍是 `noncomputable`，本文件不声称
已经得到一般停机算法。
-/

namespace SandronesLibrary.SetTheory.BusyBeaverTimeHaltingBound

open GoogologyComputability BusyBeaver BusyBeaverTime

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

/-- 机器在某时刻已经停机，则在任意更晚时刻仍处于同一停机状态。
@isnad1 id=monotone.0h2v.s4.3382c35f5f93 from=translated src=- shape=abbd4ad6 vocab=5e467308
-/
theorem haltedAt_mono (machine : BinaryMachine (n + 1)) :
    Monotone (HaltedAt machine) := by
  intro first later hle hhalted
  obtain ⟨extra, heq⟩ := Nat.exists_eq_add_of_le hle
  unfold HaltedAt at hhalted ⊢
  cases hrun : runSteps machine first (blankStart machine) with
  | running config => simp [haltedTape?, hrun] at hhalted
  | halted tape =>
      rw [heq, runSteps_add, hrun, runSteps_halted]
      simp [haltedTape?]

/-- `bound` 是固定状态数机器类的统一停机界。-/
def IsUniformHaltingBound (n bound : ℕ) : Prop :=
  ∀ machine : BinaryMachine (n + 1),
    EventuallyHalts machine ↔ HaltedAt machine bound

/--
> **Entry**: settheory.googology.busy-beaver-time-halting-bound
> **一句话**: 固定状态数的经典最大首次停机时间是统一界，最终停机等价于在该有限时刻已经停机。
> **依赖**: `settheory.googology.busy-beaver-time`
> **mathlib**: 无（复用本库确定执行与最大时间规格）
@isnad1 id=isunifor.0h1v.s2.5f06679664ff from=translated src=- shape=9d44d080 vocab=b70d6e4f
-/
theorem classicalBusyBeaverTime_is_uniform_bound (n : ℕ) :
    IsUniformHaltingBound n (classicalBusyBeaverTimeValue n) := by
  intro machine
  constructor
  · intro hhalts
    have hfirst := machineHaltingTime_spec hhalts
    have hle := (classicalBusyBeaverTimeValue_spec n).1 machine
      (machineHaltingTime machine) hfirst
    exact haltedAt_mono machine hle hfirst.1
  · intro hhalted
    exact (eventuallyHalts_iff_exists_haltedAt machine).mpr
      ⟨classicalBusyBeaverTimeValue n, hhalted⟩

/-- 给定显式燃料后可执行的有限停机检查。-/
def haltsByFuel (fuel : ℕ) (machine : BinaryMachine (n + 1)) : Bool :=
  (haltedTape? (runSteps machine fuel (blankStart machine))).isSome

/-- 布尔检查返回真，恰好表示机器在该燃料界时已经停机。
@isnad1 id=iff.0h3v.s4.3fad3c91fa48 from=translated src=- shape=cb8ec3c2 vocab=54c9d877
-/
theorem haltsByFuel_eq_true_iff (fuel : ℕ) (machine : BinaryMachine (n + 1)) :
    haltsByFuel fuel machine = true ↔ HaltedAt machine fuel := by
  rfl

/-- 若使用者给出统一停机界，有限布尔检查便精确判定该固定状态数机器是否最终停机。
@isnad1 id=iff.1h3v.s5.315dd8d91012 from=translated src=- shape=71f4b4a8 vocab=48e71259
-/
theorem haltsByFuel_decides_of_uniform_bound {n bound : ℕ}
    (hbound : IsUniformHaltingBound n bound)
    (machine : BinaryMachine (n + 1)) :
    haltsByFuel bound machine = true ↔ EventuallyHalts machine := by
  rw [haltsByFuel_eq_true_iff, ← hbound machine]

/-- 代入经典最大时间后，有限检查在命题上等价于最终停机。
@isnad1 id=iff.0h2v.s4.2478bdc7a590 from=translated src=- shape=64d1e80d vocab=c02f4b7e
-/
theorem haltsBy_classical_time_iff (machine : BinaryMachine (n + 1)) :
    haltsByFuel (classicalBusyBeaverTimeValue n) machine = true ↔
      EventuallyHalts machine := by
  exact haltsByFuel_decides_of_uniform_bound
    (classicalBusyBeaverTime_is_uniform_bound n) machine

end SandronesLibrary.SetTheory.BusyBeaverTimeHaltingBound
