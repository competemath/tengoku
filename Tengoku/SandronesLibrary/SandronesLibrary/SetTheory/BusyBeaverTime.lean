/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.SetTheory.BusyBeaverExistence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# SetTheory / BusyBeaverTime —— 经典最大停机时间

本文件复用已有 `EventuallyHalts`，新增“首次停机时间”及固定状态数机器中的最大首次停机时间。
固定机器类有限，因此最大值存在并由一台停机机器取得。

这里只建立时间型 Busy Beaver 的基础定义和存在唯一性，不包含不可计算性或停机不可判定结论。
-/

namespace SandronesLibrary.SetTheory.BusyBeaverTime

open GoogologyComputability BusyBeaver BusyBeaverExistence

/-- 机器从标准空白配置运行恰好 `time` 步后已经处于停机状态。-/
def HaltedAt (machine : BinaryMachine (n + 1)) (time : ℕ) : Prop :=
  (haltedTape? (runSteps machine time (blankStart machine))).isSome = true

instance (machine : BinaryMachine (n + 1)) : DecidablePred (HaltedAt machine) := by
  intro time
  unfold HaltedAt
  infer_instance

private theorem haltedAt_iff_exists_tape (machine : BinaryMachine (n + 1)) (time : ℕ) :
    HaltedAt machine time ↔
      ∃ tape, haltedTape? (runSteps machine time (blankStart machine)) = some tape := by
  unfold HaltedAt
  cases haltedTape? (runSteps machine time (blankStart machine)) <;> simp

/-- 已有无时间界停机关系恰好等于“存在某个停机时刻”。-/
theorem eventuallyHalts_iff_exists_haltedAt (machine : BinaryMachine (n + 1)) :
    EventuallyHalts machine ↔ ∃ time, HaltedAt machine time := by
  constructor
  · rintro ⟨time, tape, halted⟩
    exact ⟨time, (haltedAt_iff_exists_tape machine time).mpr ⟨tape, halted⟩⟩
  · rintro ⟨time, halted⟩
    rcases (haltedAt_iff_exists_tape machine time).mp halted with ⟨tape, htape⟩
    exact ⟨time, tape, htape⟩

/-- `time` 是机器的首次停机时间：该时刻已停机，而所有更早时刻均未停机。-/
def IsFirstHaltingTime (machine : BinaryMachine (n + 1)) (time : ℕ) : Prop :=
  HaltedAt machine time ∧ ∀ earlier, earlier < time → ¬HaltedAt machine earlier

/-- 若机器最终停机，取满足 `HaltedAt` 的最小自然数；不停止的机器补零。-/
noncomputable def machineHaltingTime (machine : BinaryMachine (n + 1)) : ℕ := by
  classical
  exact if h : EventuallyHalts machine then
    Nat.find ((eventuallyHalts_iff_exists_haltedAt machine).mp h) else 0

/-- 对最终停机的机器，`machineHaltingTime` 确实是首次停机时间。-/
theorem machineHaltingTime_spec {machine : BinaryMachine (n + 1)}
    (h : EventuallyHalts machine) :
    IsFirstHaltingTime machine (machineHaltingTime machine) := by
  rw [machineHaltingTime, dite_eq_left h]
  let witness := (eventuallyHalts_iff_exists_haltedAt machine).mp h
  exact ⟨Nat.find_spec witness, fun earlier hearlier => Nat.find_min witness hearlier⟩

/-- 一台确定机器的首次停机时间是唯一的。-/
theorem isFirstHaltingTime_unique {machine : BinaryMachine (n + 1)} {x y : ℕ}
    (hx : IsFirstHaltingTime machine x) (hy : IsFirstHaltingTime machine y) : x = y := by
  apply Nat.le_antisymm
  · by_contra hnot
    have hxy : y < x := by omega
    exact (hx.2 y hxy) hy.1
  · by_contra hnot
    have hyx : x < y := by omega
    exact (hy.2 x hyx) hx.1

private theorem machineHaltingTime_eq {machine : BinaryMachine (n + 1)} {time : ℕ}
    (htime : IsFirstHaltingTime machine time) : machineHaltingTime machine = time := by
  have hhalts : EventuallyHalts machine :=
    (eventuallyHalts_iff_exists_haltedAt machine).mpr ⟨time, htime.1⟩
  exact isFirstHaltingTime_unique (machineHaltingTime_spec hhalts) htime

/-- 立即停机机器的首次停机时间为一步。-/
theorem immediateHaltMachine_first_time (n : ℕ) :
    IsFirstHaltingTime (immediateHaltMachine n) 1 := by
  constructor
  · unfold HaltedAt
    simp [runSteps, executeStep, blankStart, immediateHaltMachine, writeSymbol, haltedTape?]
  · intro earlier hearlier
    have heq : earlier = 0 := by omega
    subst earlier
    simp [HaltedAt, runSteps, blankStart, haltedTape?]

/-- `value` 是时间型 Busy Beaver 值：支配所有首次停机时间，并由某台机器达到。-/
def IsBusyBeaverTimeValue (n value : ℕ) : Prop :=
  (∀ machine : BinaryMachine (n + 1), ∀ time,
      IsFirstHaltingTime machine time → time ≤ value) ∧
    ∃ machine : BinaryMachine (n + 1), IsFirstHaltingTime machine value

/-- 固定状态数全部机器的首次停机时间最大值；不停机机器的辅助分数为零。-/
noncomputable def classicalBusyBeaverTimeValue (n : ℕ) : ℕ :=
  Finset.univ.sup (machineHaltingTime (n := n))

/--
> **Entry**: settheory.googology.busy-beaver-time
> **一句话**: 固定状态数的最终停机机器具有唯一最大首次停机时间，而且该最大值由机器实际取得。
> **依赖**: `settheory.googology.unbounded-halting-relation`,
> `settheory.googology.busy-beaver-existence`
> **mathlib**: `Nat.find`, `Finset.sup`-/
theorem classicalBusyBeaverTimeValue_spec (n : ℕ) :
    IsBusyBeaverTimeValue n (classicalBusyBeaverTimeValue n) := by
  obtain ⟨machine, _, hmax⟩ :=
    Finset.exists_mem_eq_sup (Finset.univ : Finset (BinaryMachine (n + 1)))
      ⟨immediateHaltMachine n, Finset.mem_univ _⟩ (machineHaltingTime (n := n))
  have hmachine : EventuallyHalts machine := by
    by_contra hnot
    have hzero : machineHaltingTime machine = 0 := by
      simp [machineHaltingTime, hnot]
    have himmediate : machineHaltingTime (immediateHaltMachine n) = 1 :=
      machineHaltingTime_eq (immediateHaltMachine_first_time n)
    have hle : machineHaltingTime (immediateHaltMachine n) ≤
        classicalBusyBeaverTimeValue n := by
      exact Finset.le_sup (s := Finset.univ) (f := machineHaltingTime (n := n))
        (Finset.mem_univ _)
    rw [classicalBusyBeaverTimeValue, hmax, hzero, himmediate] at hle
    omega
  constructor
  · intro candidate time htime
    rw [← machineHaltingTime_eq htime]
    exact Finset.le_sup (s := Finset.univ) (f := machineHaltingTime (n := n))
      (Finset.mem_univ candidate)
  · refine ⟨machine, ?_⟩
    rw [classicalBusyBeaverTimeValue, hmax]
    exact machineHaltingTime_spec hmachine

/-- 每个固定状态数都有一个时间型 Busy Beaver 值。-/
theorem exists_isBusyBeaverTimeValue (n : ℕ) :
    ∃ value, IsBusyBeaverTimeValue n value :=
  ⟨classicalBusyBeaverTimeValue n, classicalBusyBeaverTimeValue_spec n⟩

/-- 时间型 Busy Beaver 最大值由其最大值规格唯一确定。-/
theorem isBusyBeaverTimeValue_unique {n x y : ℕ}
    (hx : IsBusyBeaverTimeValue n x) (hy : IsBusyBeaverTimeValue n y) : x = y := by
  rcases hx.2 with ⟨machineX, hmachineX⟩
  rcases hy.2 with ⟨machineY, hmachineY⟩
  exact Nat.le_antisymm (hy.1 machineX x hmachineX) (hx.1 machineY y hmachineY)

end SandronesLibrary.SetTheory.BusyBeaverTime
