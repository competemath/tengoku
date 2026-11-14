/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.SetTheory.BinaryMachineCoding
import Tengoku.SandronesLibrary.SandronesLibrary.SetTheory.BusyBeaverTimeHaltingBound

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# SetTheory / BinaryMachineCodeHalting —— 固定状态数机器代码的停机检查

本文件把固定状态数机器的编码接口与时间型 Busy Beaver 的统一停机界接口组合起来。代码先由
`decodeMachine` 还原为机器，再接受有限燃料检查；给出正确统一界时，该检查与最终停机精确等价。

现有编码和解码来自 `Fintype.equivFin`，因此是 `noncomputable`；经典最大停机时间同样是
`noncomputable`。这里得到的是命题规格，不是可执行通用停机算法，也不包含不可判定性结论。
-/

namespace SandronesLibrary.SetTheory.BinaryMachineCodeHalting

open GoogologyComputability
open BinaryMachineCoding BusyBeaver BusyBeaverTime BusyBeaverTimeHaltingBound

/--
> **Entry**: settheory.computability.binary-machine-code-halting
> **一句话**: 固定状态数机器代码在已知正确统一界时，可由界内有限运行检查精确刻画最终停机。
> **依赖**: `settheory.computability.binary-machine-coding`,
> `settheory.googology.busy-beaver-time-halting-bound`
> **mathlib**: 无（组合本库机器编码和统一停机界接口）

`code` 解码出的机器在 `fuel` 步时已经停机。-/
noncomputable def CodeHaltedAt (code : MachineCode n) (fuel : ℕ) : Prop :=
  HaltedAt (decodeMachine code) fuel

/-- `code` 解码出的机器在某个有限时刻停机。-/
noncomputable def CodeEventuallyHalts (code : MachineCode n) : Prop :=
  EventuallyHalts (decodeMachine code)

/-- 解码固定状态数机器代码后，用显式燃料进行有限停机检查。-/
noncomputable def codeHaltsByFuel (fuel : ℕ) (code : MachineCode n) : Bool :=
  haltsByFuel fuel (decodeMachine code)

/-- 代码检查返回真，恰好表示解码后的机器在该燃料时已经停机。-/
theorem codeHaltsByFuel_eq_true_iff (fuel : ℕ) (code : MachineCode n) :
    codeHaltsByFuel fuel code = true ↔ CodeHaltedAt code fuel := by
  exact haltsByFuel_eq_true_iff fuel (decodeMachine code)

/-- 若使用者给出固定状态数机器类的正确统一界，代码检查便精确刻画最终停机。-/
theorem codeHaltsByFuel_decides_of_uniform_bound {n bound : ℕ}
    (hbound : IsUniformHaltingBound n bound) (code : MachineCode n) :
    codeHaltsByFuel bound code = true ↔ CodeEventuallyHalts code := by
  exact haltsByFuel_decides_of_uniform_bound hbound (decodeMachine code)

/-- 代入经典最大停机时间后，代码检查在命题上等价于解码机器最终停机。-/
theorem codeHaltsBy_classical_time_iff (code : MachineCode n) :
    codeHaltsByFuel (classicalBusyBeaverTimeValue n) code = true ↔
      CodeEventuallyHalts code := by
  exact codeHaltsByFuel_decides_of_uniform_bound
    (classicalBusyBeaverTime_is_uniform_bound n) code

/-- 固定状态数代码在正确统一界下精确判定最终停机的汇总规格。-/
theorem binaryMachineCode_halting_specification {n bound : ℕ}
    (hbound : IsUniformHaltingBound n bound) (code : MachineCode n) :
    codeHaltsByFuel bound code = true ↔ CodeEventuallyHalts code := by
  exact codeHaltsByFuel_decides_of_uniform_bound hbound code

end SandronesLibrary.SetTheory.BinaryMachineCodeHalting
