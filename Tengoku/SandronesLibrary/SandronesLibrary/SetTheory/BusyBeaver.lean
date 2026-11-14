/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.SetTheory.GoogologyComputability

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# SetTheory / BusyBeaver —— 无时间界停机与经典 Busy Beaver 最大值关系

本文件在已有的二符号有限状态机语义上去掉人为燃料上限。经典 Busy Beaver 暂以“某个数确实
是全部停机输出的最大值”的关系表达，而不把尚未在本库证明的存在性或不可计算性藏进一个总函数。
-/

namespace SandronesLibrary.SetTheory.BusyBeaver

open GoogologyComputability

/-- 机器从标准空白纸带出发，经过某个有限步数后到达停机纸带。-/
def EventuallyHalts (machine : BinaryMachine (n + 1)) : Prop :=
  ∃ steps tape, haltedTape? (runSteps machine steps (blankStart machine)) = some tape

/-- 机器最终停机，并在停机纸带上留下恰好 `score` 个 `1`。-/
def HasHaltingOnesScore (machine : BinaryMachine (n + 1)) (score : ℕ) : Prop :=
  ∃ steps tape,
    haltedTape? (runSteps machine steps (blankStart machine)) = some tape ∧
      tape.card = score

/--
> **Entry**: settheory.googology.unbounded-halting-relation
> **一句话**: 无时间界停机不是给机器预设统一燃料，而是断言存在某个有限时刻到达停机纸带。
> **依赖**: `settheory.googology.bounded-halting`
> **mathlib**: 无（本库显式执行器）
@isnad1 id=iff.0h2v.s4.fa8cedf640c3 from=translated src=- shape=ae2f7b72 vocab=fb6f3a3e
-/
theorem eventuallyHalts_iff_exists_score (machine : BinaryMachine (n + 1)) :
    EventuallyHalts machine ↔ ∃ score, HasHaltingOnesScore machine score := by
  constructor
  · rintro ⟨steps, tape, halted⟩
    exact ⟨tape.card, steps, tape, halted, rfl⟩
  · rintro ⟨score, steps, tape, halted, _⟩
    exact ⟨steps, tape, halted⟩

/-- 限定燃料内停机必然蕴含无时间界意义下最终停机。
@isnad1 id=eventual.1h3v.s4.3f50ae685ffe from=translated src=- shape=a26e48ec vocab=ec09bc13
-/
theorem haltsWithin_implies_eventuallyHalts (fuel : ℕ)
    (machine : BinaryMachine (n + 1)) :
    HaltsWithin fuel machine → EventuallyHalts machine := by
  intro halts
  rcases (haltsWithin_iff_exists_tape fuel machine).mp halts with ⟨tape, halted⟩
  exact ⟨fuel, tape, halted⟩

/--
`value` 是经典的产出型 Busy Beaver 值：所有最终停机的固定状态数机器，其纸带 `1` 数量都不
超过 `value`，并且至少有一台最终停机的机器恰好取得 `value`。-/
def IsBusyBeaverValue (n value : ℕ) : Prop :=
  (∀ machine : BinaryMachine (n + 1), ∀ score,
      HasHaltingOnesScore machine score → score ≤ value) ∧
    ∃ machine : BinaryMachine (n + 1), HasHaltingOnesScore machine value

/--
> **Entry**: settheory.googology.busy-beaver-value-relation
> **一句话**: 经典 Busy Beaver 值用“支配全部停机输出且被某台停机机器取得”的最大值关系表达。
> **依赖**: `settheory.googology.unbounded-halting-relation`,
> `settheory.googology.busy-beaver-candidate`
> **mathlib**: `Finset.sup`
@isnad1 id=le.1h3v.s4.bfdc376cea2c from=translated src=- shape=70209c55 vocab=c2d64237
-/
theorem busyBeaverCandidate_le_of_isValue {n value : ℕ}
    (hvalue : IsBusyBeaverValue n value)
    (fuel : ℕ) :
    busyBeaverCandidate n fuel ≤ value := by
  apply Finset.sup_le
  intro machine _
  unfold boundedOnesScore
  cases hrun : runSteps machine fuel (blankStart machine) with
  | running config => exact Nat.zero_le value
  | halted tape =>
      apply hvalue.1 machine tape.card
      exact ⟨fuel, tape, by simp [haltedTape?, hrun]⟩

/--
若 `value` 满足经典最大值关系，那么冠军机器在某个有限时刻已经停机；取那个时刻为燃料，有限
搜索候选值便恰好等于 `value`。
@isnad1 id=ex.1h2v.s4.ec403f4cc793 from=translated src=- shape=07dacbe2 vocab=bbc35f3a
-/
theorem exists_candidate_eq_of_isValue {n value : ℕ}
    (hvalue : IsBusyBeaverValue n value) :
    ∃ fuel, busyBeaverCandidate n fuel = value := by
  rcases hvalue.2 with ⟨machine, fuel, tape, halted, tape_card⟩
  refine ⟨fuel, le_antisymm (busyBeaverCandidate_le_of_isValue hvalue fuel) ?_⟩
  have score_eq : boundedOnesScore fuel machine = value := by
    unfold boundedOnesScore
    cases hrun : runSteps machine fuel (blankStart machine) with
    | running config =>
        rw [hrun] at halted
        cases halted
    | halted finalTape =>
        rw [hrun] at halted
        simp only [haltedTape?, Option.some.injEq] at halted
        subst finalTape
        exact tape_card
  rw [← score_eq]
  exact boundedOnesScore_le_candidate fuel machine

/-- 满足最大值关系的自然数唯一。
@isnad1 id=eq.2h3v.s4.026c06eea62a from=translated src=- shape=920a25f1 vocab=3f586c47
-/
theorem isBusyBeaverValue_unique {n x y : ℕ} (hx : IsBusyBeaverValue n x)
    (hy : IsBusyBeaverValue n y) : x = y := by
  rcases hx.2 with ⟨machineX, hmachineX⟩
  rcases hy.2 with ⟨machineY, hmachineY⟩
  exact Nat.le_antisymm (hy.1 machineX x hmachineX) (hx.1 machineY y hmachineY)

end SandronesLibrary.SetTheory.BusyBeaver
