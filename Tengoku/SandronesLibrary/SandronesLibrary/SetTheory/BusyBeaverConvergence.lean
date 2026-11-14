/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.SetTheory.BusyBeaverExistence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# SetTheory / BusyBeaverConvergence —— 有限燃料候选最终稳定

本文件连接可执行的有限燃料候选值与经典存在性值。候选值随燃料单调增加，始终不超过经典值；
经典冠军机器在某个有限时刻停机，因此从某个不显式给出的阈值起，候选值永久等于经典值。

本结论不提供阈值算法，也不包含不可计算性声明。
-/

namespace SandronesLibrary.SetTheory.BusyBeaverConvergence

open GoogologyComputability BusyBeaver BusyBeaverExistence

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

/-- 单台机器的限定输出分数随燃料增加而不减。
@isnad1 id=monotone.0h2v.s4.46911768fab8 from=translated src=- shape=c3cc1fe9 vocab=779e4467
-/
theorem boundedOnesScore_mono (machine : BinaryMachine (n + 1)) :
    Monotone (fun fuel => boundedOnesScore fuel machine) := by
  intro first later hle
  obtain ⟨extra, heq⟩ := Nat.exists_eq_add_of_le hle
  unfold boundedOnesScore
  change (match runSteps machine first (blankStart machine) with
    | .running _ => 0
    | .halted ones => ones.card) ≤
    (match runSteps machine later (blankStart machine) with
    | .running _ => 0
    | .halted ones => ones.card)
  cases hrun : runSteps machine first (blankStart machine) with
  | running config => simp only; exact Nat.zero_le _
  | halted tape =>
      simp only
      rw [heq, runSteps_add, hrun, runSteps_halted]

/-- 固定状态数的有限燃料 Busy Beaver 候选值随燃料增加而不减。
@isnad1 id=monotone.0h1v.s3.939f38b3eb34 from=translated src=- shape=f736e2c1 vocab=ba674249
-/
theorem busyBeaverCandidate_mono (n : ℕ) :
    Monotone (busyBeaverCandidate n) := by
  intro first later hle
  apply Finset.sup_le
  intro machine _
  exact (boundedOnesScore_mono machine hle).trans
    (Finset.le_sup (s := Finset.univ)
      (f := boundedOnesScore (n := n) later) (Finset.mem_univ machine))

/-- 每个有限燃料候选值都不超过经典 Busy Beaver 值。
@isnad1 id=le.0h2v.s3.5c57f4846670 from=translated src=- shape=54bc9ee1 vocab=6a9705e4
-/
theorem busyBeaverCandidate_le_classical (n fuel : ℕ) :
    busyBeaverCandidate n fuel ≤ classicalBusyBeaverValue n := by
  exact busyBeaverCandidate_le_of_isValue (classicalBusyBeaverValue_spec n) fuel

/--
> **Entry**: settheory.googology.busy-beaver-convergence
> **一句话**: 有限燃料候选值单调逼近经典值，并在某个有限但未被计算出的阈值后永久稳定。
> **依赖**: `settheory.googology.busy-beaver-candidate`,
> `settheory.googology.busy-beaver-existence`
> **mathlib**: 无（复用本库最大值规格与有限执行语义）
@isnad1 id=ex.0h1v.s4.696efc14e335 from=translated src=- shape=83fc8e81 vocab=6a9705e4
-/
theorem exists_threshold_candidate_eq_classical (n : ℕ) :
    ∃ threshold, ∀ fuel, threshold ≤ fuel →
      busyBeaverCandidate n fuel = classicalBusyBeaverValue n := by
  obtain ⟨threshold, hthreshold⟩ :=
    exists_candidate_eq_of_isValue (classicalBusyBeaverValue_spec n)
  refine ⟨threshold, ?_⟩
  intro fuel hle
  apply Nat.le_antisymm (busyBeaverCandidate_le_classical n fuel)
  rw [← hthreshold]
  exact busyBeaverCandidate_mono n hle

end SandronesLibrary.SetTheory.BusyBeaverConvergence
