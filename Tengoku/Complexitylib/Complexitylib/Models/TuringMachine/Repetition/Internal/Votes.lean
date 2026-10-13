/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Repetition.Defs

/-!
# Vote bookkeeping for fixed-time repetition

This file connects the finite-control vote vector of `NTM.repeatAtTime` to the
block-event majority API and provides the update invariant used by the outer
trial induction.
-/

@[expose] public section

namespace Complexity

namespace NTM

variable {n k T : ℕ}

/-- Verdict of source trial `j` in a compact `k * T` repetition seed. -/
def repeatTrialVote (tm : NTM n) (x : List Bool) (k T : ℕ)
    (seed : Fin (k * T) → Bool) (j : Fin k) : Bool :=
  decide (blocksEquiv k T seed j ∈ repeatAcceptEvent tm x T)

/-- The vector of all source-trial verdicts in a compact repetition seed. -/
def repeatVotes (tm : NTM n) (x : List Bool) (k T : ℕ)
    (seed : Fin (k * T) → Bool) : Fin k → Bool :=
  fun j => repeatTrialVote tm x k T seed j

/--
@isnad1 id=iff.0h7v.s7.9901c973bbac from=translated src=- shape=d38b19cb vocab=5cf4eac2
-/
@[simp] theorem repeatTrialVote_eq_true_iff (tm : NTM n) (x : List Bool)
    (seed : Fin (k * T) → Bool) (j : Fin k) :
    repeatTrialVote tm x k T seed j = true ↔
      blocksEquiv k T seed j ∈ repeatAcceptEvent tm x T := by
  simp [repeatTrialVote]

/-- `votes` contains the expected verdicts below `m` and `false` in every
not-yet-completed trial slot. -/
def RepeatVotesThrough (expected votes : Fin k → Bool) (m : ℕ) : Prop :=
  ∀ i, votes i = if i.val < m then expected i else false

/--
@isnad1 id=repeatvo.0h2v.s4.52d322d1a0d7 from=translated src=- shape=892f3ff2 vocab=5ca5d4a1
-/
theorem RepeatVotesThrough.zero (expected : Fin k → Bool) :
    RepeatVotesThrough expected (fun _ => false) 0 := by
  intro i
  simp

/-- Recording trial `m` advances the vote invariant by one slot.
@isnad1 id=repeatvo.2h4v.s5.870b8760919c from=translated src=- shape=dd9a414b vocab=62a77979
-/
theorem RepeatVotesThrough.update {expected votes : Fin k → Bool} {m : ℕ}
    (hm : m < k) (h : RepeatVotesThrough expected votes m) :
    RepeatVotesThrough expected
      (Function.update votes ⟨m, hm⟩ (expected ⟨m, hm⟩)) (m + 1) := by
  intro i
  by_cases him : i = ⟨m, hm⟩
  · subst i
    simp
  · rw [Function.update_of_ne him]
    rw [h i]
    have hval : i.val ≠ m := by
      intro heq
      apply him
      apply Fin.ext
      exact heq
    by_cases hi : i.val < m
    · have hi' : i.val < m + 1 := by omega
      simp [hi, hi']
    · have hi' : ¬i.val < m + 1 := by omega
      simp [hi, hi']

/-- Once all `k` trials are recorded, the finite-control vector is the full
expected vote vector. -/
theorem RepeatVotesThrough.eq_expected {expected votes : Fin k → Bool}
    (h : RepeatVotesThrough expected votes k) : votes = expected := by
  funext i
  rw [h i]
  simp [i.isLt]

end NTM

end Complexity
