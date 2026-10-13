/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Classes.AverageCase.Heuristic.Defs
import Tengoku.Complexitylib.Complexitylib.Classes.AverageCase.FiniteEnsemble.Internal

/-!
# Errorless average-case heuristics -- proof internals

This layer proves codec exactness, semantic soundness of complement and decision
adapters, and the elementary probability/class monotonicity laws.
-/

public section

namespace Complexity

namespace HeuristicAnswer

/--
@isnad1 id=eq.0h1v.s3.de44299fe198 from=translated src=- shape=edb93955 vocab=3923d347
-/
theorem decode?_encode_internal (answer : HeuristicAnswer) :
    decode? answer.encode = some answer := by
  cases answer <;> rfl

/--
@isnad1 id=injectiv.0h0v.s2.4d676530d8c3 from=translated src=- shape=4b736592 vocab=089adea4
-/
theorem encode_injective_internal : Function.Injective encode := by
  intro a b hab
  have := congrArg decode? hab
  simpa only [decode?_encode_internal, Option.some.injEq] using this

/--
@isnad1 id=le.0h1v.s3.deedb7949ae6 from=translated src=- shape=8e1bdd70 vocab=ecc38d89
-/
theorem encode_length_le_one_internal (answer : HeuristicAnswer) :
    answer.encode.length ≤ 1 := by
  cases answer <;> simp [encode]

/--
@isnad1 id=eq.0h1v.s3.aabf5cfd7232 from=translated src=- shape=47dcad53 vocab=6bddaf7d
-/
theorem complement_complement_internal (answer : HeuristicAnswer) :
    answer.complement.complement = answer := by
  cases answer <;> rfl

/--
@isnad1 id=iff.0h1v.s3.cfb38813f627 from=translated src=- shape=87a471b4 vocab=c7828d52
-/
theorem complement_eq_failure_iff_internal (answer : HeuristicAnswer) :
    answer.complement = .failure ↔ answer = .failure := by
  cases answer <;> simp [complement]

/--
@isnad1 id=correctf.1h2v.s3.1a77e7ec488e from=translated src=- shape=7181b802 vocab=e62e044f
-/
theorem CorrectFor.complement_internal {answer : HeuristicAnswer} {truth : Prop}
    (hcorrect : answer.CorrectFor truth) :
    answer.complement.CorrectFor (¬ truth) := by
  cases answer <;> simp_all [CorrectFor, complement]

end HeuristicAnswer

namespace HeuristicAlgorithm

/--
@isnad1 id=iserrorl.1h2v.s4.3ea42ec02aa3 from=translated src=- shape=5fb129d5 vocab=a4b0c4ab
-/
theorem IsErrorlessFor.complement_internal {A : HeuristicAlgorithm}
    {L : Language} (herrorless : A.IsErrorlessFor L) :
    A.complement.IsErrorlessFor Lᶜ := by
  intro x
  exact (herrorless x).complement_internal

/--
@isnad1 id=iff.0h2v.s4.c9f92136b1e9 from=translated src=- shape=94da4bda vocab=11bc4efb
-/
theorem complement_apply_eq_failure_iff_internal
    (A : HeuristicAlgorithm) (x : List Bool) :
    A.complement x = .failure ↔ A x = .failure := by
  exact HeuristicAnswer.complement_eq_failure_iff_internal (A x)

/--
@isnad1 id=le.0h3v.s4.a593d3dca77b from=translated src=- shape=9fb8395b vocab=549cb834
-/
theorem failureProbability_nonneg_internal
    (D : FiniteEnsemble (List Bool)) (A : HeuristicAlgorithm) (n : ℕ) :
    0 ≤ A.failureProbability D n :=
  D.probability_nonneg_internal n _

/--
@isnad1 id=le.0h3v.s4.8ed3ed615943 from=translated src=- shape=44b143ee vocab=549cb834
-/
theorem failureProbability_le_one_internal
    (D : FiniteEnsemble (List Bool)) (A : HeuristicAlgorithm) (n : ℕ) :
    A.failureProbability D n ≤ 1 :=
  D.probability_le_one_internal n _

/--
@isnad1 id=le.0h4v.s4.a42054018c4d from=translated src=- shape=21a0baba vocab=a717b235
-/
theorem answerProbability_nonneg_internal
    (D : FiniteEnsemble (List Bool)) (A : HeuristicAlgorithm)
    (answer : HeuristicAnswer) (n : ℕ) :
    0 ≤ A.answerProbability D answer n :=
  D.probability_nonneg_internal n _

/--
@isnad1 id=le.0h4v.s4.f21d20164df5 from=translated src=- shape=d4243a18 vocab=a717b235
-/
theorem answerProbability_le_one_internal
    (D : FiniteEnsemble (List Bool)) (A : HeuristicAlgorithm)
    (answer : HeuristicAnswer) (n : ℕ) :
    A.answerProbability D answer n ≤ 1 :=
  D.probability_le_one_internal n _

/--
@isnad1 id=eq.0h3v.s4.e5ff21318695 from=translated src=- shape=318235bf vocab=f246d85d
-/
theorem failureProbability_eq_answerProbability_internal
    (D : FiniteEnsemble (List Bool)) (A : HeuristicAlgorithm) (n : ℕ) :
    A.failureProbability D n = A.answerProbability D .failure n :=
  rfl

/--
@isnad1 id=le.1h4v.s5.217b4705dece from=translated src=- shape=2b097d59 vocab=4ec8c0be
-/
theorem IsErrorlessFor.one_sub_languageProbability_sub_failure_le_reject_internal
    {A : HeuristicAlgorithm} {L : Language}
    (herrorless : A.IsErrorlessFor L)
    (D : FiniteEnsemble (List Bool)) (n : ℕ) :
    1 - D.languageProbability L n - A.failureProbability D n ≤
      A.answerProbability D .reject n := by
  classical
  unfold FiniteEnsemble.languageProbability failureProbability answerProbability
  have hcover : ∀ x : List Bool, True →
      x ∈ L ∨ A x = .failure ∨ A x = .reject := by
    intro x _hx
    cases hanswer : A x with
    | accept =>
        left
        simpa only [IsErrorlessFor, hanswer, HeuristicAnswer.CorrectFor] using
          herrorless x
    | reject => exact Or.inr (Or.inr rfl)
    | failure => exact Or.inr (Or.inl rfl)
  have htotal : 1 ≤ D.probability n
      (fun x => x ∈ L ∨ A x = .failure ∨ A x = .reject) := by
    have hmono := D.probability_mono_internal n
      (fun _x : List Bool => True)
      (fun x => x ∈ L ∨ A x = .failure ∨ A x = .reject) hcover
    simpa only [D.probability_true_internal] using hmono
  have houter := D.probability_or_le_internal n
    (fun x => x ∈ L) (fun x => A x = .failure ∨ A x = .reject)
  have hinner := D.probability_or_le_internal n
    (fun x => A x = .failure) (fun x => A x = .reject)
  linarith

/--
@isnad1 id=eq.0h3v.s4.0a1315eebaf8 from=translated src=- shape=373a519f vocab=642fcf06
-/
theorem failureProbability_complement_internal
    (D : FiniteEnsemble (List Bool)) (A : HeuristicAlgorithm) (n : ℕ) :
    A.complement.failureProbability D n = A.failureProbability D n := by
  apply D.probability_congr_internal
  intro x
  exact complement_apply_eq_failure_iff_internal A x

/--
@isnad1 id=failswit.2h4v.s5.72c0c60363e3 from=translated src=- shape=3298d698 vocab=7eb6d479
-/
theorem FailsWithProbabilityAtMost.mono_internal
    {D : FiniteEnsemble (List Bool)} {A : HeuristicAlgorithm} {δ ε : ℕ → ℚ}
    (hfailure : A.FailsWithProbabilityAtMost D δ)
    (hδε : ∀ n, δ n ≤ ε n) :
    A.FailsWithProbabilityAtMost D ε := by
  intro n
  exact (hfailure n).trans (hδε n)

/--
@isnad1 id=failswit.1h3v.s4.1b4d83234cd6 from=translated src=- shape=0590e556 vocab=a6843241
-/
theorem FailsWithProbabilityAtMost.complement_internal
    {D : FiniteEnsemble (List Bool)} {A : HeuristicAlgorithm} {δ : ℕ → ℚ}
    (hfailure : A.FailsWithProbabilityAtMost D δ) :
    A.complement.FailsWithProbabilityAtMost D δ := by
  intro n
  rw [failureProbability_complement_internal]
  exact hfailure n

/--
@isnad1 id=eq.0h2v.s4.03c46e9f2c21 from=translated src=- shape=7aaa08a5 vocab=480f6fca
-/
theorem ofDecision_apply_internal (decide : List Bool → Bool) (x : List Bool) :
    ofDecision decide x = if decide x then .accept else .reject :=
  rfl

/--
@isnad1 id=eq.0h1v.s4.53893b821f1a from=translated src=- shape=4e2bb622 vocab=57651276
-/
theorem ofDecision_encoded_internal (decide : List Bool → Bool) :
    (ofDecision decide).encoded = fun x => [decide x] := by
  funext x
  cases h : decide x <;> simp [ofDecision, encoded, HeuristicAnswer.encode, h]

/--
@isnad1 id=ispolyno.1h1v.s5.3c11ca475303 from=translated src=- shape=6a563d43 vocab=d37eb2cf
-/
theorem ofDecision_isPolynomialTime_internal {decide : List Bool → Bool}
    (htime : (fun x => [decide x]) ∈ FP) :
    (ofDecision decide).IsPolynomialTime := by
  rw [IsPolynomialTime, ofDecision_encoded_internal]
  exact htime

/--
@isnad1 id=iserrorl.1h2v.s4.efccd1ef62b7 from=translated src=- shape=788fcd54 vocab=ced1eec7
-/
theorem ofDecision_isErrorlessFor_internal {decide : List Bool → Bool}
    {L : Language} (hdecide : ∀ x, decide x = true ↔ x ∈ L) :
    (ofDecision decide).IsErrorlessFor L := by
  intro x
  cases h : decide x
  · simp only [ofDecision, h, Bool.false_eq_true, ↓reduceIte,
      HeuristicAnswer.CorrectFor]
    intro hx
    have : decide x = true := (hdecide x).mpr hx
    simp [h] at this
  · simp only [ofDecision, h, ↓reduceIte, HeuristicAnswer.CorrectFor]
    exact (hdecide x).mp h

/--
@isnad1 id=eq.0h3v.s4.7fbef97a4c31 from=translated src=- shape=f7c4a066 vocab=bab05826
-/
theorem ofDecision_failureProbability_internal
    (D : FiniteEnsemble (List Bool)) (decide : List Bool → Bool) (n : ℕ) :
    (ofDecision decide).failureProbability D n = 0 := by
  unfold failureProbability
  have himpossible : ∀ x : List Bool, ofDecision decide x ≠ .failure := by
    intro x
    cases h : decide x <;> simp [ofDecision, h]
  apply le_antisymm
  · have hzero := D.probability_mono_internal n
      (fun x => ofDecision decide x = .failure) (fun _ => False)
      (fun x hx => himpossible x hx)
    exact hzero.trans_eq (D.probability_false_internal n)
  · exact D.probability_nonneg_internal n _

/--
@isnad1 id=failswit.0h2v.s4.ff0565a22e68 from=translated src=- shape=7a944cb4 vocab=c872a78e
-/
theorem ofDecision_failsWithProbabilityAtMost_zero_internal
    (D : FiniteEnsemble (List Bool)) (decide : List Bool → Bool) :
    (ofDecision decide).FailsWithProbabilityAtMost D (fun _ => 0) := by
  intro n
  rw [ofDecision_failureProbability_internal]

end HeuristicAlgorithm

/--
@isnad1 id=le.0h2v.s3.4c5ebdb3cc00 from=translated src=- shape=5ffe46ab vocab=650150d4
-/
theorem inversePolynomialFailure_nonneg_internal (c n : ℕ) :
    0 ≤ inversePolynomialFailure c n := by
  unfold inversePolynomialFailure
  positivity

/--
@isnad1 id=le.0h2v.s3.2304d84b7fd3 from=translated src=- shape=628a94f6 vocab=650150d4
-/
theorem inversePolynomialFailure_le_one_internal (c n : ℕ) :
    inversePolynomialFailure c n ≤ 1 := by
  unfold inversePolynomialFailure
  have hbase : (1 : ℚ) ≤ Nat.max 1 n := by
    exact_mod_cast Nat.le_max_left 1 n
  have hpow : (1 : ℚ) ≤ (Nat.max 1 n : ℚ) ^ c := by
    exact one_le_pow₀ hbase
  simpa using one_div_le_one_div_of_le (a := (1 : ℚ)) (by norm_num) hpow

/--
@isnad1 id=le.1h2v.s4.3ab553911f6f from=translated src=- shape=3879634c vocab=c8174eb9
-/
theorem AvgPAt_mono_internal {δ ε : ℕ → ℚ} (hδε : ∀ n, δ n ≤ ε n) :
    AvgPAt δ ⊆ AvgPAt ε := by
  intro problem hproblem
  obtain ⟨A, htime, herrorless, hfailure⟩ := hproblem
  exact ⟨A, htime, herrorless, hfailure.mono_internal hδε⟩

/--
@isnad1 id=iff.0h1v.s4.6ae2c56015f0 from=translated src=- shape=ebfe2f9b vocab=f96b857c
-/
theorem mem_AvgP_iff_internal (problem : DistributionalProblem) :
    problem ∈ AvgP ↔
      ∀ c, problem ∈ AvgPAt (inversePolynomialFailure c) := by
  simp [AvgP]

/--
@isnad1 id=mem.3h3v.s6.2be5747c9c87 from=translated src=- shape=5189d648 vocab=ec6b1c69
-/
theorem DistributionalProblem.mem_AvgPAt_of_decision_internal
    (problem : DistributionalProblem) (δ : ℕ → ℚ)
    (decide : List Bool → Bool)
    (htime : (fun x => [decide x]) ∈ FP)
    (hdecide : ∀ x, decide x = true ↔ x ∈ problem.language)
    (hδ : ∀ n, 0 ≤ δ n) :
    problem ∈ AvgPAt δ := by
  refine ⟨HeuristicAlgorithm.ofDecision decide,
    HeuristicAlgorithm.ofDecision_isPolynomialTime_internal htime,
    HeuristicAlgorithm.ofDecision_isErrorlessFor_internal hdecide, ?_⟩
  intro n
  rw [HeuristicAlgorithm.ofDecision_failureProbability_internal]
  exact hδ n

/--
@isnad1 id=mem.2h2v.s6.6f1a6a62ff33 from=translated src=- shape=540811a9 vocab=7ea91a18
-/
theorem DistributionalProblem.mem_AvgP_of_decision_internal
    (problem : DistributionalProblem) (decide : List Bool → Bool)
    (htime : (fun x => [decide x]) ∈ FP)
    (hdecide : ∀ x, decide x = true ↔ x ∈ problem.language) :
    problem ∈ AvgP := by
  rw [mem_AvgP_iff_internal]
  intro c
  exact problem.mem_AvgPAt_of_decision_internal
    (inversePolynomialFailure c) decide htime hdecide
    (inversePolynomialFailure_nonneg_internal c)

end Complexity
