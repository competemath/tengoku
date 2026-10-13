/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Classes.AverageCase.Heuristic.Defs
public import Tengoku.Complexitylib.Complexitylib.Classes.AverageCase.Heuristic.Internal

/-!
# Errorless average-case heuristics

This module exposes the exact errorless-heuristic semantics used in average-case
complexity: globally sound yes/no/failure answers, polynomial runtime through a
canonical `FP` output codec, and slice-wise failure probability over arbitrary
finite uniform-seed ensembles. It also defines `AvgPAt δ` and the
inverse-polynomial intersection `AvgP` for distributional problems.
-/

public section

namespace Complexity

namespace HeuristicAnswer

/-- Canonical heuristic answers round-trip through their binary codec.
@isnad1 id=eq.0h1v.s3.de44299fe198 from=translated src=- shape=edb93955 vocab=3923d347
-/
@[simp] theorem decode?_encode (answer : HeuristicAnswer) :
    decode? answer.encode = some answer :=
  decode?_encode_internal answer

/-- The canonical three-answer encoding is injective.
@isnad1 id=injectiv.0h0v.s2.4d676530d8c3 from=translated src=- shape=4b736592 vocab=089adea4
-/
theorem encode_injective : Function.Injective encode :=
  encode_injective_internal

/-- Every canonical heuristic-answer code has length at most one.
@isnad1 id=le.0h1v.s3.deedb7949ae6 from=translated src=- shape=8e1bdd70 vocab=ecc38d89
-/
theorem encode_length_le_one (answer : HeuristicAnswer) :
    answer.encode.length ≤ 1 :=
  encode_length_le_one_internal answer

/-- Complementing an answer twice returns the original answer.
@isnad1 id=eq.0h1v.s3.aabf5cfd7232 from=translated src=- shape=47dcad53 vocab=6bddaf7d
-/
@[simp] theorem complement_complement (answer : HeuristicAnswer) :
    answer.complement.complement = answer :=
  complement_complement_internal answer

/-- Complement preserves and reflects explicit failure.
@isnad1 id=iff.0h1v.s3.cfb38813f627 from=translated src=- shape=87a471b4 vocab=c7828d52
-/
@[simp] theorem complement_eq_failure_iff (answer : HeuristicAnswer) :
    answer.complement = .failure ↔ answer = .failure :=
  complement_eq_failure_iff_internal answer

/-- Complementing a sound answer gives a sound answer for the negated truth
value.
@isnad1 id=correctf.1h2v.s3.1a77e7ec488e from=translated src=- shape=7181b802 vocab=e62e044f
-/
theorem CorrectFor.complement {answer : HeuristicAnswer} {truth : Prop}
    (hcorrect : answer.CorrectFor truth) :
    answer.complement.CorrectFor (¬ truth) :=
  hcorrect.complement_internal

end HeuristicAnswer

namespace HeuristicAlgorithm

/-- Complementing a globally errorless heuristic yields an errorless heuristic
for the complement language.
@isnad1 id=iserrorl.1h2v.s4.3ea42ec02aa3 from=translated src=- shape=5fb129d5 vocab=a4b0c4ab
-/
theorem IsErrorlessFor.complement {A : HeuristicAlgorithm} {L : Language}
    (herrorless : A.IsErrorlessFor L) :
    A.complement.IsErrorlessFor Lᶜ :=
  herrorless.complement_internal

/-- Complementing a heuristic preserves its failure event pointwise.
@isnad1 id=iff.0h2v.s4.c9f92136b1e9 from=translated src=- shape=94da4bda vocab=11bc4efb
-/
@[simp] theorem complement_apply_eq_failure_iff
    (A : HeuristicAlgorithm) (x : List Bool) :
    A.complement x = .failure ↔ A x = .failure :=
  complement_apply_eq_failure_iff_internal A x

/-- Failure probability is nonnegative.
@isnad1 id=le.0h3v.s4.a593d3dca77b from=translated src=- shape=9fb8395b vocab=549cb834
-/
theorem failureProbability_nonneg (D : FiniteEnsemble (List Bool))
    (A : HeuristicAlgorithm) (n : ℕ) :
    0 ≤ A.failureProbability D n :=
  failureProbability_nonneg_internal D A n

/-- Failure probability is at most one.
@isnad1 id=le.0h3v.s4.8ed3ed615943 from=translated src=- shape=44b143ee vocab=549cb834
-/
theorem failureProbability_le_one (D : FiniteEnsemble (List Bool))
    (A : HeuristicAlgorithm) (n : ℕ) :
    A.failureProbability D n ≤ 1 :=
  failureProbability_le_one_internal D A n

/-- Every answer probability is nonnegative.
@isnad1 id=le.0h4v.s4.a42054018c4d from=translated src=- shape=21a0baba vocab=a717b235
-/
theorem answerProbability_nonneg (D : FiniteEnsemble (List Bool))
    (A : HeuristicAlgorithm) (answer : HeuristicAnswer) (n : ℕ) :
    0 ≤ A.answerProbability D answer n :=
  answerProbability_nonneg_internal D A answer n

/-- Every answer probability is at most one.
@isnad1 id=le.0h4v.s4.f21d20164df5 from=translated src=- shape=d4243a18 vocab=a717b235
-/
theorem answerProbability_le_one (D : FiniteEnsemble (List Bool))
    (A : HeuristicAlgorithm) (answer : HeuristicAnswer) (n : ℕ) :
    A.answerProbability D answer n ≤ 1 :=
  answerProbability_le_one_internal D A answer n

/-- Failure probability is the probability of the `failure` answer.
@isnad1 id=eq.0h3v.s4.e5ff21318695 from=translated src=- shape=318235bf vocab=f246d85d
-/
theorem failureProbability_eq_answerProbability
    (D : FiniteEnsemble (List Bool)) (A : HeuristicAlgorithm) (n : ℕ) :
    A.failureProbability D n = A.answerProbability D .failure n :=
  failureProbability_eq_answerProbability_internal D A n

/-- An errorless heuristic correctly rejects mass at least one minus the
language mass and its failure mass.
@isnad1 id=le.1h4v.s5.217b4705dece from=translated src=- shape=2b097d59 vocab=4ec8c0be
-/
theorem IsErrorlessFor.one_sub_languageProbability_sub_failure_le_reject
    {A : HeuristicAlgorithm} {L : Language}
    (herrorless : A.IsErrorlessFor L)
    (D : FiniteEnsemble (List Bool)) (n : ℕ) :
    1 - D.languageProbability L n - A.failureProbability D n ≤
      A.answerProbability D .reject n :=
  herrorless.one_sub_languageProbability_sub_failure_le_reject_internal D n

/-- Complementing a heuristic preserves its failure probability exactly.
@isnad1 id=eq.0h3v.s4.0a1315eebaf8 from=translated src=- shape=373a519f vocab=642fcf06
-/
@[simp] theorem failureProbability_complement
    (D : FiniteEnsemble (List Bool)) (A : HeuristicAlgorithm) (n : ℕ) :
    A.complement.failureProbability D n = A.failureProbability D n :=
  failureProbability_complement_internal D A n

/-- A failure guarantee remains true under a pointwise weaker bound.
@isnad1 id=failswit.2h4v.s5.72c0c60363e3 from=translated src=- shape=3298d698 vocab=7eb6d479
-/
theorem FailsWithProbabilityAtMost.mono
    {D : FiniteEnsemble (List Bool)} {A : HeuristicAlgorithm} {δ ε : ℕ → ℚ}
    (hfailure : A.FailsWithProbabilityAtMost D δ)
    (hδε : ∀ n, δ n ≤ ε n) :
    A.FailsWithProbabilityAtMost D ε :=
  hfailure.mono_internal hδε

/-- Complementing a heuristic preserves every failure guarantee.
@isnad1 id=failswit.1h3v.s4.1b4d83234cd6 from=translated src=- shape=0590e556 vocab=a6843241
-/
theorem FailsWithProbabilityAtMost.complement
    {D : FiniteEnsemble (List Bool)} {A : HeuristicAlgorithm} {δ : ℕ → ℚ}
    (hfailure : A.FailsWithProbabilityAtMost D δ) :
    A.complement.FailsWithProbabilityAtMost D δ :=
  hfailure.complement_internal

/-- The decision-function adapter has its advertised pointwise semantics.
@isnad1 id=eq.0h2v.s4.03c46e9f2c21 from=translated src=- shape=7aaa08a5 vocab=480f6fca
-/
theorem ofDecision_apply (decide : List Bool → Bool) (x : List Bool) :
    ofDecision decide x = if decide x then .accept else .reject :=
  ofDecision_apply_internal decide x

/-- The canonical encoding of a decision adapter is its singleton Boolean
output.
@isnad1 id=eq.0h1v.s4.53893b821f1a from=translated src=- shape=4e2bb622 vocab=57651276
-/
theorem ofDecision_encoded (decide : List Bool → Bool) :
    (ofDecision decide).encoded = fun x => [decide x] :=
  ofDecision_encoded_internal decide

/-- A decision adapter runs in polynomial time whenever its singleton Boolean
output function belongs to `FP`.
@isnad1 id=ispolyno.1h1v.s5.3c11ca475303 from=translated src=- shape=6a563d43 vocab=d37eb2cf
-/
theorem ofDecision_isPolynomialTime {decide : List Bool → Bool}
    (htime : (fun x => [decide x]) ∈ FP) :
    (ofDecision decide).IsPolynomialTime :=
  ofDecision_isPolynomialTime_internal htime

/-- An exact Boolean decision function induces a globally errorless heuristic.
@isnad1 id=iserrorl.1h2v.s4.efccd1ef62b7 from=translated src=- shape=788fcd54 vocab=ced1eec7
-/
theorem ofDecision_isErrorlessFor {decide : List Bool → Bool} {L : Language}
    (hdecide : ∀ x, decide x = true ↔ x ∈ L) :
    (ofDecision decide).IsErrorlessFor L :=
  ofDecision_isErrorlessFor_internal hdecide

/-- A total decision adapter has zero failure probability on every ensemble
slice.
@isnad1 id=eq.0h3v.s4.7fbef97a4c31 from=translated src=- shape=f7c4a066 vocab=bab05826
-/
@[simp] theorem ofDecision_failureProbability
    (D : FiniteEnsemble (List Bool)) (decide : List Bool → Bool) (n : ℕ) :
    (ofDecision decide).failureProbability D n = 0 :=
  ofDecision_failureProbability_internal D decide n

/-- A total decision adapter meets the zero failure bound.
@isnad1 id=failswit.0h2v.s4.ff0565a22e68 from=translated src=- shape=7a944cb4 vocab=c872a78e
-/
theorem ofDecision_failsWithProbabilityAtMost_zero
    (D : FiniteEnsemble (List Bool)) (decide : List Bool → Bool) :
    (ofDecision decide).FailsWithProbabilityAtMost D (fun _ => 0) :=
  ofDecision_failsWithProbabilityAtMost_zero_internal D decide

end HeuristicAlgorithm

/-- The total inverse-polynomial failure target is nonnegative.
@isnad1 id=le.0h2v.s3.4c5ebdb3cc00 from=translated src=- shape=5ffe46ab vocab=650150d4
-/
theorem inversePolynomialFailure_nonneg (c n : ℕ) :
    0 ≤ inversePolynomialFailure c n :=
  inversePolynomialFailure_nonneg_internal c n

/-- The total inverse-polynomial failure target is at most one.
@isnad1 id=le.0h2v.s3.2304d84b7fd3 from=translated src=- shape=628a94f6 vocab=650150d4
-/
theorem inversePolynomialFailure_le_one (c n : ℕ) :
    inversePolynomialFailure c n ≤ 1 :=
  inversePolynomialFailure_le_one_internal c n

/-- `AvgPAt` is monotone in its allowed failure probability.
@isnad1 id=le.1h2v.s4.3ab553911f6f from=translated src=- shape=3879634c vocab=c8174eb9
-/
theorem AvgPAt_mono {δ ε : ℕ → ℚ} (hδε : ∀ n, δ n ≤ ε n) :
    AvgPAt δ ⊆ AvgPAt ε :=
  AvgPAt_mono_internal hδε

/-- Membership in `AvgP` means meeting every total inverse-polynomial failure
target.
@isnad1 id=iff.0h1v.s4.6ae2c56015f0 from=translated src=- shape=ebfe2f9b vocab=f96b857c
-/
theorem mem_AvgP_iff (problem : DistributionalProblem) :
    problem ∈ AvgP ↔
      ∀ c, problem ∈ AvgPAt (inversePolynomialFailure c) :=
  mem_AvgP_iff_internal problem

namespace DistributionalProblem

/-- Any exact polynomial-time Boolean decision function gives a zero-failure
member of `AvgPAt δ` for every nonnegative failure allowance.
@isnad1 id=mem.3h3v.s6.2be5747c9c87 from=translated src=- shape=5189d648 vocab=ec6b1c69
-/
theorem mem_AvgPAt_of_decision (problem : DistributionalProblem)
    (δ : ℕ → ℚ) (decide : List Bool → Bool)
    (htime : (fun x => [decide x]) ∈ FP)
    (hdecide : ∀ x, decide x = true ↔ x ∈ problem.language)
    (hδ : ∀ n, 0 ≤ δ n) :
    problem ∈ AvgPAt δ :=
  problem.mem_AvgPAt_of_decision_internal δ decide htime hdecide hδ

/-- Any exact polynomial-time Boolean decision function solves the same language
errorlessly on every distribution ensemble, hence places the distributional
problem in `AvgP`.
@isnad1 id=mem.2h2v.s6.6f1a6a62ff33 from=translated src=- shape=540811a9 vocab=7ea91a18
-/
theorem mem_AvgP_of_decision (problem : DistributionalProblem)
    (decide : List Bool → Bool)
    (htime : (fun x => [decide x]) ∈ FP)
    (hdecide : ∀ x, decide x = true ↔ x ∈ problem.language) :
    problem ∈ AvgP :=
  problem.mem_AvgP_of_decision_internal decide htime hdecide

end DistributionalProblem

end Complexity
