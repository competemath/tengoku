/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.MINCKT.Gap.Difference.SoI.Unconditional.Slack.Defs
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.MINCKT.Gap.Difference.SoI.Unconditional.Iterated.Internal
import Tengoku.Complexitylib.Complexitylib.Metacomplexity.Kolmogorov.Internal
import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.OutputBounds

/-!
# Explicit slack amplification -- proof internals
-/

public section

namespace Complexity

namespace GapMINCKT

namespace DifferenceEstimator

namespace Unconditional

namespace Iterated

namespace Slack

/--
@isnad1 id=le.0h1v.s4.aef6402dc459 from=translated src=- shape=c9c13a30 vocab=f984f1a1
-/
theorem paddedTime_le_totalTime_internal (inst : MINCKT.Instance) :
    paddedTime inst ≤
      totalTime inst.output.length inst.condition.length inst.time := by
  exact paddedTime_le_total_internal inst

/--
@isnad1 id=le.0h6v.s4.9bb6a1eca1b7 from=translated src=- shape=8d56605a vocab=605a5317
-/
theorem finalClock_source_le_internal
    (clock : ℕ → ℕ) (additive compilerLoss : ℕ)
    (outputLength conditionLength time : ℕ) :
    time ≤ finalClock clock additive compilerLoss
      outputLength conditionLength time := by
  let total := totalTime outputLength conditionLength time
  let exponent := slackExponent clock additive compilerLoss
    outputLength conditionLength time
  have htime : time ≤ total + 1 := by
    dsimp [total, totalTime]
    omega
  have hright : total + 1 ≤
      (clockIterate clock 4 total + 1) * (total + 1) :=
    Nat.le_mul_of_pos_left _ (by omega)
  have hpow : 0 < 2 ^ exponent := Nat.pow_pos (by omega)
  exact htime.trans <| hright.trans <|
    Nat.le_mul_of_pos_left _ hpow

/--
@isnad1 id=le.0h6v.s5.74c3e4f56634 from=translated src=- shape=0038da2a vocab=24f8e787
-/
theorem finalClock_iterateFour_le_internal
    (clock : ℕ → ℕ) (additive compilerLoss : ℕ)
    (outputLength conditionLength time : ℕ) :
    clockIterate clock 4 (totalTime outputLength conditionLength time) ≤
      finalClock clock additive compilerLoss
        outputLength conditionLength time := by
  let total := totalTime outputLength conditionLength time
  let exponent := slackExponent clock additive compilerLoss
    outputLength conditionLength time
  have hright : clockIterate clock 4 total ≤
      (clockIterate clock 4 total + 1) * (total + 1) := by
    exact (Nat.le_add_right _ 1).trans <|
      Nat.le_mul_of_pos_right _ (by omega)
  have hpow : 0 < 2 ^ exponent := Nat.pow_pos (by omega)
  exact hright.trans (Nat.le_mul_of_pos_left _ hpow)

/--
@isnad1 id=le.0h6v.s5.59282a72cd04 from=translated src=- shape=5e68eb9f vocab=7d863e95
-/
theorem slackExponent_le_log_finalClock_internal
    (clock : ℕ → ℕ) (additive compilerLoss : ℕ)
    (outputLength conditionLength time : ℕ) :
    slackExponent clock additive compilerLoss
        outputLength conditionLength time ≤
      Nat.log 2 (finalClock clock additive compilerLoss
        outputLength conditionLength time) := by
  apply Nat.le_log_of_pow_le Nat.one_lt_two
  apply Nat.le_mul_of_pos_right
  exact Nat.mul_pos (by omega) (by omega)

/--
@isnad1 id=le.1h4v.s6.9dc230986553 from=translated src=- shape=d155b221 vocab=01548c9d
-/
theorem losses_le_slackExponent_internal
    {clock : ℕ → ℕ} (hclock : Monotone clock)
    (additive compilerLoss : ℕ) (inst : MINCKT.Instance) :
    Nat.log 2 (clockIterate clock 2 (paddedTime inst)) +
          logarithmicSoILoss clock additive
            (clockIterate clock 2 (paddedTime inst)) +
        correction clock compilerLoss inst ≤
      slackExponent clock additive compilerLoss inst.output.length
        inst.condition.length inst.time := by
  have htotal := paddedTime_le_totalTime_internal inst
  have htwo :
      Nat.log 2 (clockIterate clock 2 (paddedTime inst)) ≤
        Nat.log 2 (clockIterate clock 2
          (totalTime inst.output.length inst.condition.length inst.time) + 1) :=
    Nat.log_mono_right <|
      (clockIterate_monotone_internal hclock 2 htotal).trans
        (Nat.le_add_right _ 1)
  have hthree :
      Nat.log 2 (clockIterate clock 3 (paddedTime inst)) ≤
        Nat.log 2 (clockIterate clock 3
          (totalTime inst.output.length inst.condition.length inst.time) + 1) :=
    Nat.log_mono_right <|
      (clockIterate_monotone_internal hclock 3 htotal).trans
        (Nat.le_add_right _ 1)
  have hfour :
      Nat.log 2 (clockIterate clock 4 (paddedTime inst)) ≤
        Nat.log 2 (clockIterate clock 4
          (totalTime inst.output.length inst.condition.length inst.time) + 1) :=
    Nat.log_mono_right <|
      (clockIterate_monotone_internal hclock 4 htotal).trans
        (Nat.le_add_right _ 1)
  simp only [clockIterate] at htwo
  simp only [clockIterate] at hthree
  simp only [clockIterate] at hfour
  simp only [logarithmicSoILoss, correction, slackExponent, clockIterate]
  omega

/--
@isnad1 id=le.0h3v.s5.181164ff812e from=translated src=- shape=24353062 vocab=b4e037b9
-/
theorem upperLoss_budget_internal
    (clock : ℕ → ℕ) (compilerLoss : ℕ)
    (inst : MINCKT.Instance) :
    (ordinaryParameters clock).logarithmicSlack
          ((plan clock compilerLoss).conditionInput inst) +
        (plan clock compilerLoss).pairUpperLoss inst ≤
      (plan clock compilerLoss).correction inst := by
  simp [plan, Iterated.plan, correction, Plan.conditionInput,
    ordinaryParameters, GapMINKT.Logarithmic.Parameters.logarithmicSlack,
    GapMINKT.Logarithmic.Parameters.transformedTime, clockIterate]

/--
@isnad1 id=le.1h4v.s5.a1f0305c469b from=translated src=- shape=916946c8 vocab=30dd76f5
-/
theorem lowerLoss_budget_internal
    {clock : ℕ → ℕ} (hclock : Monotone clock)
    (additive compilerLoss : ℕ) (inst : MINCKT.Instance) :
    (ordinaryParameters clock).logarithmicSlack
          ((plan clock compilerLoss).pairInput inst) +
          logarithmicSoILoss clock additive
            ((plan clock compilerLoss).soiTime inst) +
        (plan clock compilerLoss).correction inst ≤
      (parameters clock additive compilerLoss).logarithmicSlack inst := by
  have hloss := losses_le_slackExponent_internal hclock additive compilerLoss inst
  have hslack := slackExponent_le_log_finalClock_internal clock additive
    compilerLoss inst.output.length inst.condition.length inst.time
  have h := hloss.trans hslack
  simp only [plan, Iterated.plan, Plan.pairInput, ordinaryParameters,
    GapMINKT.Logarithmic.Parameters.logarithmicSlack,
    GapMINKT.Logarithmic.Parameters.transformedTime] at h ⊢
  exact h

/--
@isnad1 id=compatib.2h7v.s6.13ff1a20fc2a from=translated src=- shape=ceca3132 vocab=5a01b467
-/
theorem IsRegularClock.compatible_internal
    {ordinaryTapes conditionalTapes : ℕ}
    {clock : ℕ → ℕ} {additive compilerLoss : ℕ}
    {ordinaryMachine : TM ordinaryTapes}
    {conditionalMachine : OracleTM conditionalTapes}
    (hclock : IsRegularClock clock)
    (hpair : ∀ inst,
      ordinaryMachine.timeBoundedKolmogorovComplexity
            (pair inst.output inst.condition)
              ((plan clock compilerLoss).pairInputTime inst) ≤
        inst.complexity conditionalMachine +
            ordinaryMachine.timeBoundedKolmogorovComplexity
              inst.condition inst.time +
          ((plan clock compilerLoss).pairUpperLoss inst : WithTop ℕ)) :
    Compatible (plan clock compilerLoss) ordinaryMachine conditionalMachine
      (ordinaryParameters clock) (parameters clock additive compilerLoss) clock
        (logarithmicSoILoss clock additive) := by
  constructor
  · intro inst
    have hthreeFour : clockIterate clock 3 (paddedTime inst) ≤
        clockIterate clock 4 (paddedTime inst) := hclock.dominates _
    have hfourTotal := clockIterate_monotone_internal hclock.monotone 4
      (paddedTime_le_totalTime_internal inst)
    exact (hthreeFour.trans hfourTotal).trans <|
      finalClock_iterateFour_le_internal clock additive compilerLoss
        inst.output.length inst.condition.length inst.time
  · intro inst
    exact (paddedTime_size_le_internal inst).trans
      (clockIterate_dominates_internal hclock.dominates 2 _)
  · intro inst
    rfl
  · intro inst
    exact (clockIterate_monotone_internal hclock.monotone 4
      (paddedTime_le_totalTime_internal inst)).trans <|
        finalClock_iterateFour_le_internal clock additive compilerLoss
          inst.output.length inst.condition.length inst.time
  · intro inst
    rfl
  · exact hpair
  · exact upperLoss_budget_internal clock compilerLoss
  · exact lowerLoss_budget_internal hclock.monotone additive compilerLoss

/--
@isnad1 id=compatib.2h8v.s5.de48ba7d1bd2 from=translated src=- shape=2ff4cd59 vocab=4cd15a36
-/
theorem IsRegularClock.compatible_of_pairComposition_internal
    {ordinaryTapes conditionalTapes : ℕ}
    {clock : ℕ → ℕ} {additive compilerLoss : ℕ}
    {composition : PairCompositionPlan}
    {ordinaryMachine : TM ordinaryTapes}
    {conditionalMachine : OracleTM conditionalTapes}
    (hclock : IsRegularClock clock)
    (hsupports : SupportsPairUpper (plan clock compilerLoss) composition
      ordinaryMachine conditionalMachine) :
    Compatible (plan clock compilerLoss) ordinaryMachine conditionalMachine
      (ordinaryParameters clock) (parameters clock additive compilerLoss) clock
        (logarithmicSoILoss clock additive) :=
  Slack.IsRegularClock.compatible_internal hclock
    hsupports.pair_upper_internal

/--
@isnad1 id=le.1h4v.s4.fa983c66347e from=translated src=- shape=e670c9a8 vocab=0c0a53e1
-/
theorem length_le_of_timeBoundedKolmogorovComplexity_ne_top_internal
    {tapes : ℕ} {machine : TM tapes} {output : List Bool} {time : ℕ}
    (hfinite : machine.timeBoundedKolmogorovComplexity output time ≠ ⊤) :
    output.length ≤ time := by
  by_contra hlt
  apply hfinite
  rw [TM.timeBoundedKolmogorovComplexity_eq_top_iff_internal]
  rintro ⟨program, c, steps, hsteps, hrun, -, hout⟩
  have hlength := TM.output_length_le_of_reachesIn hrun hout
  omega

/--
@isnad1 id=eq.0h3v.s5.b73dd196882b from=translated src=- shape=b176c487 vocab=4783952a
-/
theorem pairInput_replicate_internal (clock : ℕ → ℕ)
    (compilerLoss length : ℕ) :
    (plan clock compilerLoss).pairInput ⟨List.replicate length true, [], 0⟩ =
      ⟨pair (List.replicate length true) [], clock length⟩ := by
  simp [Plan.pairInput, plan, Iterated.plan, clockIterate, paddedTime]

/--
@isnad1 id=isestima.0h3v.s4.145aae25a920 from=translated src=- shape=63d6140d vocab=c9827f66
-/
theorem pairInput_replicate_isEstimatorQuery_internal (clock : ℕ → ℕ)
    (compilerLoss length : ℕ) :
    (plan clock compilerLoss).IsEstimatorQuery
      ⟨pair (List.replicate length true) [], clock length⟩ :=
  ⟨⟨List.replicate length true, [], 0⟩,
    Or.inl (pairInput_replicate_internal clock compilerLoss length).symm⟩

/--
@isnad1 id=le.1h6v.s5.97ae1c41f5f1 from=translated src=- shape=0dceae39 vocab=c3cf12fd
-/
theorem two_mul_add_two_le_clock_clock_of_satisfiesBoundsOn_internal
    {tapes : ℕ} {machine : TM tapes} {clock : ℕ → ℕ} {compilerLoss : ℕ}
    {estimate : GapMINKT.Logarithmic.Estimator}
    (hestimate : estimate.SatisfiesBoundsOn machine (ordinaryParameters clock)
      (plan clock compilerLoss).IsEstimatorQuery) (length : ℕ) :
    2 * length + 2 ≤ clock (clock length) := by
  have hupper := (hestimate _
    (pairInput_replicate_isEstimatorQuery_internal clock compilerLoss length)).2
  have hfinite : machine.timeBoundedKolmogorovComplexity
      (pair (List.replicate length true) []) (clock (clock length)) ≠ ⊤ := by
    intro htop
    change machine.timeBoundedKolmogorovComplexity
      (pair (List.replicate length true) []) (clock (clock length)) ≤ _ at hupper
    rw [htop] at hupper
    exact WithTop.not_top_le_coe _ hupper
  simpa [pair_length] using
    length_le_of_timeBoundedKolmogorovComplexity_ne_top_internal hfinite

/--
@isnad1 id=le.1h5v.s6.59e18339f9c1 from=translated src=- shape=50867371 vocab=b7545614
-/
theorem two_mul_add_two_le_clock_of_forall_ne_top_internal
    {tapes : ℕ} {machine : TM tapes} {clock : ℕ → ℕ} {compilerLoss : ℕ}
    (hfinite : ∀ query : MINKT.Instance,
      (plan clock compilerLoss).IsEstimatorQuery query →
      machine.timeBoundedKolmogorovComplexity query.output query.time ≠ ⊤)
    (length : ℕ) :
    2 * length + 2 ≤ clock length := by
  simpa [pair_length] using
    length_le_of_timeBoundedKolmogorovComplexity_ne_top_internal (hfinite _
      (pairInput_replicate_isEstimatorQuery_internal clock compilerLoss length))

/--
@isnad1 id=not.0h4v.s4.1fc44c7262b4 from=translated src=- shape=dcc8bf56 vocab=3700439f
-/
theorem not_satisfiesBoundsOn_plan_id_internal {tapes : ℕ}
    (machine : TM tapes) (compilerLoss : ℕ)
    (estimate : GapMINKT.Logarithmic.Estimator) :
    ¬ estimate.SatisfiesBoundsOn machine (ordinaryParameters id)
      (plan id compilerLoss).IsEstimatorQuery := fun hestimate => by
  have hclock :=
    two_mul_add_two_le_clock_clock_of_satisfiesBoundsOn_internal hestimate 0
  simp at hclock

end Slack

end Iterated

end Unconditional

end DifferenceEstimator

end GapMINCKT

end Complexity
