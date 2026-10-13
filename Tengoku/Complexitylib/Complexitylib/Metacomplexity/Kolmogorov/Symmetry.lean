/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.Kolmogorov.Symmetry.Defs
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.Kolmogorov.Symmetry.Internal

/-!
# Time-bounded symmetry of information

This module exposes a machine-relative version of Hirahara's SoI hypothesis.
The lower-chain inequality is separate from the unconditional upper chain rule:
SoI is a hypothesis, while upper composition follows from an evaluator
contract. SoI is satisfiable (it holds trivially wherever the joint complexity
is `⊤`), so it only has content together with hypotheses that make the
machines capable; lemmas that need a finite joint complexity assume it
explicitly.

The polynomial package quantifies an identity-dominating, polynomially bounded
clock and retains an explicit additive constant next to its base-two logarithmic
loss. Later results must instantiate the ordinary and conditional evaluators;
no universality or Heuristica consequence is assumed here.
-/

public section

namespace Complexity

/-- The identity transform is an admissible Kolmogorov clock.
@isnad1 id=isadmiss.0h0v.s1.41e3d7b690ca from=translated src=- shape=87ceb31f vocab=e2877495
-/
theorem isAdmissibleKolmogorovClock_id :
    IsAdmissibleKolmogorovClock id :=
  isAdmissibleKolmogorovClock_id_internal

/-- On an admissible pair whose joint description is finite, SoI forces the
transformed conditional description to exist.
@isnad1 id=ne.3h9v.s6.ad898fad3159 from=translated src=- shape=140fafe0 vocab=35dc8158
-/
theorem TimeBoundedSymmetryOfInformation.conditional_ne_top
    {ordinaryTapes conditionalTapes : ℕ}
    {ordinaryMachine : TM ordinaryTapes}
    {conditionalMachine : OracleTM conditionalTapes}
    {clock loss : ℕ → ℕ}
    (hsoi : TimeBoundedSymmetryOfInformation ordinaryMachine
      conditionalMachine clock loss)
    {first condition : List Bool} {time : ℕ}
    (hsize : first.length + condition.length ≤ time)
    (hpair : ordinaryMachine.timeBoundedKolmogorovComplexity
      (pair first condition) time ≠ ⊤) :
    conditionalMachine.randomAccessConditionalTimeBoundedKolmogorovComplexity
      first condition (clock time) ≠ ⊤ :=
  hsoi.conditional_ne_top_internal hsize hpair

/-- On an admissible pair whose joint description is finite, SoI also forces
the transformed ordinary description of the condition to exist.
@isnad1 id=ne.3h9v.s6.ddb5d2372b88 from=translated src=- shape=82c1597e vocab=98a58814
-/
theorem TimeBoundedSymmetryOfInformation.condition_ne_top
    {ordinaryTapes conditionalTapes : ℕ}
    {ordinaryMachine : TM ordinaryTapes}
    {conditionalMachine : OracleTM conditionalTapes}
    {clock loss : ℕ → ℕ}
    (hsoi : TimeBoundedSymmetryOfInformation ordinaryMachine
      conditionalMachine clock loss)
    {first condition : List Bool} {time : ℕ}
    (hsize : first.length + condition.length ≤ time)
    (hpair : ordinaryMachine.timeBoundedKolmogorovComplexity
      (pair first condition) time ≠ ⊤) :
    ordinaryMachine.timeBoundedKolmogorovComplexity
      condition (clock time) ≠ ⊤ :=
  hsoi.condition_ne_top_internal hsize hpair

/-- Increasing the permitted loss preserves a fixed-clock SoI theorem.
@isnad1 id=timeboun.2h7v.s5.9de421367b0c from=translated src=- shape=350d6434 vocab=f19502c4
-/
theorem TimeBoundedSymmetryOfInformation.weaken_loss
    {ordinaryTapes conditionalTapes : ℕ}
    {ordinaryMachine : TM ordinaryTapes}
    {conditionalMachine : OracleTM conditionalTapes}
    {clock firstLoss secondLoss : ℕ → ℕ}
    (hsoi : TimeBoundedSymmetryOfInformation ordinaryMachine
      conditionalMachine clock firstLoss)
    (hloss : ∀ time, firstLoss time ≤ secondLoss time) :
    TimeBoundedSymmetryOfInformation ordinaryMachine conditionalMachine
      clock secondLoss :=
  hsoi.weaken_loss_internal hloss

/-- Giving both left-hand descriptions more time preserves SoI.
@isnad1 id=timeboun.2h7v.s5.fd37adea9bc6 from=translated src=- shape=ffafb62c vocab=f19502c4
-/
theorem TimeBoundedSymmetryOfInformation.weaken_clock
    {ordinaryTapes conditionalTapes : ℕ}
    {ordinaryMachine : TM ordinaryTapes}
    {conditionalMachine : OracleTM conditionalTapes}
    {firstClock secondClock loss : ℕ → ℕ}
    (hsoi : TimeBoundedSymmetryOfInformation ordinaryMachine
      conditionalMachine firstClock loss)
    (hclock : ∀ time, firstClock time ≤ secondClock time) :
    TimeBoundedSymmetryOfInformation ordinaryMachine conditionalMachine
      secondClock loss :=
  hsoi.weaken_clock_internal hclock

/-- The algebraic depth-loss bridge used by conditional meta-complexity
reductions. If a paired description is upper-bounded by an alternative
conditional description plus an earlier-clock description of the condition,
SoI cancels the later-clock condition term. The exact remainder is the
condition's two-clock depth plus the operational and SoI losses.

The paired-description upper bound remains an explicit premise; constructing
it is an evaluator theorem, not an algebraic consequence of SoI.
@isnad1 id=le.4h14v.s7.3cad0921d1ab from=translated src=- shape=c2b6df6a vocab=79d48ea5
-/
theorem TimeBoundedSymmetryOfInformation.conditional_le_of_pair_upper
    {ordinaryTapes conditionalTapes alternativeTapes : ℕ}
    {ordinaryMachine : TM ordinaryTapes}
    {conditionalMachine : OracleTM conditionalTapes}
    {alternativeMachine : OracleTM alternativeTapes}
    {clock loss : ℕ → ℕ}
    (hsoi : TimeBoundedSymmetryOfInformation ordinaryMachine
      conditionalMachine clock loss)
    {first condition : List Bool}
    {time conditionTime alternativeTime upperLoss : ℕ}
    (hsize : first.length + condition.length ≤ time)
    (hclock : conditionTime ≤ clock time)
    (hpairUpper :
      ordinaryMachine.timeBoundedKolmogorovComplexity
          (pair first condition) time ≤
        OracleTM.randomAccessConditionalTimeBoundedKolmogorovComplexity
              alternativeMachine first condition alternativeTime +
            ordinaryMachine.timeBoundedKolmogorovComplexity
              condition conditionTime +
          (upperLoss : WithTop ℕ)) :
    conditionalMachine.randomAccessConditionalTimeBoundedKolmogorovComplexity
        first condition (clock time) ≤
      OracleTM.randomAccessConditionalTimeBoundedKolmogorovComplexity
            alternativeMachine first condition alternativeTime +
          ordinaryMachine.computationalDepthBetween
            condition conditionTime (clock time) +
        (upperLoss : WithTop ℕ) + (loss time : WithTop ℕ) :=
  hsoi.conditional_le_of_pair_upper_internal hsize hclock hpairUpper

/-- Fully composed evaluator-to-depth bridge. A condition-first operational
compiler with additive program length supplies the paired upper bound required
by SoI, yielding the target conditional-complexity inequality without any
additional algebraic premise. All finiteness, clock, and description-budget
requirements remain visible until a concrete universal evaluator discharges
them.
@isnad1 id=le.9h17v.s8.c9efdbaaf1a0 from=translated src=- shape=a4db8c1f vocab=44482349
-/
theorem TimeBoundedSymmetryOfInformation.conditional_le_of_composition
    {ordinaryTapes conditionalTapes alternativeTapes : ℕ}
    {ordinaryMachine : TM ordinaryTapes}
    {conditionalMachine : OracleTM conditionalTapes}
    {alternativeMachine : OracleTM alternativeTapes}
    {compile : List Bool → List Bool → List Bool}
    {clock loss : ℕ → ℕ}
    (hsoi : TimeBoundedSymmetryOfInformation ordinaryMachine
      conditionalMachine clock loss)
    {first condition : List Bool}
    {time conditionTime alternativeTime conditionBound alternativeBound
      constant : ℕ}
    (hsize : first.length + condition.length ≤ time)
    (hclock : conditionTime ≤ clock time)
    (hcompose : TimeBoundedConditionalPairCompositionAt ordinaryMachine
      ordinaryMachine alternativeMachine compile first condition conditionTime
      alternativeTime time conditionBound alternativeBound)
    (hlength : ∀ conditionProgram alternativeProgram,
      conditionProgram.length ≤ conditionBound →
      alternativeProgram.length ≤ alternativeBound →
      (compile conditionProgram alternativeProgram).length ≤
        alternativeProgram.length + conditionProgram.length + constant)
    (hconditionFinite : ordinaryMachine.timeBoundedKolmogorovComplexity
      condition conditionTime ≠ ⊤)
    (halternativeFinite :
      alternativeMachine.randomAccessConditionalTimeBoundedKolmogorovComplexity
        first condition alternativeTime ≠ ⊤)
    (hconditionBound : ordinaryMachine.timeBoundedKolmogorovComplexity
      condition conditionTime ≤ (conditionBound : WithTop ℕ))
    (halternativeBound :
      alternativeMachine.randomAccessConditionalTimeBoundedKolmogorovComplexity
        first condition alternativeTime ≤ (alternativeBound : WithTop ℕ)) :
    conditionalMachine.randomAccessConditionalTimeBoundedKolmogorovComplexity
        first condition (clock time) ≤
      alternativeMachine.randomAccessConditionalTimeBoundedKolmogorovComplexity
            first condition alternativeTime +
          ordinaryMachine.computationalDepthBetween
            condition conditionTime (clock time) +
        (constant : WithTop ℕ) + (loss time : WithTop ℕ) :=
  hsoi.conditional_le_of_composition_internal hsize hclock hcompose hlength
    hconditionFinite halternativeFinite hconditionBound halternativeBound

/-- Any polynomial SoI witness remains valid at an admissible larger clock,
with the logarithmic loss recalculated at that clock. The premise quantifies
over witnesses because the existential clock is intentionally opaque.
@isnad1 id=and.3h5v.s6.c8844ae8e4da from=translated src=- shape=4992ad93 vocab=c2c1e42b
-/
theorem PolynomialTimeBoundedSymmetryOfInformation.enlarge_clock
    {ordinaryTapes conditionalTapes : ℕ}
    {ordinaryMachine : TM ordinaryTapes}
    {conditionalMachine : OracleTM conditionalTapes}
    (hsoi : PolynomialTimeBoundedSymmetryOfInformation ordinaryMachine
      conditionalMachine)
    {largerClock : ℕ → ℕ}
    (hlargerAdmissible : IsAdmissibleKolmogorovClock largerClock)
    (hlarger : ∀ clock additive,
      IsAdmissibleKolmogorovClock clock →
      TimeBoundedSymmetryOfInformation ordinaryMachine conditionalMachine clock
        (fun time => Nat.log 2 (clock time) + additive) →
      ∀ time, clock time ≤ largerClock time) :
    IsAdmissibleKolmogorovClock largerClock ∧
      ∃ additive,
        TimeBoundedSymmetryOfInformation ordinaryMachine conditionalMachine
          largerClock (fun time => Nat.log 2 (largerClock time) + additive) :=
  hsoi.enlarge_clock_internal hlargerAdmissible hlarger

end Complexity
