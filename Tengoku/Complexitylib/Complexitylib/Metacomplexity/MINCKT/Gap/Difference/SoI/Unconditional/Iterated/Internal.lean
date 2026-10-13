/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.MINCKT.Gap.Difference.SoI.Unconditional.Iterated.Defs
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.MINCKT.Gap.Difference.SoI.Unconditional.Internal
import Tengoku.Complexitylib.Complexitylib.Metacomplexity.Kolmogorov.Internal
import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.OutputBounds

/-!
# The iterated-clock schedule -- proof internals
-/

public section

namespace Complexity

namespace GapMINCKT

namespace DifferenceEstimator

namespace Unconditional

namespace Iterated

/--
@isnad1 id=eq.0h2v.s4.22a2426872d0 from=translated src=- shape=3aee0d2d vocab=8163b109
-/
theorem clockIterate_zero_internal (clock : ℕ → ℕ) (time : ℕ) :
    clockIterate clock 0 time = time := rfl

/--
@isnad1 id=eq.0h3v.s5.40600ad130ac from=translated src=- shape=daa32759 vocab=398774c2
-/
theorem clockIterate_succ_internal (clock : ℕ → ℕ)
    (iterations time : ℕ) :
    clockIterate clock (iterations + 1) time =
      clock (clockIterate clock iterations time) := rfl

/--
@isnad1 id=monotone.1h2v.s4.4a948bdc130b from=translated src=- shape=e9042b07 vocab=eecc9b95
-/
theorem clockIterate_monotone_internal {clock : ℕ → ℕ}
    (hclock : Monotone clock) (iterations : ℕ) :
    Monotone (clockIterate clock iterations) := by
  induction iterations with
  | zero => exact fun _ _ h => h
  | succ iterations ih =>
      intro first second hle
      exact hclock (ih hle)

/--
@isnad1 id=le.1h3v.s4.542c800c68b6 from=translated src=- shape=d21aa90f vocab=1d2a61d4
-/
theorem clockIterate_dominates_internal {clock : ℕ → ℕ}
    (hclock : ∀ time, time ≤ clock time) (iterations time : ℕ) :
    time ≤ clockIterate clock iterations time := by
  induction iterations with
  | zero => exact le_rfl
  | succ iterations ih => exact ih.trans (hclock _)

/--
@isnad1 id=le.0h1v.s4.90d1b4564896 from=translated src=- shape=2e4fd076 vocab=c3d8cd5e
-/
theorem paddedTime_size_le_internal (inst : MINCKT.Instance) :
    inst.output.length + inst.condition.length ≤ paddedTime inst :=
  le_max_left _ _

/--
@isnad1 id=le.0h1v.s3.5bfef62df5e1 from=translated src=- shape=b70c6bb1 vocab=620528ac
-/
theorem paddedTime_time_le_internal (inst : MINCKT.Instance) :
    inst.time ≤ paddedTime inst :=
  le_max_right _ _

/--
@isnad1 id=le.0h1v.s4.82bd3411f535 from=translated src=- shape=5e1e7a22 vocab=eb23fcce
-/
theorem paddedTime_le_total_internal (inst : MINCKT.Instance) :
    paddedTime inst ≤ inst.time + inst.output.length + inst.condition.length := by
  apply max_le
  · omega
  · omega

/--
@isnad1 id=eq.0h2v.s4.fe458a7a5a91 from=translated src=- shape=50dc2d95 vocab=d2e9b3ff
-/
theorem ordinaryParameters_transformedTime_internal (clock : ℕ → ℕ)
    (inst : MINKT.Instance) :
    (ordinaryParameters clock).transformedTime inst = clock inst.time := rfl

/--
@isnad1 id=eq.0h2v.s5.4e8c0fd13b6d from=translated src=- shape=b6fd75f5 vocab=b1356f0e
-/
theorem conditionalParameters_transformedTime_internal (clock : ℕ → ℕ)
    (inst : MINCKT.Instance) :
    (conditionalParameters clock).transformedTime inst =
      clockIterate clock 4
        (inst.time + inst.output.length + inst.condition.length) := rfl

/--
@isnad1 id=eq.0h4v.s4.84941cd55f78 from=translated src=- shape=dcabb485 vocab=b1bf3018
-/
theorem plan_pairInputTime_internal (clock : ℕ → ℕ)
    (pairUpperLoss correction : MINCKT.Instance → ℕ)
    (inst : MINCKT.Instance) :
    (plan clock pairUpperLoss correction).pairInputTime inst =
      clockIterate clock 1 (paddedTime inst) := rfl

/--
@isnad1 id=eq.0h4v.s4.b4e6a35956ec from=translated src=- shape=dcabb485 vocab=5039854f
-/
theorem plan_conditionInputTime_internal (clock : ℕ → ℕ)
    (pairUpperLoss correction : MINCKT.Instance → ℕ)
    (inst : MINCKT.Instance) :
    (plan clock pairUpperLoss correction).conditionInputTime inst =
      clockIterate clock 3 (paddedTime inst) := rfl

/--
@isnad1 id=eq.0h4v.s4.5f0fdec661ab from=translated src=- shape=dcabb485 vocab=7e4ecd50
-/
theorem plan_soiTime_internal (clock : ℕ → ℕ)
    (pairUpperLoss correction : MINCKT.Instance → ℕ)
    (inst : MINCKT.Instance) :
    (plan clock pairUpperLoss correction).soiTime inst =
      clockIterate clock 2 (paddedTime inst) := rfl

/--
@isnad1 id=eq.0h4v.s4.a1569cefb9c5 from=translated src=- shape=6b07a718 vocab=2ce6948f
-/
theorem plan_pairUpperLoss_internal (clock : ℕ → ℕ)
    (pairUpperLoss correction : MINCKT.Instance → ℕ)
    (inst : MINCKT.Instance) :
    (plan clock pairUpperLoss correction).pairUpperLoss inst =
      pairUpperLoss inst := rfl

/--
@isnad1 id=eq.0h4v.s4.d6674efd4a26 from=translated src=- shape=65eb3338 vocab=ab921520
-/
theorem plan_correction_internal (clock : ℕ → ℕ)
    (pairUpperLoss correction : MINCKT.Instance → ℕ)
    (inst : MINCKT.Instance) :
    (plan clock pairUpperLoss correction).correction inst = correction inst := rfl

/--
@isnad1 id=iswideni.1h1v.s3.abb9f0b5673e from=translated src=- shape=aef97f5f vocab=caffc954
-/
theorem IsRegularClock.ordinaryParameters_widening_internal
    {clock : ℕ → ℕ} (hclock : IsRegularClock clock) :
    (ordinaryParameters clock).IsWidening := by
  intro _outputLength time
  exact hclock.dominates time

/--
@isnad1 id=iswideni.1h1v.s3.f0fce8583f75 from=translated src=- shape=aef97f5f vocab=a1d51046
-/
theorem IsRegularClock.conditionalParameters_widening_internal
    {clock : ℕ → ℕ} (hclock : IsRegularClock clock) :
    (conditionalParameters clock).IsWidening := by
  intro outputLength conditionLength time
  exact (by omega : time ≤ time + outputLength + conditionLength) |>.trans
    (clockIterate_dominates_internal hclock.dominates 4 _)

/--
@isnad1 id=isadmiss.0h0v.s1.446281f752c6 from=translated src=- shape=87ceb31f vocab=6e400cd9
-/
theorem isAdmissibleClock_id_internal : IsAdmissibleClock id where
  monotone := monotone_id
  dominates := fun _ => le_rfl
  polynomiallyBounded := ⟨1, 1, fun time => by simp⟩

/--
@isnad1 id=not.0h4v.s4.75c761305290 from=translated src=- shape=0da608ac vocab=afb3bf28
-/
theorem not_satisfiesBounds_ordinaryParameters_internal {tapes : ℕ}
    (machine : TM tapes) (clock : ℕ → ℕ)
    (estimate : GapMINKT.Logarithmic.Estimator) :
    ¬ estimate.SatisfiesBounds machine (ordinaryParameters clock) := by
  intro h
  have hlower := (h ⟨List.replicate (clock 0 + 1) true, 0⟩).2
  have htop : machine.timeBoundedKolmogorovComplexity
      (List.replicate (clock 0 + 1) true) (clock 0) = ⊤ := by
    rw [TM.timeBoundedKolmogorovComplexity_eq_top_iff_internal]
    rintro ⟨program, c, steps, hsteps, hrun, -, hout⟩
    have hfar := TM.reachesIn_output_cells_far hrun (clock 0 + 1)
      (by show 0 + steps < clock 0 + 1; omega)
    have hbit := hout.1 (clock 0) (by simp)
    rw [hfar] at hbit
    simp [Γ.ofBool] at hbit
  change machine.timeBoundedKolmogorovComplexity
      (List.replicate (clock 0 + 1) true) (clock 0) ≤ _ at hlower
  rw [htop] at hlower
  exact WithTop.not_top_le_coe _ hlower

/--
@isnad1 id=compatib.3h8v.s6.19d218e8ac9e from=translated src=- shape=479e6d8d vocab=6d1cf0af
-/
theorem IsRegularClock.compatible_internal
    {ordinaryTapes conditionalTapes : ℕ}
    {clock soiLoss : ℕ → ℕ}
    {pairUpperLoss correction : MINCKT.Instance → ℕ}
    {ordinaryMachine : TM ordinaryTapes}
    {conditionalMachine : OracleTM conditionalTapes}
    (hclock : IsRegularClock clock)
    (hloss : LossBudget clock pairUpperLoss correction soiLoss)
    (hpair : ∀ inst,
      ordinaryMachine.timeBoundedKolmogorovComplexity
            (pair inst.output inst.condition)
              ((plan clock pairUpperLoss correction).pairInputTime inst) ≤
        inst.complexity conditionalMachine +
            ordinaryMachine.timeBoundedKolmogorovComplexity
              inst.condition inst.time +
          ((plan clock pairUpperLoss correction).pairUpperLoss inst : WithTop ℕ)) :
    Compatible (plan clock pairUpperLoss correction) ordinaryMachine
      conditionalMachine (ordinaryParameters clock) (conditionalParameters clock)
        clock soiLoss := by
  constructor
  · intro inst
    have hstep : clockIterate clock 3 (paddedTime inst) ≤
        clockIterate clock 4 (paddedTime inst) := by
      exact hclock.dominates _
    have hpad := clockIterate_monotone_internal hclock.monotone 4
      (paddedTime_le_total_internal inst)
    exact hstep.trans hpad
  · intro inst
    exact (paddedTime_size_le_internal inst).trans
      (clockIterate_dominates_internal hclock.dominates 2 _)
  · intro inst
    rfl
  · intro inst
    exact clockIterate_monotone_internal hclock.monotone 4
      (paddedTime_le_total_internal inst)
  · intro inst
    rfl
  · exact hpair
  · intro inst
    simp [Plan.conditionInput, GapMINKT.Logarithmic.Parameters.logarithmicSlack,
      GapMINKT.Logarithmic.Parameters.transformedTime, ordinaryParameters, plan]
    exact hloss.upper inst
  · intro inst
    simp [Plan.pairInput, GapMINKT.Logarithmic.Parameters.logarithmicSlack,
      GapMINKT.Logarithmic.Parameters.transformedTime, GapMINCKT.Parameters.logarithmicSlack,
      GapMINCKT.Parameters.transformedTime, ordinaryParameters, conditionalParameters, plan]
    exact hloss.lower inst

/--
@isnad1 id=compatib.3h9v.s5.3862e96e1671 from=translated src=- shape=0ae54f2c vocab=a72c3397
-/
theorem IsRegularClock.compatible_of_pairComposition_internal
    {ordinaryTapes conditionalTapes : ℕ}
    {clock soiLoss : ℕ → ℕ}
    {pairUpperLoss correction : MINCKT.Instance → ℕ}
    {composition : PairCompositionPlan}
    {ordinaryMachine : TM ordinaryTapes}
    {conditionalMachine : OracleTM conditionalTapes}
    (hclock : IsRegularClock clock)
    (hloss : LossBudget clock pairUpperLoss correction soiLoss)
    (hsupports : SupportsPairUpper (plan clock pairUpperLoss correction)
      composition ordinaryMachine conditionalMachine) :
    Compatible (plan clock pairUpperLoss correction) ordinaryMachine
      conditionalMachine (ordinaryParameters clock) (conditionalParameters clock)
        clock soiLoss :=
  hclock.compatible_internal hloss hsupports.pair_upper_internal

end Iterated

end Unconditional

end DifferenceEstimator

end GapMINCKT

end Complexity
