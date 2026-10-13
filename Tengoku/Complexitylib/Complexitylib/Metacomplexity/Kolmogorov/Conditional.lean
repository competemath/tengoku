/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.Kolmogorov.Conditional.Defs
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.Kolmogorov.Conditional.Internal

/-!
# Random-access conditional Kolmogorov complexity

The finite condition is exposed through a faithful Boolean oracle. Canonical
tagged queries separately read condition bits and test whether an index is in
bounds, so the oracle retains both contents and length. This is an explicit
random-access convention suitable for conditional meta-complexity; any theorem
whose source fixes a different evaluator convention must provide a simulation
bridge rather than identify the models silently.
-/

public section

namespace Complexity

namespace RandomAccessCondition

/-- A canonical bit query returns the indexed bit, defaulting to false out of
bounds.
@isnad1 id=eq.0h2v.s5.6d6c9f22bfc1 from=translated src=- shape=b76cf4e6 vocab=5ea3e722
-/
@[simp] theorem oracle_bitQuery (condition : List Bool) (index : ℕ) :
    oracle condition (bitQuery index) = (condition[index]?).getD false :=
  oracle_bitQuery_internal condition index

/-- A canonical bounds query says exactly whether the index is valid.
@isnad1 id=eq.0h2v.s4.9a0bef93ca86 from=translated src=- shape=71d4a3b2 vocab=b4e9b42c
-/
@[simp] theorem oracle_inBoundsQuery (condition : List Bool) (index : ℕ) :
    oracle condition (inBoundsQuery index) = decide (index < condition.length) :=
  oracle_inBoundsQuery_internal condition index

/-- The random-access oracle faithfully retains the finite condition, including
its length.
@isnad1 id=injectiv.0h0v.s2.2135545b4285 from=translated src=- shape=836e6cbb vocab=5e02d853
-/
theorem oracle_injective : Function.Injective oracle :=
  oracle_injective_internal

end RandomAccessCondition

namespace OracleTM

variable {n simulatorTapes sourceTapes : ℕ}

/-- Any program producing relative to the condition oracle upper-bounds plain
conditional complexity.
@isnad1 id=le.1h5v.s5.ef0e9bb34943 from=translated src=- shape=e92af1cc vocab=22e39818
-/
theorem randomAccessConditionalPlainKolmogorovComplexity_le
    {machine : OracleTM n} {program output condition : List Bool}
    (hproduce : machine.Produces (RandomAccessCondition.oracle condition)
      program output) :
    machine.randomAccessConditionalPlainKolmogorovComplexity output condition ≤
      program.length :=
  randomAccessConditionalPlainKolmogorovComplexity_le_internal hproduce

/-- Any program producing within the clock upper-bounds bounded conditional
complexity.
@isnad1 id=le.1h6v.s5.4083c582657f from=translated src=- shape=711682a8 vocab=f37d5cc6
-/
theorem randomAccessConditionalTimeBoundedKolmogorovComplexity_le
    {machine : OracleTM n} {program output condition : List Bool} {time : ℕ}
    (hproduce : machine.ProducesInTime (RandomAccessCondition.oracle condition)
      program output time) :
    machine.randomAccessConditionalTimeBoundedKolmogorovComplexity
        output condition time ≤ program.length :=
  randomAccessConditionalTimeBoundedKolmogorovComplexity_le_internal hproduce

/-- Bounded conditional complexity is infinite exactly when no program
produces relative to the condition oracle within the clock.
@isnad1 id=iff.0h5v.s5.b9daa190f760 from=translated src=- shape=c87a56c1 vocab=a0a8dd87
-/
theorem randomAccessConditionalTimeBoundedKolmogorovComplexity_eq_top_iff
    (machine : OracleTM n) (output condition : List Bool) (time : ℕ) :
    machine.randomAccessConditionalTimeBoundedKolmogorovComplexity
          output condition time = ⊤ ↔
      ¬∃ program, machine.ProducesInTime
        (RandomAccessCondition.oracle condition) program output time :=
  randomAccessConditionalTimeBoundedKolmogorovComplexity_eq_top_iff_internal
    machine output condition time

/-- Every finite bounded conditional complexity value is attained.
@isnad1 id=ex.1h5v.s5.34479f72a2ba from=translated src=- shape=bbd66b2f vocab=7b4d5cf0
-/
theorem randomAccessConditionalTimeBoundedKolmogorovComplexity_witness
    (machine : OracleTM n) (output condition : List Bool) (time : ℕ)
    (hfinite : machine.randomAccessConditionalTimeBoundedKolmogorovComplexity
      output condition time ≠ ⊤) :
    ∃ program, (program.length : WithTop ℕ) =
        machine.randomAccessConditionalTimeBoundedKolmogorovComplexity
          output condition time ∧
      machine.ProducesInTime (RandomAccessCondition.oracle condition)
        program output time :=
  randomAccessConditionalTimeBoundedKolmogorovComplexity_witness_internal
    machine output condition time hfinite

/-- Bounded conditional complexity is at most `bound` exactly when a program
of at most that length succeeds within the clock.
@isnad1 id=iff.0h6v.s5.274663310b4a from=translated src=- shape=f0661bef vocab=f37d5cc6
-/
theorem randomAccessConditionalTimeBoundedKolmogorovComplexity_le_coe_iff
    (machine : OracleTM n) (output condition : List Bool) (time bound : ℕ) :
    machine.randomAccessConditionalTimeBoundedKolmogorovComplexity
          output condition time ≤ (bound : WithTop ℕ) ↔
      ∃ program, program.length ≤ bound ∧
        machine.ProducesInTime (RandomAccessCondition.oracle condition)
          program output time :=
  randomAccessConditionalTimeBoundedKolmogorovComplexity_le_coe_iff_internal
    machine output condition time bound

/-- Enlarging the clock cannot increase bounded conditional complexity.
@isnad1 id=le.1h6v.s5.758eb9f9f27b from=translated src=- shape=772fc19f vocab=e2f18b0b
-/
theorem randomAccessConditionalTimeBoundedKolmogorovComplexity_mono
    (machine : OracleTM n) (output condition : List Bool)
    {first second : ℕ} (hclock : first ≤ second) :
    machine.randomAccessConditionalTimeBoundedKolmogorovComplexity
        output condition second ≤
      machine.randomAccessConditionalTimeBoundedKolmogorovComplexity
        output condition first :=
  randomAccessConditionalTimeBoundedKolmogorovComplexity_mono_internal
    machine output condition hclock

/-- An oracle-uniform polynomial simulation transfers conditional descriptions
with one compiler constant and clock shared by every finite condition.
@isnad1 id=ex.3h7v.s7.ed8c505c1c62 from=translated src=- shape=1532fcd0 vocab=40e2f110
-/
theorem SimulatesInTime.randomAccessConditionalKolmogorov_transfer
    {simulator : OracleTM simulatorTapes} {source : OracleTM sourceTapes}
    {compile : List Bool → List Bool} {constant : ℕ}
    {clock : TM.TimeOverhead}
    (hsim : simulator.SimulatesInTime source compile clock)
    (hlength : TM.HasAdditiveProgramOverhead compile constant)
    (hclock : TM.PolynomialTimeOverhead clock) :
    ∃ coefficient exponent,
      ∀ (condition output : List Bool) (sourceTime bound : ℕ),
        source.randomAccessConditionalTimeBoundedKolmogorovComplexity
              output condition sourceTime ≤ (bound : WithTop ℕ) →
          simulator.randomAccessConditionalTimeBoundedKolmogorovComplexity
              output condition
              (coefficient * (bound + sourceTime + 1) ^ exponent) ≤
            (bound + constant : ℕ) :=
  hsim.randomAccessConditionalKolmogorov_transfer_internal hlength hclock

end OracleTM

namespace TM

/-- An embedded ordinary machine ignores every condition, so its bounded
conditional complexity is exactly its ordinary bounded complexity.
@isnad1 id=eq.0h5v.s4.5e44cfb1803c from=translated src=- shape=ec5ef640 vocab=a8ab0cbb
-/
theorem toOracleTM_randomAccessConditionalTimeBoundedKolmogorovComplexity_eq
    (machine : TM n) (output condition : List Bool) (time : ℕ) :
    machine.toOracleTM.randomAccessConditionalTimeBoundedKolmogorovComplexity
        output condition time =
      machine.timeBoundedKolmogorovComplexity output time :=
  toOracleTM_randomAccessConditionalTimeBoundedKolmogorovComplexity_eq_internal
    machine output condition time

end TM

end Complexity
