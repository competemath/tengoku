/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.Kolmogorov.Oracle.Defs
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.Kolmogorov.Oracle.Internal

/-!
# Oracle-relative Kolmogorov complexity

This module exposes plain and time-bounded description complexity relative to
an arbitrary deterministic oracle machine and Boolean oracle. The ordinary TM
embedding preserves bounded complexity exactly for every oracle. An
oracle-uniform polynomial simulation transfers bounded descriptions with one
compiler constant and clock shared by all oracles.
-/

public section

namespace Complexity

namespace OracleTM

variable {n : ℕ}

/-- Any oracle program producing the requested output upper-bounds plain
oracle-relative complexity.
@isnad1 id=le.1h5v.s5.550bb8a0f626 from=translated src=- shape=8e049bf4 vocab=acca86f0
-/
theorem plainKolmogorovComplexity_le
    {machine : OracleTM n} {oracle : BooleanOracle}
    {program output : List Bool}
    (hproduce : machine.Produces oracle program output) :
    machine.plainKolmogorovComplexity oracle output ≤ program.length :=
  plainKolmogorovComplexity_le_internal hproduce

/-- Any oracle program producing within a clock upper-bounds time-bounded
oracle-relative complexity.
@isnad1 id=le.1h6v.s5.9d7956fdf32b from=translated src=- shape=70b2f3c2 vocab=caddc801
-/
theorem timeBoundedKolmogorovComplexity_le
    {machine : OracleTM n} {oracle : BooleanOracle}
    {program output : List Bool} {time : ℕ}
    (hproduce : machine.ProducesInTime oracle program output time) :
    machine.timeBoundedKolmogorovComplexity oracle output time ≤
      program.length :=
  timeBoundedKolmogorovComplexity_le_internal hproduce

/-- Bounded oracle complexity is infinite exactly when no program produces the
output within the clock.
@isnad1 id=iff.0h5v.s5.460a7b6ca54f from=translated src=- shape=fc41924e vocab=c2eaff9b
-/
theorem timeBoundedKolmogorovComplexity_eq_top_iff
    (machine : OracleTM n) (oracle : BooleanOracle)
    (output : List Bool) (time : ℕ) :
    machine.timeBoundedKolmogorovComplexity oracle output time = ⊤ ↔
      ¬∃ program, machine.ProducesInTime oracle program output time :=
  timeBoundedKolmogorovComplexity_eq_top_iff_internal
    machine oracle output time

/-- Every finite bounded oracle complexity value is attained by a program.
@isnad1 id=ex.1h5v.s5.48264b443b6e from=translated src=- shape=6fb58d3f vocab=2fafe3c6
-/
theorem timeBoundedKolmogorovComplexity_witness
    (machine : OracleTM n) (oracle : BooleanOracle)
    (output : List Bool) (time : ℕ)
    (hfinite : machine.timeBoundedKolmogorovComplexity oracle output time ≠ ⊤) :
    ∃ program, (program.length : WithTop ℕ) =
        machine.timeBoundedKolmogorovComplexity oracle output time ∧
      machine.ProducesInTime oracle program output time :=
  timeBoundedKolmogorovComplexity_witness_internal
    machine oracle output time hfinite

/-- Bounded oracle complexity is at most `bound` exactly when a program of at
most that length produces the output within the clock.
@isnad1 id=iff.0h6v.s5.4e9368bfeca5 from=translated src=- shape=5106003b vocab=caddc801
-/
theorem timeBoundedKolmogorovComplexity_le_coe_iff
    (machine : OracleTM n) (oracle : BooleanOracle)
    (output : List Bool) (time bound : ℕ) :
    machine.timeBoundedKolmogorovComplexity oracle output time ≤
        (bound : WithTop ℕ) ↔
      ∃ program, program.length ≤ bound ∧
        machine.ProducesInTime oracle program output time :=
  timeBoundedKolmogorovComplexity_le_coe_iff_internal
    machine oracle output time bound

/-- Enlarging the oracle-machine clock cannot increase bounded complexity.
@isnad1 id=le.1h6v.s5.fe2479245da8 from=translated src=- shape=8f216787 vocab=c6628b93
-/
theorem timeBoundedKolmogorovComplexity_mono
    (machine : OracleTM n) (oracle : BooleanOracle)
    (output : List Bool) {first second : ℕ} (hclock : first ≤ second) :
    machine.timeBoundedKolmogorovComplexity oracle output second ≤
      machine.timeBoundedKolmogorovComplexity oracle output first :=
  timeBoundedKolmogorovComplexity_mono_internal
    machine oracle output hclock

/-- An oracle-uniform polynomial simulation transfers every bounded
oracle-relative description using the same compiler constant and polynomial
clock for all Boolean oracles.
@isnad1 id=ex.3h7v.s7.c5fb80e3bf91 from=translated src=- shape=8075144d vocab=314075cb
-/
theorem SimulatesInTime.kolmogorov_transfer
    {simulatorTapes sourceTapes : ℕ}
    {simulator : OracleTM simulatorTapes} {source : OracleTM sourceTapes}
    {compile : List Bool → List Bool} {constant : ℕ}
    {clock : TM.TimeOverhead}
    (hsim : simulator.SimulatesInTime source compile clock)
    (hlength : TM.HasAdditiveProgramOverhead compile constant)
    (hclock : TM.PolynomialTimeOverhead clock) :
    ∃ coefficient exponent,
      ∀ (oracle : BooleanOracle) (output : List Bool)
        (sourceTime bound : ℕ),
        source.timeBoundedKolmogorovComplexity oracle output sourceTime ≤
            (bound : WithTop ℕ) →
          simulator.timeBoundedKolmogorovComplexity oracle output
              (coefficient * (bound + sourceTime + 1) ^ exponent) ≤
            (bound + constant : ℕ) :=
  polynomialTimeOverhead_kolmogorov_transfer_internal
    hsim hlength hclock

end OracleTM

namespace TM

/-- Embedding an ordinary machine into the oracle model preserves its bounded
Kolmogorov complexity exactly, independently of the supplied oracle.
@isnad1 id=eq.0h5v.s4.7ad2213bf6c0 from=translated src=- shape=84e4921b vocab=bcb469ad
-/
theorem toOracleTM_timeBoundedKolmogorovComplexity_eq
    (machine : TM n) (oracle : BooleanOracle)
    (output : List Bool) (time : ℕ) :
    machine.toOracleTM.timeBoundedKolmogorovComplexity oracle output time =
      machine.timeBoundedKolmogorovComplexity output time :=
  toOracleTM_timeBoundedKolmogorovComplexity_eq_internal
    machine oracle output time

end TM

end Complexity
