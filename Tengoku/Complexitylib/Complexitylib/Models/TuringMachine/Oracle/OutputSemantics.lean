/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Oracle.OutputSemantics.Defs
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Oracle.OutputSemantics.Internal

/-!
# Pointwise output semantics for deterministic oracle TMs

These relations treat the finite input as a program and the Boolean oracle as
a separate parameter. The ordinary-TM embedding preserves bounded production
exactly, so the oracle semantics is a conservative extension.
-/

public section

namespace Complexity

namespace OracleTM

variable {n : ℕ}

/-- Increasing the clock preserves bounded oracle-machine halting.
@isnad1 id=haltsint.2h6v.s5.794081864103 from=translated src=- shape=953f8b02 vocab=2547a38f
-/
theorem HaltsInTime.mono
    {machine : OracleTM n} {oracle : BooleanOracle} {program : List Bool}
    {first second : ℕ} (hbound : first ≤ second)
    (hhalt : machine.HaltsInTime oracle program first) :
    machine.HaltsInTime oracle program second :=
  hhalt.mono_internal hbound

/-- Forgetting a clock turns bounded oracle-machine halting into eventual
halting.
@isnad1 id=halts.1h5v.s4.8175e7d695bf from=translated src=- shape=f2a57a93 vocab=b2681ba8
-/
theorem halts_of_haltsInTime
    {machine : OracleTM n} {oracle : BooleanOracle} {program : List Bool}
    {time : ℕ} (hhalt : machine.HaltsInTime oracle program time) :
    machine.Halts oracle program :=
  halts_of_haltsInTime_internal hhalt

/-- Increasing the clock preserves bounded oracle-machine production.
@isnad1 id=produces.2h7v.s5.b2194883029d from=translated src=- shape=a15cf462 vocab=7728a2d2
-/
theorem ProducesInTime.mono
    {machine : OracleTM n} {oracle : BooleanOracle}
    {program output : List Bool} {first second : ℕ}
    (hbound : first ≤ second)
    (hproduce : machine.ProducesInTime oracle program output first) :
    machine.ProducesInTime oracle program output second :=
  hproduce.mono_internal hbound

/-- Forgetting a clock turns bounded oracle production into eventual
production.
@isnad1 id=produces.1h6v.s4.52ba5f3064d1 from=translated src=- shape=75d8b799 vocab=b854ff84
-/
theorem produces_of_producesInTime
    {machine : OracleTM n} {oracle : BooleanOracle}
    {program output : List Bool} {time : ℕ}
    (hproduce : machine.ProducesInTime oracle program output time) :
    machine.Produces oracle program output :=
  produces_of_producesInTime_internal hproduce

end OracleTM

namespace TM

/-- The ordinary-machine embedding preserves exact bounded production for
every oracle.
@isnad1 id=iff.0h6v.s4.a374f99aa7db from=translated src=- shape=1e6c2a9f vocab=f2052d77
-/
theorem toOracleTM_producesInTime_iff
    (machine : TM n) (oracle : BooleanOracle)
    (program output : List Bool) (time : ℕ) :
    machine.toOracleTM.ProducesInTime oracle program output time ↔
      machine.ProducesInTime program output time :=
  toOracleTM_producesInTime_iff_internal machine oracle program output time

end TM

end Complexity
