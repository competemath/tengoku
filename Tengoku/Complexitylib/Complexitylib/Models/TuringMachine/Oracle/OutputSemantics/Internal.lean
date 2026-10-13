/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Oracle.OutputSemantics.Defs
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Oracle
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.OutputSemantics.Defs

/-!
# Pointwise output semantics for deterministic oracle TMs -- proof internals
-/

public section

namespace Complexity

namespace OracleTM

variable {n : ℕ}

/--
@isnad1 id=haltsint.2h6v.s5.794081864103 from=translated src=- shape=953f8b02 vocab=2547a38f
-/
theorem HaltsInTime.mono_internal
    {machine : OracleTM n} {oracle : BooleanOracle} {program : List Bool}
    {first second : ℕ} (hbound : first ≤ second)
    (hhalt : machine.HaltsInTime oracle program first) :
    machine.HaltsInTime oracle program second := by
  obtain ⟨cfg, steps, hsteps, hreach, hhalted⟩ := hhalt
  exact ⟨cfg, steps, hsteps.trans hbound, hreach, hhalted⟩

/--
@isnad1 id=halts.1h5v.s4.8175e7d695bf from=translated src=- shape=f2a57a93 vocab=b2681ba8
-/
theorem halts_of_haltsInTime_internal
    {machine : OracleTM n} {oracle : BooleanOracle} {program : List Bool}
    {time : ℕ} (hhalt : machine.HaltsInTime oracle program time) :
    machine.Halts oracle program :=
  ⟨time, hhalt⟩

/--
@isnad1 id=produces.2h7v.s5.b2194883029d from=translated src=- shape=a15cf462 vocab=7728a2d2
-/
theorem ProducesInTime.mono_internal
    {machine : OracleTM n} {oracle : BooleanOracle}
    {program output : List Bool} {first second : ℕ}
    (hbound : first ≤ second)
    (hproduce : machine.ProducesInTime oracle program output first) :
    machine.ProducesInTime oracle program output second := by
  obtain ⟨cfg, steps, hsteps, hreach, hhalt, houtput⟩ := hproduce
  exact ⟨cfg, steps, hsteps.trans hbound, hreach, hhalt, houtput⟩

/--
@isnad1 id=produces.1h6v.s4.52ba5f3064d1 from=translated src=- shape=75d8b799 vocab=b854ff84
-/
theorem produces_of_producesInTime_internal
    {machine : OracleTM n} {oracle : BooleanOracle}
    {program output : List Bool} {time : ℕ}
    (hproduce : machine.ProducesInTime oracle program output time) :
    machine.Produces oracle program output :=
  ⟨time, hproduce⟩

end OracleTM

namespace TM

/--
@isnad1 id=iff.0h6v.s4.a374f99aa7db from=translated src=- shape=1e6c2a9f vocab=f2052d77
-/
theorem toOracleTM_producesInTime_iff_internal
    (machine : TM n) (oracle : BooleanOracle)
    (program output : List Bool) (time : ℕ) :
    machine.toOracleTM.ProducesInTime oracle program output time ↔
      machine.ProducesInTime program output time := by
  constructor
  · rintro ⟨cfg, steps, hsteps, hreach, hhalt, houtput⟩
    exact ⟨cfg.erase, steps, hsteps,
      machine.erase_toOracleTM_reachesIn oracle hreach,
      hhalt, houtput⟩
  · rintro ⟨cfg, steps, hsteps, hreach, hhalt, houtput⟩
    have hreach' : machine.reachesIn steps
        (machine.toOracleTM.initCfg program).erase cfg := by
      exact hreach
    obtain ⟨oracleCfg, horacleReach, herase⟩ :=
      machine.exists_toOracleTM_reachesIn_of_reachesIn_erase oracle
        (machine.toOracleTM.initCfg program) hreach'
    refine ⟨oracleCfg, steps, hsteps, horacleReach, ?_, ?_⟩
    · change oracleCfg.erase.state = machine.qhalt
      rw [herase]
      exact hhalt
    · change oracleCfg.erase.output.HasOutput output
      rw [herase]
      exact houtput

end TM

end Complexity
