/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Oracle.Defs

/-!
# Deterministic Boolean-oracle Turing machines -- proof internals
-/

public section

namespace Complexity

namespace Tape

/--
@isnad1 id=eq.0h1v.s4.7f818dc03e6e from=translated src=- shape=802c6af4 vocab=713df92b
-/
theorem length_oracleQuery_internal (tape : Tape) :
    tape.oracleQuery.length = tape.head - 1 := by
  simp [oracleQuery]

end Tape

namespace OracleCfg

/--
@isnad1 id=eq.0h4v.s4.0ba147f731a4 from=translated src=- shape=cea54d22 vocab=a0d9b9e9
-/
theorem erase_init_internal (qstart : Q) (input : List Bool) :
    (OracleCfg.init (n := n) qstart input).erase = Cfg.init qstart input :=
  rfl

end OracleCfg

namespace OracleTM

variable {n : ℕ}

/--
@isnad1 id=iff.0h4v.s5.d5758ef82439 from=translated src=- shape=5311c3cf vocab=017bde04
-/
theorem step_eq_none_iff_halted_internal
    {machine : OracleTM n} {oracle : BooleanOracle}
    {cfg : OracleCfg n machine.Q} :
    machine.step oracle cfg = none ↔ machine.halted cfg := by
  by_cases hhalt : cfg.state = machine.qhalt
  · simp [step, halted, hhalt]
  · cases hquery : machine.queryTransition cfg.state with
    | none => simp [step, halted, hhalt, hquery]
    | some states =>
        obtain ⟨yesState, noState⟩ := states
        simp [step, halted, hhalt, hquery]

/--
@isnad1 id=eq.2h6v.s5.012107fbdade from=translated src=- shape=2135934f vocab=9de1fded
-/
theorem stepRel_functional_internal
    {machine : OracleTM n} {oracle : BooleanOracle}
    {cfg first second : OracleCfg n machine.Q}
    (hfirst : machine.stepRel oracle cfg first)
    (hsecond : machine.stepRel oracle cfg second) : first = second := by
  exact Option.some.inj (hfirst.symm.trans hsecond)

/--
@isnad1 id=eq.2h7v.s5.95b68242f967 from=translated src=- shape=68c8aaec vocab=861c67d9
-/
theorem reachesIn_functional_internal
    {machine : OracleTM n} {oracle : BooleanOracle}
    {time : ℕ} {start first second : OracleCfg n machine.Q}
    (hfirst : machine.reachesIn oracle time start first)
    (hsecond : machine.reachesIn oracle time start second) : first = second := by
  induction hfirst generalizing second with
  | zero =>
      cases hsecond
      rfl
  | step hstep _ ih =>
      cases hsecond with
      | step hstep' hrest' =>
          have hmiddle := Option.some.inj (hstep.symm.trans hstep')
          subst hmiddle
          exact ih hrest'

/--
@isnad1 id=reachesi.2h9v.s6.2ac4e744f201 from=translated src=- shape=077f6888 vocab=95ec1fcc
-/
theorem reachesIn_map_internal
    {machine : OracleTM n} {oracle : BooleanOracle} {workTapes : ℕ}
    {target : TM workTapes}
    (mapCfg : OracleCfg n machine.Q → Cfg workTapes target.Q)
    (hstep : ∀ {cfg next}, machine.step oracle cfg = some next →
      target.step (mapCfg cfg) = some (mapCfg next))
    {time : ℕ} {start result : OracleCfg n machine.Q}
    (hreach : machine.reachesIn oracle time start result) :
    target.reachesIn time (mapCfg start) (mapCfg result) := by
  induction hreach with
  | zero => exact TM.reachesIn.zero
  | step hone _ ih => exact TM.reachesIn.step (hstep hone) ih

/--
@isnad1 id=eq.3h6v.s7.b511ba89a2d5 from=translated src=- shape=5dc74483 vocab=57d85e8b
-/
theorem step_query_true_internal
    {machine : OracleTM n} {oracle : BooleanOracle}
    {cfg : OracleCfg n machine.Q} {yesState noState : machine.Q}
    (hhalt : cfg.state ≠ machine.qhalt)
    (hquery : machine.queryTransition cfg.state = some (yesState, noState))
    (hanswer : oracle cfg.query.oracleQuery = true) :
    machine.step oracle cfg = some { cfg with state := yesState } := by
  simp [step, hhalt, hquery, hanswer]

/--
@isnad1 id=eq.3h6v.s7.4c74968b9d86 from=translated src=- shape=52278313 vocab=47022741
-/
theorem step_query_false_internal
    {machine : OracleTM n} {oracle : BooleanOracle}
    {cfg : OracleCfg n machine.Q} {yesState noState : machine.Q}
    (hhalt : cfg.state ≠ machine.qhalt)
    (hquery : machine.queryTransition cfg.state = some (yesState, noState))
    (hanswer : oracle cfg.query.oracleQuery = false) :
    machine.step oracle cfg = some { cfg with state := noState } := by
  simp [step, hhalt, hquery, hanswer]

/--
@isnad1 id=reachesi.3h6v.s6.698e86eeee77 from=translated src=- shape=67c23513 vocab=c16801dd
-/
theorem reachesIn_one_query_true_internal
    {machine : OracleTM n} {oracle : BooleanOracle}
    {cfg : OracleCfg n machine.Q} {yesState noState : machine.Q}
    (hhalt : cfg.state ≠ machine.qhalt)
    (hquery : machine.queryTransition cfg.state = some (yesState, noState))
    (hanswer : oracle cfg.query.oracleQuery = true) :
    machine.reachesIn oracle 1 cfg { cfg with state := yesState } := by
  exact reachesIn.step
    (step_query_true_internal hhalt hquery hanswer) reachesIn.zero

/--
@isnad1 id=reachesi.3h6v.s6.d1553c827e1e from=translated src=- shape=d4e33ca6 vocab=71625355
-/
theorem reachesIn_one_query_false_internal
    {machine : OracleTM n} {oracle : BooleanOracle}
    {cfg : OracleCfg n machine.Q} {yesState noState : machine.Q}
    (hhalt : cfg.state ≠ machine.qhalt)
    (hquery : machine.queryTransition cfg.state = some (yesState, noState))
    (hanswer : oracle cfg.query.oracleQuery = false) :
    machine.reachesIn oracle 1 cfg { cfg with state := noState } := by
  exact reachesIn.step
    (step_query_false_internal hhalt hquery hanswer) reachesIn.zero

end OracleTM

namespace TM

/--
@isnad1 id=eq.0h3v.s5.e2a542e3bfee from=translated src=- shape=f467465f vocab=ccf9e9b6
-/
theorem toOracleTM_queryTransition_internal (machine : TM n) (state : machine.Q) :
    machine.toOracleTM.queryTransition state = none :=
  rfl

/--
@isnad1 id=eq.0h5v.s5.3cef8f80c696 from=translated src=- shape=948e6692 vocab=9535c6cd
-/
theorem toOracleTM_step_oracle_independent_internal
    (machine : TM n) (first second : BooleanOracle)
    (cfg : OracleCfg n machine.Q) :
    machine.toOracleTM.step first cfg = machine.toOracleTM.step second cfg := by
  simp [OracleTM.step, TM.toOracleTM]

/--
@isnad1 id=eq.0h4v.s5.88801fb4c3a8 from=translated src=- shape=8cc5f020 vocab=4b6e8918
-/
theorem erase_toOracleTM_step_internal
    (machine : TM n) (oracle : BooleanOracle)
    (cfg : OracleCfg n machine.Q) :
    Option.map OracleCfg.erase (machine.toOracleTM.step oracle cfg) =
      machine.step cfg.erase := by
  by_cases hhalt : cfg.state = machine.qhalt
  · simp [OracleTM.step, TM.step, TM.toOracleTM, OracleCfg.erase, hhalt]
  · simp [OracleTM.step, TM.step, TM.toOracleTM, OracleCfg.erase, hhalt]

/--
@isnad1 id=eq.1h5v.s6.ef3d815c3457 from=translated src=- shape=d490647b vocab=41e82151
-/
theorem erase_toOracleTM_step_some_internal
    (machine : TM n) (oracle : BooleanOracle)
    {cfg next : OracleCfg n machine.Q}
    (hstep : machine.toOracleTM.step oracle cfg = some next) :
    machine.step cfg.erase = some next.erase := by
  have herase := erase_toOracleTM_step_internal machine oracle cfg
  rw [hstep] at herase
  exact herase.symm

/--
@isnad1 id=reachesi.1h6v.s5.72c9fb7a1e23 from=translated src=- shape=6ec82b75 vocab=a03b15b2
-/
theorem erase_toOracleTM_reachesIn_internal
    (machine : TM n) (oracle : BooleanOracle)
    {time : ℕ} {start result : OracleCfg n machine.Q}
    (hreach : machine.toOracleTM.reachesIn oracle time start result) :
    machine.reachesIn time start.erase result.erase := by
  exact OracleTM.reachesIn_map_internal OracleCfg.erase
    (erase_toOracleTM_step_some_internal machine oracle) hreach

/--
@isnad1 id=ex.1h5v.s6.c54ea03d9924 from=translated src=- shape=0a0b3a4e vocab=41e82151
-/
theorem exists_toOracleTM_step_of_step_erase_internal
    (machine : TM n) (oracle : BooleanOracle)
    {cfg : OracleCfg n machine.Q} {next : Cfg n machine.Q}
    (hstep : machine.step cfg.erase = some next) :
    ∃ oracleNext, machine.toOracleTM.step oracle cfg = some oracleNext ∧
      oracleNext.erase = next := by
  have herase := erase_toOracleTM_step_internal machine oracle cfg
  rw [hstep] at herase
  cases horacle : machine.toOracleTM.step oracle cfg with
  | none => simp [horacle] at herase
  | some oracleNext =>
      refine ⟨oracleNext, rfl, ?_⟩
      have heq : some oracleNext.erase = some next := by
        simpa [horacle] using herase
      exact Option.some.inj heq

/--
@isnad1 id=ex.1h6v.s6.3076ce2766e9 from=translated src=- shape=5ff49aa3 vocab=2ebb9e24
-/
theorem exists_toOracleTM_reachesIn_of_reachesIn_erase_internal
    (machine : TM n) (oracle : BooleanOracle)
    {time : ℕ} (start : OracleCfg n machine.Q) {result : Cfg n machine.Q}
    (hreach : machine.reachesIn time start.erase result) :
    ∃ oracleResult,
      machine.toOracleTM.reachesIn oracle time start oracleResult ∧
        oracleResult.erase = result := by
  induction time generalizing start result with
  | zero =>
      cases hreach
      exact ⟨start, OracleTM.reachesIn.zero, rfl⟩
  | succ time ih =>
      obtain ⟨middle, hstep, hrest⟩ :=
        (TM.reachesIn_succ_iff.mp hreach)
      obtain ⟨oracleMiddle, horacleStep, heraseMiddle⟩ :=
        exists_toOracleTM_step_of_step_erase_internal machine oracle hstep
      have hrest' : machine.reachesIn time oracleMiddle.erase result := by
        rw [heraseMiddle]
        exact hrest
      obtain ⟨oracleResult, horacleRest, heraseResult⟩ :=
        ih oracleMiddle hrest'
      exact ⟨oracleResult,
        OracleTM.reachesIn.step horacleStep horacleRest, heraseResult⟩

/--
@isnad1 id=iff.0h5v.s4.a525aee7fb50 from=translated src=- shape=11cf5ca5 vocab=3b4a6724
-/
theorem toOracleTM_decidesInTime_iff_internal
    (machine : TM n) (oracle : BooleanOracle)
    (language : Language) (timeBound : ℕ → ℕ) :
    machine.toOracleTM.DecidesInTime oracle language timeBound ↔
      machine.DecidesInTime language timeBound := by
  constructor
  · intro hdecides input
    obtain ⟨cfg, time, htime, hreach, hhalt, hyes, hno⟩ := hdecides input
    exact ⟨cfg.erase, time, htime,
      erase_toOracleTM_reachesIn_internal machine oracle hreach,
      hhalt, hyes, hno⟩
  · intro hdecides input
    obtain ⟨cfg, time, htime, hreach, hhalt, hyes, hno⟩ := hdecides input
    have hreach' : machine.reachesIn time
        (machine.toOracleTM.initCfg input).erase cfg := by
      exact hreach
    obtain ⟨oracleCfg, horacleReach, herase⟩ :=
      exists_toOracleTM_reachesIn_of_reachesIn_erase_internal
        machine oracle (machine.toOracleTM.initCfg input) hreach'
    refine ⟨oracleCfg, time, htime, horacleReach, ?_, ?_, ?_⟩
    · change oracleCfg.erase.state = machine.qhalt
      rw [herase]
      exact hhalt
    · intro hinput
      change oracleCfg.erase.output.cells 1 = Γ.one
      rw [herase]
      exact hyes hinput
    · intro hinput
      change oracleCfg.erase.output.cells 1 = Γ.zero
      rw [herase]
      exact hno hinput

end TM

end Complexity
