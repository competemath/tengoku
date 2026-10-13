/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Oracle.Defs
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Oracle.Internal

/-!
# Deterministic Boolean-oracle Turing machines

The oracle model has a dedicated query tape and charges one step per lookup.
Writing the query remains part of ordinary machine execution. Exact-time runs
are deterministic, and the ordinary-TM embedding has no query states, is
independent of the supplied oracle, and erases step-for-step to the source TM.

This first layer is deterministic. Nondeterministic oracle execution and
relativized complexity classes are deliberately left to subsequent modules.
-/

public section

namespace Complexity

namespace Tape

/-- A query contains exactly the cells strictly between the left marker and
the query-tape head.
@isnad1 id=eq.0h1v.s4.7f818dc03e6e from=translated src=- shape=802c6af4 vocab=713df92b
-/
@[simp] theorem length_oracleQuery (tape : Tape) :
    tape.oracleQuery.length = tape.head - 1 :=
  length_oracleQuery_internal tape

end Tape

namespace OracleCfg

/-- Erasing the query tape from an initial oracle configuration gives the
ordinary initial configuration.
@isnad1 id=eq.0h4v.s4.0ba147f731a4 from=translated src=- shape=cea54d22 vocab=a0d9b9e9
-/
@[simp] theorem erase_init (qstart : Q) (input : List Bool) :
    (OracleCfg.init (n := n) qstart input).erase = Cfg.init qstart input :=
  erase_init_internal qstart input

end OracleCfg

namespace OracleTM

variable {n : ℕ}

/-- An oracle step is absent exactly at the halt state.
@isnad1 id=iff.0h4v.s5.d5758ef82439 from=translated src=- shape=5311c3cf vocab=017bde04
-/
theorem step_eq_none_iff_halted
    {machine : OracleTM n} {oracle : BooleanOracle}
    {cfg : OracleCfg n machine.Q} :
    machine.step oracle cfg = none ↔ machine.halted cfg :=
  step_eq_none_iff_halted_internal

/-- Deterministic one-step oracle execution has at most one successor.
@isnad1 id=eq.2h6v.s5.012107fbdade from=translated src=- shape=2135934f vocab=9de1fded
-/
theorem stepRel_functional
    {machine : OracleTM n} {oracle : BooleanOracle}
    {cfg first second : OracleCfg n machine.Q}
    (hfirst : machine.stepRel oracle cfg first)
    (hsecond : machine.stepRel oracle cfg second) : first = second :=
  stepRel_functional_internal hfirst hsecond

/-- An exact-time deterministic oracle run has a unique final configuration.
@isnad1 id=eq.2h7v.s5.95b68242f967 from=translated src=- shape=68c8aaec vocab=861c67d9
-/
theorem reachesIn_functional
    {machine : OracleTM n} {oracle : BooleanOracle}
    {time : ℕ} {start first second : OracleCfg n machine.Q}
    (hfirst : machine.reachesIn oracle time start first)
    (hsecond : machine.reachesIn oracle time start second) : first = second :=
  reachesIn_functional_internal hfirst hsecond

/-- A step-preserving configuration map sends an exact-time oracle run to an
exact-time run of an ordinary target machine.
@isnad1 id=reachesi.2h9v.s6.2ac4e744f201 from=translated src=- shape=077f6888 vocab=95ec1fcc
-/
theorem reachesIn_map
    {machine : OracleTM n} {oracle : BooleanOracle} {workTapes : ℕ}
    {target : TM workTapes}
    (mapCfg : OracleCfg n machine.Q → Cfg workTapes target.Q)
    (hstep : ∀ {cfg next}, machine.step oracle cfg = some next →
      target.step (mapCfg cfg) = some (mapCfg next))
    {time : ℕ} {start result : OracleCfg n machine.Q}
    (hreach : machine.reachesIn oracle time start result) :
    target.reachesIn time (mapCfg start) (mapCfg result) :=
  reachesIn_map_internal mapCfg hstep hreach

/-- A true oracle answer enters the declared true-successor state and leaves
all tapes unchanged.
@isnad1 id=eq.3h6v.s7.b511ba89a2d5 from=translated src=- shape=5dc74483 vocab=57d85e8b
-/
theorem step_query_true
    {machine : OracleTM n} {oracle : BooleanOracle}
    {cfg : OracleCfg n machine.Q} {yesState noState : machine.Q}
    (hhalt : cfg.state ≠ machine.qhalt)
    (hquery : machine.queryTransition cfg.state = some (yesState, noState))
    (hanswer : oracle cfg.query.oracleQuery = true) :
    machine.step oracle cfg = some { cfg with state := yesState } :=
  step_query_true_internal hhalt hquery hanswer

/-- A false oracle answer enters the declared false-successor state and leaves
all tapes unchanged.
@isnad1 id=eq.3h6v.s7.4c74968b9d86 from=translated src=- shape=52278313 vocab=47022741
-/
theorem step_query_false
    {machine : OracleTM n} {oracle : BooleanOracle}
    {cfg : OracleCfg n machine.Q} {yesState noState : machine.Q}
    (hhalt : cfg.state ≠ machine.qhalt)
    (hquery : machine.queryTransition cfg.state = some (yesState, noState))
    (hanswer : oracle cfg.query.oracleQuery = false) :
    machine.step oracle cfg = some { cfg with state := noState } :=
  step_query_false_internal hhalt hquery hanswer

/-- A true oracle lookup is one exact execution step.
@isnad1 id=reachesi.3h6v.s6.698e86eeee77 from=translated src=- shape=67c23513 vocab=c16801dd
-/
theorem reachesIn_one_query_true
    {machine : OracleTM n} {oracle : BooleanOracle}
    {cfg : OracleCfg n machine.Q} {yesState noState : machine.Q}
    (hhalt : cfg.state ≠ machine.qhalt)
    (hquery : machine.queryTransition cfg.state = some (yesState, noState))
    (hanswer : oracle cfg.query.oracleQuery = true) :
    machine.reachesIn oracle 1 cfg { cfg with state := yesState } :=
  reachesIn_one_query_true_internal hhalt hquery hanswer

/-- A false oracle lookup is one exact execution step.
@isnad1 id=reachesi.3h6v.s6.d1553c827e1e from=translated src=- shape=d4e33ca6 vocab=71625355
-/
theorem reachesIn_one_query_false
    {machine : OracleTM n} {oracle : BooleanOracle}
    {cfg : OracleCfg n machine.Q} {yesState noState : machine.Q}
    (hhalt : cfg.state ≠ machine.qhalt)
    (hquery : machine.queryTransition cfg.state = some (yesState, noState))
    (hanswer : oracle cfg.query.oracleQuery = false) :
    machine.reachesIn oracle 1 cfg { cfg with state := noState } :=
  reachesIn_one_query_false_internal hhalt hquery hanswer

end OracleTM

namespace TM

/-- The ordinary-machine embedding has no query states.
@isnad1 id=eq.0h3v.s5.e2a542e3bfee from=translated src=- shape=f467465f vocab=ccf9e9b6
-/
@[simp] theorem toOracleTM_queryTransition (machine : TM n) (state : machine.Q) :
    machine.toOracleTM.queryTransition state = none :=
  toOracleTM_queryTransition_internal machine state

/-- Every step of an embedded ordinary machine is independent of the oracle.
@isnad1 id=eq.0h5v.s5.3cef8f80c696 from=translated src=- shape=948e6692 vocab=9535c6cd
-/
theorem toOracleTM_step_oracle_independent
    (machine : TM n) (first second : BooleanOracle)
    (cfg : OracleCfg n machine.Q) :
    machine.toOracleTM.step first cfg = machine.toOracleTM.step second cfg :=
  toOracleTM_step_oracle_independent_internal machine first second cfg

/-- Erasing the query tape after one embedded-machine step agrees exactly with
one step of the source ordinary TM.
@isnad1 id=eq.0h4v.s5.88801fb4c3a8 from=translated src=- shape=8cc5f020 vocab=4b6e8918
-/
theorem erase_toOracleTM_step
    (machine : TM n) (oracle : BooleanOracle)
    (cfg : OracleCfg n machine.Q) :
    Option.map OracleCfg.erase (machine.toOracleTM.step oracle cfg) =
      machine.step cfg.erase :=
  erase_toOracleTM_step_internal machine oracle cfg

/-- Erasing the query tape sends every exact-time embedded-machine run to the
source ordinary-machine run with the same number of steps.
@isnad1 id=reachesi.1h6v.s5.72c9fb7a1e23 from=translated src=- shape=6ec82b75 vocab=a03b15b2
-/
theorem erase_toOracleTM_reachesIn
    (machine : TM n) (oracle : BooleanOracle)
    {time : ℕ} {start result : OracleCfg n machine.Q}
    (hreach : machine.toOracleTM.reachesIn oracle time start result) :
    machine.reachesIn time start.erase result.erase :=
  erase_toOracleTM_reachesIn_internal machine oracle hreach

/-- Every source-machine step lifts to an embedded oracle-machine step from
any configuration with the required erased ordinary state.
@isnad1 id=ex.1h5v.s6.c54ea03d9924 from=translated src=- shape=0a0b3a4e vocab=41e82151
-/
theorem exists_toOracleTM_step_of_step_erase
    (machine : TM n) (oracle : BooleanOracle)
    {cfg : OracleCfg n machine.Q} {next : Cfg n machine.Q}
    (hstep : machine.step cfg.erase = some next) :
    ∃ oracleNext, machine.toOracleTM.step oracle cfg = some oracleNext ∧
      oracleNext.erase = next :=
  exists_toOracleTM_step_of_step_erase_internal machine oracle hstep

/-- Every exact-time source run lifts to an exact-time embedded oracle run;
the final configuration erases to the source result.
@isnad1 id=ex.1h6v.s6.3076ce2766e9 from=translated src=- shape=5ff49aa3 vocab=2ebb9e24
-/
theorem exists_toOracleTM_reachesIn_of_reachesIn_erase
    (machine : TM n) (oracle : BooleanOracle)
    {time : ℕ} (start : OracleCfg n machine.Q) {result : Cfg n machine.Q}
    (hreach : machine.reachesIn time start.erase result) :
    ∃ oracleResult,
      machine.toOracleTM.reachesIn oracle time start oracleResult ∧
        oracleResult.erase = result :=
  exists_toOracleTM_reachesIn_of_reachesIn_erase_internal
    machine oracle start hreach

/-- The ordinary-machine embedding decides exactly the same timed languages,
for every supplied oracle.
@isnad1 id=iff.0h5v.s4.a525aee7fb50 from=translated src=- shape=11cf5ca5 vocab=3b4a6724
-/
theorem toOracleTM_decidesInTime_iff
    (machine : TM n) (oracle : BooleanOracle)
    (language : Language) (timeBound : ℕ → ℕ) :
    machine.toOracleTM.DecidesInTime oracle language timeBound ↔
      machine.DecidesInTime language timeBound :=
  toOracleTM_decidesInTime_iff_internal machine oracle language timeBound

end TM

end Complexity
