/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Oracle.Universality.Defs

/-!
# Oracle-uniform universal-machine interfaces -- proof internals
-/

public section

namespace Complexity

namespace OracleTM

variable {firstTapes secondTapes thirdTapes : ℕ}

/--
@isnad1 id=simulate.0h2v.s3.bef0cfc62f25 from=translated src=- shape=5fca6213 vocab=216ba9d2
-/
theorem simulates_refl_internal (machine : OracleTM firstTapes) :
    machine.Simulates machine id where
  halts_iff := by simp
  produces_iff := by simp

/--
@isnad1 id=simulate.2h8v.s5.dd67b371188d from=translated src=- shape=014dd85b vocab=78acd7ac
-/
theorem simulates_comp_internal
    {first : OracleTM firstTapes} {second : OracleTM secondTapes}
    {third : OracleTM thirdTapes}
    {compileFirst compileSecond : List Bool → List Bool}
    (hfirst : first.Simulates second compileFirst)
    (hsecond : second.Simulates third compileSecond) :
    first.Simulates third (compileFirst ∘ compileSecond) where
  halts_iff oracle program := by
    exact (hfirst.halts_iff oracle (compileSecond program)).trans
      (hsecond.halts_iff oracle program)
  produces_iff oracle program output := by
    exact (hfirst.produces_iff oracle (compileSecond program) output).trans
      (hsecond.produces_iff oracle program output)

/--
@isnad1 id=simulate.0h2v.s4.c5913bebf9f2 from=translated src=- shape=ed6f81a7 vocab=51f45a67
-/
theorem simulatesInTime_refl_internal (machine : OracleTM firstTapes) :
    machine.SimulatesInTime machine id (fun _ sourceTime => sourceTime) where
  produces _oracle _program _output _sourceTime hproduce := hproduce

/--
@isnad1 id=simulate.2h10v.s6.8fd4ff1c7953 from=translated src=- shape=045a4427 vocab=909c6fb7
-/
theorem simulatesInTime_comp_internal
    {first : OracleTM firstTapes} {second : OracleTM secondTapes}
    {third : OracleTM thirdTapes}
    {compileFirst compileSecond : List Bool → List Bool}
    {clockFirst clockSecond : TM.TimeOverhead}
    (hfirst : first.SimulatesInTime second compileFirst clockFirst)
    (hsecond : second.SimulatesInTime third compileSecond clockSecond) :
    first.SimulatesInTime third (compileFirst ∘ compileSecond)
      (fun program sourceTime =>
        clockFirst (compileSecond program) (clockSecond program sourceTime)) where
  produces oracle program output sourceTime hproduce :=
    hfirst.produces oracle (compileSecond program) output
      (clockSecond program sourceTime)
      (hsecond.produces oracle program output sourceTime hproduce)

/--
@isnad1 id=isuniver.1h3v.s4.8095a3d665b3 from=translated src=- shape=3c964571 vocab=dd8d7752
-/
theorem efficientlyUniversalFor_isUniversal_internal
    {simulator : OracleTM firstTapes}
    {admissible : TM.TimeOverhead → Prop}
    (h : simulator.IsEfficientlyUniversalFor admissible) :
    simulator.IsUniversal := by
  intro sourceTapes source
  obtain ⟨compile, _constant, _clock, hcompile, hsim, _hlength, _htimed, _hpolicy⟩ :=
    h sourceTapes source
  exact ⟨compile, hcompile, hsim⟩

/--
@isnad1 id=iseffici.1h5v.s5.dce89f5721db from=translated src=- shape=96bf3fe0 vocab=cb02b7d7
-/
theorem efficientlyUniversalFor_mono_internal
    {simulator : OracleTM firstTapes}
    {firstPolicy secondPolicy : TM.TimeOverhead → Prop}
    (hpolicy : ∀ clock, firstPolicy clock → secondPolicy clock)
    (h : simulator.IsEfficientlyUniversalFor firstPolicy) :
    simulator.IsEfficientlyUniversalFor secondPolicy := by
  intro sourceTapes source
  obtain ⟨compile, constant, clock, hcompile, hsim, hlength, htimed, hclock⟩ :=
    h sourceTapes source
  exact ⟨compile, constant, clock, hcompile, hsim, hlength, htimed,
    hpolicy clock hclock⟩

end OracleTM

end Complexity
