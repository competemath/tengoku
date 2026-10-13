/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Oracle.Universality.Defs
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Oracle.Universality.Internal

/-!
# Oracle-uniform universal-machine interfaces

The same finite compiler and simulation clock must work for every Boolean
oracle. Semantic and timed simulations compose, and efficient oracle
universality implies semantic oracle universality.
-/

public section

namespace Complexity

namespace OracleTM

variable {firstTapes secondTapes thirdTapes : ℕ}

/-- Every oracle machine simulates itself under the identity compiler.
@isnad1 id=simulate.0h2v.s3.bef0cfc62f25 from=translated src=- shape=5fca6213 vocab=216ba9d2
-/
theorem Simulates.refl (machine : OracleTM firstTapes) :
    machine.Simulates machine id :=
  simulates_refl_internal machine

/-- Oracle-uniform semantic simulations compose.
@isnad1 id=simulate.2h8v.s5.dd67b371188d from=translated src=- shape=014dd85b vocab=78acd7ac
-/
theorem Simulates.comp
    {first : OracleTM firstTapes} {second : OracleTM secondTapes}
    {third : OracleTM thirdTapes}
    {compileFirst compileSecond : List Bool → List Bool}
    (hfirst : first.Simulates second compileFirst)
    (hsecond : second.Simulates third compileSecond) :
    first.Simulates third (compileFirst ∘ compileSecond) :=
  simulates_comp_internal hfirst hsecond

/-- Identity execution has identity oracle-simulation overhead.
@isnad1 id=simulate.0h2v.s4.c5913bebf9f2 from=translated src=- shape=ed6f81a7 vocab=51f45a67
-/
theorem SimulatesInTime.refl (machine : OracleTM firstTapes) :
    machine.SimulatesInTime machine id (fun _ sourceTime => sourceTime) :=
  simulatesInTime_refl_internal machine

/-- Timed oracle-uniform simulations compose by nesting their clocks.
@isnad1 id=simulate.2h10v.s6.8fd4ff1c7953 from=translated src=- shape=045a4427 vocab=909c6fb7
-/
theorem SimulatesInTime.comp
    {first : OracleTM firstTapes} {second : OracleTM secondTapes}
    {third : OracleTM thirdTapes}
    {compileFirst compileSecond : List Bool → List Bool}
    {clockFirst clockSecond : TM.TimeOverhead}
    (hfirst : first.SimulatesInTime second compileFirst clockFirst)
    (hsecond : second.SimulatesInTime third compileSecond clockSecond) :
    first.SimulatesInTime third (compileFirst ∘ compileSecond)
      (fun program sourceTime =>
        clockFirst (compileSecond program) (clockSecond program sourceTime)) :=
  simulatesInTime_comp_internal hfirst hsecond

/-- Efficient oracle universality for any clock policy implies semantic oracle
universality.
@isnad1 id=isuniver.1h3v.s4.8095a3d665b3 from=translated src=- shape=3c964571 vocab=dd8d7752
-/
theorem IsEfficientlyUniversalFor.isUniversal
    {simulator : OracleTM firstTapes}
    {admissible : TM.TimeOverhead → Prop}
    (h : simulator.IsEfficientlyUniversalFor admissible) :
    simulator.IsUniversal :=
  efficientlyUniversalFor_isUniversal_internal h

/-- Polynomially efficient oracle universality implies semantic oracle
universality.
@isnad1 id=isuniver.1h2v.s3.80bf34b4f50f from=translated src=- shape=b28a8773 vocab=b17ce754
-/
theorem IsEfficientlyUniversal.isUniversal
    {simulator : OracleTM firstTapes}
    (h : simulator.IsEfficientlyUniversal) : simulator.IsUniversal :=
  efficientlyUniversalFor_isUniversal_internal h

/-- Weakening the admissible clock policy preserves oracle universality.
@isnad1 id=iseffici.1h5v.s5.dce89f5721db from=translated src=- shape=96bf3fe0 vocab=cb02b7d7
-/
theorem IsEfficientlyUniversalFor.mono
    {simulator : OracleTM firstTapes}
    {firstPolicy secondPolicy : TM.TimeOverhead → Prop}
    (hpolicy : ∀ clock, firstPolicy clock → secondPolicy clock)
    (h : simulator.IsEfficientlyUniversalFor firstPolicy) :
    simulator.IsEfficientlyUniversalFor secondPolicy :=
  efficientlyUniversalFor_mono_internal hpolicy h

end OracleTM

end Complexity
