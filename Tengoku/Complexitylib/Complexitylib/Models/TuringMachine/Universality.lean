/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Universality.Internal

/-!
# Generic universal-machine interfaces

This module gives machine-independent definitions of semantic and efficient
universality. A simulation compiler acts on arbitrary binary programs; its
correctness does not mention a concrete description codec. Additive description
overhead and an explicit program-sensitive clock are separate reusable
hypotheses. Universality requires the compiler to be computable.

The default `IsEfficientlyUniversal` policy asks for a polynomial in source
running time and source-program length. `IsEfficientlyUniversalFor` remains
available for sharper policies.

## Main results

- `TM.IsComputable.comp` -- computable string functions compose
- `TM.Simulates.refl`, `TM.Simulates.comp` -- semantic simulation is compositional
- `TM.HasAdditiveProgramOverhead.comp` -- additive compiler costs compose
- `TM.SimulatesInTime.comp` -- exact simulation clocks compose
- `TM.PolynomialTimeOverhead.comp` -- polynomial clocks survive compilation
- `TM.IsEfficientlyUniversalFor.isUniversal` -- efficient implies semantic
- `TM.Simulates.isUniversal` -- universality transfers through a simulator
-/

public section

namespace Complexity

namespace TM

variable {firstTapes secondTapes thirdTapes : ℕ}

/-- Every machine simulates itself under the identity compiler.
@isnad1 id=simulate.0h2v.s3.30cf04548982 from=translated src=- shape=5fca6213 vocab=2d6356e4
-/
theorem Simulates.refl (machine : TM firstTapes) : machine.Simulates machine id :=
  simulates_refl_internal machine

/-- Semantic simulations compose, with the inner compiler applied first.
@isnad1 id=simulate.2h8v.s5.a80084d71e72 from=translated src=- shape=014dd85b vocab=80afe1f3
-/
theorem Simulates.comp {first : TM firstTapes} {second : TM secondTapes}
    {third : TM thirdTapes} {compileFirst compileSecond : List Bool → List Bool}
    (hFirst : first.Simulates second compileFirst)
    (hSecond : second.Simulates third compileSecond) :
    first.Simulates third (compileFirst ∘ compileSecond) :=
  simulates_comp_internal hFirst hSecond

/-- The identity compiler has zero additive program overhead.
@isnad1 id=hasaddit.0h0v.s3.ed2b47a45c1f from=translated src=- shape=bbf18520 vocab=a4c41115
-/
theorem HasAdditiveProgramOverhead.id : HasAdditiveProgramOverhead id 0 :=
  additiveProgramOverhead_id_internal

/-- A larger additive constant preserves a compiler-length bound.
@isnad1 id=hasaddit.2h3v.s4.89109dd00a55 from=translated src=- shape=8c4751ed vocab=54a2a0ee
-/
theorem HasAdditiveProgramOverhead.mono {compile : List Bool → List Bool}
    {first second : ℕ} (hbound : first ≤ second)
    (hoverhead : HasAdditiveProgramOverhead compile first) :
    HasAdditiveProgramOverhead compile second :=
  additiveProgramOverhead_mono_internal hbound hoverhead

/-- Additive compiler-length bounds compose by addition.
@isnad1 id=hasaddit.2h4v.s5.ed0c49e5ab8a from=translated src=- shape=12b9d3e5 vocab=1fbb2495
-/
theorem HasAdditiveProgramOverhead.comp
    {compileFirst compileSecond : List Bool → List Bool} {first second : ℕ}
    (hFirst : HasAdditiveProgramOverhead compileFirst first)
    (hSecond : HasAdditiveProgramOverhead compileSecond second) :
    HasAdditiveProgramOverhead (compileFirst ∘ compileSecond) (second + first) :=
  additiveProgramOverhead_comp_internal hFirst hSecond

/-- Identity execution has the identity time overhead.
@isnad1 id=simulate.0h2v.s4.f93f67bc066d from=translated src=- shape=ed6f81a7 vocab=07ef65f0
-/
theorem SimulatesInTime.refl (machine : TM firstTapes) :
    machine.SimulatesInTime machine id (fun _ sourceTime => sourceTime) :=
  simulatesInTime_refl_internal machine

/-- Enlarging a simulation clock preserves a timed simulation.
@isnad1 id=simulate.2h7v.s5.6d80b0037b1f from=translated src=- shape=d4565858 vocab=272c30c9
-/
theorem SimulatesInTime.mono {simulator : TM firstTapes} {source : TM secondTapes}
    {compile : List Bool → List Bool} {firstClock secondClock : TimeOverhead}
    (hclock : ∀ program sourceTime, firstClock program sourceTime ≤
      secondClock program sourceTime)
    (hsim : simulator.SimulatesInTime source compile firstClock) :
    simulator.SimulatesInTime source compile secondClock :=
  simulatesInTime_mono_internal hclock hsim

/-- Timed simulations compose by feeding the inner compiled program and clock
to the outer clock.
@isnad1 id=simulate.2h10v.s6.6c0784dbcc16 from=translated src=- shape=045a4427 vocab=e1eddde7
-/
theorem SimulatesInTime.comp {first : TM firstTapes} {second : TM secondTapes}
    {third : TM thirdTapes} {compileFirst compileSecond : List Bool → List Bool}
    {clockFirst clockSecond : TimeOverhead}
    (hFirst : first.SimulatesInTime second compileFirst clockFirst)
    (hSecond : second.SimulatesInTime third compileSecond clockSecond) :
    first.SimulatesInTime third (compileFirst ∘ compileSecond)
      (fun program sourceTime =>
        clockFirst (compileSecond program) (clockSecond program sourceTime)) :=
  simulatesInTime_comp_internal hFirst hSecond

/-- The identity clock is polynomial.
@isnad1 id=polynomi.0h0v.s2.d98c66ca1f19 from=translated src=- shape=9483f484 vocab=a51de042
-/
theorem PolynomialTimeOverhead.identity :
    PolynomialTimeOverhead (fun _program sourceTime => sourceTime) :=
  polynomialTimeOverhead_identity_internal

/-- Polynomial clocks compose through a compiler with additive length overhead.
@isnad1 id=polynomi.3h4v.s5.578f9011da8c from=translated src=- shape=7cc963ba vocab=a442247e
-/
theorem PolynomialTimeOverhead.comp
    {compileInner : List Bool → List Bool} {additive : ℕ}
    {clockOuter clockInner : TimeOverhead}
    (hlength : HasAdditiveProgramOverhead compileInner additive)
    (hOuter : PolynomialTimeOverhead clockOuter)
    (hInner : PolynomialTimeOverhead clockInner) :
    PolynomialTimeOverhead (fun program sourceTime =>
      clockOuter (compileInner program) (clockInner program sourceTime)) :=
  polynomialTimeOverhead_comp_internal hlength hOuter hInner

/-- Universality for any admissible time policy implies semantic universality.
@isnad1 id=isuniver.1h3v.s4.c644b8cc819e from=translated src=- shape=3c964571 vocab=1c5eb34d
-/
theorem IsEfficientlyUniversalFor.isUniversal {simulator : TM firstTapes}
    {admissible : TimeOverhead → Prop}
    (h : simulator.IsEfficientlyUniversalFor admissible) : simulator.IsUniversal :=
  efficientlyUniversalFor_isUniversal_internal h

/-- Polynomially efficient universality implies semantic universality.
@isnad1 id=isuniver.1h2v.s3.6a70a0f0d757 from=translated src=- shape=b28a8773 vocab=17569727
-/
theorem IsEfficientlyUniversal.isUniversal {simulator : TM firstTapes}
    (h : simulator.IsEfficientlyUniversal) : simulator.IsUniversal :=
  efficientlyUniversalFor_isUniversal_internal h

/-- Weakening the admissibility policy preserves efficient universality.
@isnad1 id=iseffici.1h5v.s5.58e7f964f2fb from=translated src=- shape=96bf3fe0 vocab=aef309ab
-/
theorem IsEfficientlyUniversalFor.mono {simulator : TM firstTapes}
    {firstPolicy secondPolicy : TimeOverhead → Prop}
    (hpolicy : ∀ clock, firstPolicy clock → secondPolicy clock)
    (h : simulator.IsEfficientlyUniversalFor firstPolicy) :
    simulator.IsEfficientlyUniversalFor secondPolicy :=
  efficientlyUniversalFor_mono_internal hpolicy h

end TM

end Complexity
