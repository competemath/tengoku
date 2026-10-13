/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Hoare.Space.Defs
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Hoare.Space.Internal

/-!
# Space-aware Hoare specifications

`TM.HoareSpace` states the all-reachable auxiliary-space invariant required by
`TM.ComputesInSpace`; `TM.HoareTimeSpace` pairs it with a terminating
time-bounded Hoare triple.
The public API includes structural rules, sequential composition, transducer
closure, and a fresh-start computation bridge.

## Main results

- `TM.HoareTimeSpace.consequence` — weaken/strengthen every contract component.
- `TM.HoareSpace.weaken_pre`, `TM.HoareSpace.mono` — structural space rules.
- `Cfg.WithinAuxSpace.reachesIn` — bound head growth along a concrete run.
- `TM.HoareTime.and_hoareSpace` — pair existing endpoint and safety proofs.
- `TM.HoareTime.toHoareTimeSpace` — derive all-reachable space from time and
  an initial head bound.
- `TM.seqTM_hoareTimeSpace` — compose two phases at one space budget.
- `TM.IsTransducer.seqTM` — sequential composition remains append-only.
- `TM.computesInSpace_of_hoareTimeSpace` — package per-input contracts.
-/

public section

namespace Complexity

namespace Cfg

/-- Enlarging the logical input region and work-space budget preserves an
auxiliary-space bound.
@isnad1 id=withinau.3h7v.s5.1c5164caf9aa from=translated src=- shape=dc480df7 vocab=268166dc
-/
theorem WithinAuxSpace.mono {c : Cfg n Q}
    {inputLength inputLength' space space' : ℕ}
    (h : c.WithinAuxSpace inputLength space)
    (hinput : inputLength ≤ inputLength') (hspace : space ≤ space') :
    c.WithinAuxSpace inputLength' space' :=
  h.mono_internal hinput hspace

/-- The standard combinator phase transition moves input and work heads by at
most one, so one additional auxiliary-space cell covers the seam.
@isnad1 id=withinau.1h5v.s5.98a0c7da9dcc from=translated src=- shape=6a550e38 vocab=e81c7248
-/
theorem WithinAuxSpace.transition {c : Cfg n Q}
    {inputLength space : ℕ} (h : c.WithinAuxSpace inputLength space) :
    ({ state := c.state,
       input := TM.transitionInput c.input,
       work := fun i => TM.transitionTape (c.work i),
       output := TM.transitionTape c.output } : Cfg n Q).WithinAuxSpace
      inputLength (space + 1) :=
  h.transition_internal

/-- A `time`-step run can increase every charged head position by at most
`time`, so adding that many cells preserves the auxiliary-space bound.
@isnad1 id=withinau.2h7v.s5.486c8e4e1fb7 from=translated src=- shape=f8e046a1 vocab=d9a15b7f
-/
theorem WithinAuxSpace.reachesIn {tm : TM n}
    {c c' : Cfg n tm.Q} {time inputLength space : ℕ}
    (h : c.WithinAuxSpace inputLength space)
    (hreach : tm.reachesIn time c c') :
    c'.WithinAuxSpace inputLength (space + time) :=
  h.reachesIn_internal hreach

end Cfg

namespace TM

variable {n : ℕ}

/-- **A step-closed configuration predicate discharges a space contract.** Supply any predicate
that holds at every start satisfying the precondition, is preserved by one step, and implies the
space bound; every reachable configuration then satisfies the bound. This is the workhorse for
machines whose space analysis is a phase invariant rather than a composition of subroutine
contracts.
@isnad1 id=hoarespa.1h8v.s6.200946129fcc from=translated src=- shape=cbae0b4c vocab=317f690c
-/
theorem hoareSpace_of_invariant {tm : TM n} {pre : TapePred n}
    {inputLength space : ℕ} (P : Cfg n tm.Q → Prop)
    (hinit : ∀ inp work out, pre inp work out →
      P { state := tm.qstart, input := inp, work := work, output := out })
    (hstep : ∀ c c', P c → tm.step c = some c' → P c')
    (hbound : ∀ c, P c → c.WithinAuxSpace inputLength space) :
    tm.HoareSpace pre inputLength space :=
  hoareSpace_of_invariant_internal P hinit hstep hbound

/-- Strengthening the precondition preserves an all-reachable space contract.
@isnad1 id=hoarespa.1h7v.s5.9bc32143cdda from=translated src=- shape=c4d92ee2 vocab=02951dd1
-/
theorem HoareSpace.weaken_pre {tm : TM n}
    {pre pre' : TapePred n} {inputLength space : ℕ}
    (h : tm.HoareSpace pre inputLength space)
    (hpre : ∀ inp work out, pre' inp work out → pre inp work out) :
    tm.HoareSpace pre' inputLength space :=
  h.weaken_pre_internal hpre

/-- Enlarging the logical input region and auxiliary-space budget preserves a
space contract.
@isnad1 id=hoarespa.3h7v.s5.bedd32f4c348 from=translated src=- shape=8deea61d vocab=cbaf4e76
-/
theorem HoareSpace.mono {tm : TM n}
    {pre : TapePred n} {inputLength inputLength' space space' : ℕ}
    (h : tm.HoareSpace pre inputLength space)
    (hinput : inputLength ≤ inputLength') (hspace : space ≤ space') :
    tm.HoareSpace pre inputLength' space' :=
  h.mono_internal hinput hspace

/-- Pair an existing terminating Hoare proof with an all-reachable space
proof. This is the main entry point for upgrading established subroutine
contracts without reproving their endpoint behavior.
@isnad1 id=hoaretim.2h7v.s5.0448cfcf1405 from=translated src=- shape=10c80201 vocab=1397ed72
-/
theorem HoareTime.and_hoareSpace {tm : TM n}
    {pre post : TapePred n} {time inputLength space : ℕ}
    (htime : tm.HoareTime pre post time)
    (hspace : tm.HoareSpace pre inputLength space) :
    tm.HoareTimeSpace pre post time inputLength space :=
  ⟨htime, hspace⟩

/-- Upgrade a terminating time-bounded Hoare triple to an all-reachable
time-and-space contract. If every starting configuration fits in
`initialSpace`, then at most one additional cell per machine step gives the
uniform bound `initialSpace + time`.
@isnad1 id=hoaretim.2h7v.s6.1a7ff624abf5 from=translated src=- shape=c4630c0e vocab=8e66ad76
-/
theorem HoareTime.toHoareTimeSpace {tm : TM n}
    {pre post : TapePred n} {time inputLength initialSpace : ℕ}
    (htime : tm.HoareTime pre post time)
    (hinitial : ∀ inp work out, pre inp work out →
      ({ state := tm.qstart, input := inp, work := work, output := out } :
        Cfg n tm.Q).WithinAuxSpace inputLength initialSpace) :
    tm.HoareTimeSpace pre post time inputLength (initialSpace + time) :=
  htime.toHoareTimeSpace_internal hinitial

/-- A time-and-space contract exposes its ordinary time-bounded Hoare triple.
@isnad1 id=hoaretim.1h7v.s5.45318507b02c from=translated src=- shape=de71bec1 vocab=22e5c60f
-/
theorem HoareTimeSpace.toHoareTime {tm : TM n}
    {pre post : TapePred n} {time inputLength space : ℕ}
    (h : tm.HoareTimeSpace pre post time inputLength space) :
    tm.HoareTime pre post time :=
  h.1

/-- A time-and-space contract exposes its all-reachable space component.
@isnad1 id=hoarespa.1h7v.s5.d606422d6d84 from=translated src=- shape=4711f781 vocab=ee8cdbe4
-/
theorem HoareTimeSpace.toHoareSpace {tm : TM n}
    {pre post : TapePred n} {time inputLength space : ℕ}
    (h : tm.HoareTimeSpace pre post time inputLength space) :
    tm.HoareSpace pre inputLength space :=
  h.2

/-- Consequence rule: strengthen the precondition, weaken the postcondition,
and enlarge any of the three numerical bounds.
@isnad1 id=hoaretim.4h14v.s6.b3ca03d059a8 from=translated src=- shape=7ab00e1c vocab=bab587fb
-/
theorem HoareTimeSpace.consequence {tm : TM n}
    {pre pre' post post' : TapePred n}
    {time time' inputLength inputLength' space space' : ℕ}
    (h : tm.HoareTimeSpace pre post time inputLength space)
    (hpre : ∀ inp work out, pre' inp work out → pre inp work out)
    (hpost : ∀ inp work out, post inp work out → post' inp work out)
    (htime : time ≤ time') (hinput : inputLength ≤ inputLength')
    (hspace : space ≤ space') :
    tm.HoareTimeSpace pre' post' time' inputLength' space' :=
  h.consequence_internal hpre hpost htime hinput hspace

/-- Sequentially composing one-way-output machines preserves the transducer
discipline.
@isnad1 id=istransd.2h3v.s4.9f96d800827e from=translated src=- shape=85b2e57a vocab=952dc3a9
-/
theorem IsTransducer.seqTM {tm₁ tm₂ : TM n}
    (h₁ : tm₁.IsTransducer) (h₂ : tm₂.IsTransducer) :
    (seqTM tm₁ tm₂).IsTransducer :=
  h₁.seqTM_internal h₂

/-- Sequential composition of time-and-space Hoare contracts.
@isnad1 id=hoaretim.2h13v.s6.7f5c7308cf98 from=translated src=- shape=014f2b93 vocab=c5dfbc49
-/
theorem seqTM_hoareTimeSpace (tm₁ tm₂ : TM n)
    {pre mid mid' post : TapePred n}
    {b₁ b₂ inputLength space₁ space₂ : ℕ}
    (h₁ : tm₁.HoareTimeSpace pre mid b₁ inputLength space₁)
    (htrans : ∀ inp work out, mid inp work out →
      mid' (transitionInput inp) (fun i => transitionTape (work i))
        (transitionTape out))
    (h₂ : tm₂.HoareTimeSpace mid' post b₂ inputLength space₂) :
    (seqTM tm₁ tm₂).HoareTimeSpace pre post (b₁ + 1 + b₂)
      inputLength (max space₁ space₂) :=
  seqTM_hoareTimeSpace_internal tm₁ tm₂ h₁ htrans h₂

/-- Per-input fresh-start time-and-space contracts package a total function
transducer satisfying `TM.ComputesInSpace`.
@isnad1 id=computes.2h5v.s6.5917256bf1ac from=translated src=- shape=76a2a501 vocab=5184d181
-/
theorem computesInSpace_of_hoareTimeSpace
    {tm : TM n} {f : List Bool → List Bool} {T S : ℕ → ℕ}
    (htrans : tm.IsTransducer)
    (h : ∀ x, tm.HoareTimeSpace
      (fun inp work out =>
        inp = Tape.init (x.map Γ.ofBool) ∧
        work = (fun _ => Tape.init []) ∧ out = Tape.init [])
      (fun _ _ out => out.HasOutput (f x))
      (T x.length) x.length (S x.length)) :
    tm.ComputesInSpace f S :=
  computesInSpace_of_hoareTimeSpace_internal htrans h

end TM

end Complexity
