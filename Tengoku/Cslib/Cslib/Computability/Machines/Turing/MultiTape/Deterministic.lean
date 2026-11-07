/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module

public import Tengoku.Seed.Algebra.Order.Group.Abs
public import Tengoku.Seed.Algebra.Order.Group.Int
public import Tengoku.Seed.Algebra.Order.BigOperators.Group.Finset
public import Tengoku
public import Tengoku.Cslib.Cslib.Foundations.Relation.RelatesInSteps
public import Tengoku.Cslib.Cslib.Computability.Machines.Turing.MultiTape.Configuration

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Deterministic Multi-Tape Turing Machines

Defines deterministic Turing machines with a read-only input tape, `k` work tapes and one write-only
output tape.
The tapes contain symbols from `Option Symbol` for a finite alphabet `Symbol` (where `none` is the
blank symbol).

## Design

The multi-tape Turing machine uses a read-only input tape, `k` work tapes and a write-only output
tape.
The input head can move freely on the input, but any move attempt beyond one cell outside the input
results in no movement.
The transition function can optionally output one symbol, which models the write-only output tape.
Because of these restrictions, we ignore the input and output tapes for space usage of the machine.
The space usage is defined as the total number of cells the work tape heads visited during
execution.

Restricting the movement of the input head is not essential, but useful because it allows
us to easily bound the number of possible configurations of a space-bounded machine. Most textbooks
have this restriction.

Instead of considering the cells _visited_ by the work tape heads, some textbooks
(including [AroraBarak09]) only consider the number of cells that contain
a non-blank symbol at some point in the execution or the number of cells written to. This allows
work tape heads to freely move at no cost as long as they do not write. It is
important to note that this causes `DSPACE(1)` to include `DSPACE(log log n)`, a class that
contains e.g. the non-regular language `{0^n 1^n | n ∈ ℕ}` (it is accepted by a TM that writes a
single marker on the work tape and then counts the number of symbols by work tape head movement
without writing).
Defining space usage via "cells visited" thus yields the more fine-grained "complexity world" in
which `DSPACE(1)` is exactly the class of regular languages.

This definition is adapted from the one in [Papadimitriou94], chapter 2.3 including
the sub-linear space modifications from chapter 2.5 with the following changes:
- We allow Turing machines to choose to not write on a tape. This is equivalent to
  writing the read symbol again but makes it easier to reason about the semantics.
- Our tapes are infinite in both directions instead of just to the right. This definition is
  equivalent (see [AroraBarak09], Claim 1.4). It saves us from having to add a "start marker" to
  the alphabet.
- We only have a single halting state. The different ways to halt (accepting, rejecting, etc) can
  be distinguished based on the output.
- The way to prevent the input head to move outside the input is enforced by the interpretation
  and not by a restriction on the transition function. The two definitions are equivalent, but
  not restricting the transition function makes it easier to define a universal machine.

## Important Declarations

We define a number of structures and concepts related to multi-tape Turing machine computation:

* `MultiTapeTM`: the TM itself
* `spaceUsed`: the number of work tape cells touched by the heads until a certain step
* `TransitionRelation`: the transition relation from one configuration to the next
* `HaltsAt`: the run from a configuration halts at exactly a given step
* `spaceUsed`: the number of tape cells touched by work tape heads, our main space measure
* `ComputesInTimeAndSpace`: a proof that a specific TM computes an output from an input in a certain
    number of steps and using a certain number of tape cells
* `ComputesFunInTimeAndSpace`: a machine computes a function between specified encodings,
    respecting time and space bounds on each actual input.
* `ComputableInTimeAndSpace`: such a machine exists with binary alphabet and finitely many states.
* `ComputableInTimeAndSpaceOfLength`: the specialization to bounds on encoded input length.
* `DecidableInTimeAndSpace`: a proof that a TM decides a language within a certain time
    and space bound.

There are two ways to talk about the behaviour of a multi-tape Turing machine, and they are
proven to be equivalent.

* `MultiTapeTM.runFrom`: the configuration reached after a given number of execution steps
* `RelatesInSteps tm.TransitionRelation cfg cfg' t`: a proof that `tm` transforms the configuration
    `cfg` into `cfg'` in exactly `t` steps

## References

* [C. Papadimitriou, *Computational Complexity*][Papadimitriou94]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]

-/

@[expose] public section

open Cslib Relation

namespace Turing

variable {k : ℕ} {State Symbol : Type*}

/--
A multi-tape Turing machine with `k` work tapes over the alphabet of `Option Symbol` (where `none`
is the blank tape symbol). Note that it is not required that `Symbol` or `State` are finite
to keep the definition more general. The restriction will be introduced once we start talking about
computability by Turing machines in general.-/
structure MultiTapeTM (k : ℕ) (Symbol State : Type*) where
  /-- initial state-/
  q₀ : State
  /-- transition function, mapping a state, the current input symbol and a tuple of work head
  symbols to a movement for the input head, actions on the work tape, optionally a symbol to output
  and the successor state-/
  tr (q : State) (input : Option Symbol) (work : Fin k → Option Symbol) :
    Action k Symbol State

namespace MultiTapeTM

variable {tm : MultiTapeTM k Symbol State}

section Cfg

/-!
## Stepping a Turing Machine

This section defines the step function that lets the machine transition from one configuration to
the next, and the configuration reached after a number of steps. Configurations themselves are
defined in `Cslib.Computability.Machines.Turing.MultiTape.Configuration`.
-/

/-- The step function corresponding to a `MultiTapeTM`.-/
def step (cfg : Cfg k Symbol State input) : Cfg k Symbol State input :=
  match cfg.state with
  -- in the halting state, we stay at the configuration
  | none => cfg
  | some q => (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).apply cfg

/-- One step at a live state is the transition's action applied to the configuration.
@isnad1 id=eq.1h7v.s6.3c72afa7faf8 from=translated src=- shape=78660b4b vocab=31240ac4
-/
public lemma step_apply_of_state {cfg : Cfg k Symbol State input} {q : State}
    (h : cfg.state = some q) :
    tm.step cfg = (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).apply cfg := by
  rw [step, h]

/-- The symbol (optionally) output when executing one step starting from configuration `cfg`.-/
def outputSymbol (cfg : Cfg k Symbol State input) : Option Symbol :=
  match cfg.state with
  | none => none
  | some q => (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).output

/-- The input head after a live step.
@isnad1 id=eq.1h7v.s6.17d8996e5fe6 from=translated src=- shape=28fe1929 vocab=7d726cfd
-/
public lemma step_inputPos_of_state {cfg : Cfg k Symbol State input} {q : State}
    (h : cfg.state = some q) :
    (tm.step cfg).inputPos =
      moveInputPos cfg.inputPos (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).inputTape := by
  rw [step_apply_of_state h, Action.apply_inputPos]

/-- A work tape after a live step.
@isnad1 id=eq.1h8v.s7.63674c4a5e3c from=translated src=- shape=05d787c3 vocab=bd05a3c6
-/
public lemma step_workTapes_of_state {cfg : Cfg k Symbol State input} {q : State}
    (h : cfg.state = some q) (i : Fin k) :
    (tm.step cfg).workTapes i =
      match (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).workTapes i |>.1 with
      | none => cfg.workTapes i
      | some s => Function.update (cfg.workTapes i) (cfg.workTapePos i) s := by
  rw [step_apply_of_state h]
  rfl

/-- A work tape head after a live step.
@isnad1 id=eq.1h8v.s6.628439613121 from=translated src=- shape=0076d335 vocab=b7435a88
-/
public lemma step_workTapePos_of_state {cfg : Cfg k Symbol State input} {q : State}
    (h : cfg.state = some q) (i : Fin k) :
    (tm.step cfg).workTapePos i =
      cfg.workTapePos i + ((tm.tr q cfg.inputSymbol cfg.workTapeSymbols).workTapes i).2 := by
  rw [step_apply_of_state h]
  rfl

/-- The initial configuration corresponding to an input string.-/
@[simp]
def initCfg (input : List Symbol) : Cfg k Symbol State input := Cfg.init tm.q₀ input

/--
@isnad1 id=eq.1h6v.s5.61e11d3c758f from=translated src=- shape=2ac197fb vocab=d3a40da4
-/
@[simp]
lemma step_of_halt {cfg : Cfg k Symbol State input} (h : cfg.state = none) :
    tm.step cfg = cfg := by
  unfold step
  rw [h]

/-- The configuration reached by running the Turing machine for `t` steps from `cfg`.
If the Turing machine halts, it will stay at the halting configuration.-/
def runFrom (cfg : Cfg k Symbol State input) (t : ℕ) : Cfg k Symbol State input := tm.step^[t] cfg

/-- Nothing changes after the machine has halted.
@isnad1 id=eq.2h8v.s6.bc8da02bb233 from=translated src=- shape=6a82ab26 vocab=8703aa09
-/
lemma runFrom_eq_of_halt
    (tm : MultiTapeTM k Symbol State)
    (cfg : Cfg k Symbol State input) {τ t : ℕ} (hle : τ ≤ t)
    (hhalt : (tm.runFrom cfg τ).state = none) :
    tm.runFrom cfg t = tm.runFrom cfg τ := by
  rw [runFrom, ← Nat.sub_add_cancel hle, Function.iterate_add_apply]
  exact Function.iterate_fixed (step_of_halt hhalt) _

/-- The machine `tm` started in `cfg` halts at step `t`: it is halted after `t` steps and not
halted after any smaller number of steps.-/
def HaltsAt (tm : MultiTapeTM k Symbol State) {input : List Symbol}
    (cfg : Cfg k Symbol State input) (t : ℕ) : Prop :=
  (tm.runFrom cfg t).Halted ∧ ∀ s < t, ¬(tm.runFrom cfg s).Halted

namespace HaltsAt

variable {input : List Symbol} {cfg : Cfg k Symbol State input} {s t : ℕ}

/--
@isnad1 id=halted.1h7v.s5.251e700e9017 from=translated src=- shape=65304c74 vocab=d0a43ee4
-/
lemma halted (h : tm.HaltsAt cfg t) : (tm.runFrom cfg t).Halted := h.1

/--
@isnad1 id=not.2h8v.s5.262010eb8292 from=translated src=- shape=30098625 vocab=a0cd737b
-/
lemma not_halted (h : tm.HaltsAt cfg t) (hs : s < t) : ¬(tm.runFrom cfg s).Halted := h.2 s hs

/-- The halting step is the first step at which the machine is halted.
@isnad1 id=le.2h8v.s5.84d927f7a67f from=translated src=- shape=bd782134 vocab=7e5619ef
-/
lemma le_of_halted (h : tm.HaltsAt cfg t) (hs : (tm.runFrom cfg s).Halted) : t ≤ s :=
  Nat.le_of_not_lt fun hlt => h.not_halted hlt hs

/-- The halting step is unique.
@isnad1 id=eq.2h8v.s5.ff1c0dea5d4d from=translated src=- shape=7e6e61d4 vocab=951783b0
-/
lemma unique (h₁ : tm.HaltsAt cfg s) (h₂ : tm.HaltsAt cfg t) : s = t :=
  Nat.le_antisymm (h₁.le_of_halted h₂.halted) (h₂.le_of_halted h₁.halted)

/-- From the halting step on, the configuration does not change.
@isnad1 id=eq.2h8v.s5.3528c8cc9e2f from=translated src=- shape=71c5d7c8 vocab=0115a1bd
-/
lemma runFrom_eq (h : tm.HaltsAt cfg t) (hts : t ≤ s) : tm.runFrom cfg s = tm.runFrom cfg t :=
  runFrom_eq_of_halt tm cfg hts h.halted

end HaltsAt

/-- A run that is halted after `t` steps halts at some step `u ≤ t`.
@isnad1 id=ex.1h7v.s5.97b1775f0935 from=translated src=- shape=21d1fc3a vocab=7e5619ef
-/
lemma exists_haltsAt {input : List Symbol} {cfg : Cfg k Symbol State input} {t : ℕ}
    (hhalt : (tm.runFrom cfg t).Halted) : ∃ u ≤ t, tm.HaltsAt cfg u := by
  classical
  have hex : ∃ n, (tm.runFrom cfg n).Halted := ⟨t, hhalt⟩
  exact ⟨Nat.find hex, Nat.find_min' hex hhalt, Nat.find_spec hex,
    fun s hs => Nat.find_min hex hs⟩

/-- A run that is halted after some number of steps halts at exactly one step.
@isnad1 id=existsun.1h7v.s5.061db4629b46 from=translated src=- shape=be4baecf vocab=8ed26228
-/
lemma existsUnique_haltsAt {input : List Symbol} {cfg : Cfg k Symbol State input} {t : ℕ}
    (hhalt : (tm.runFrom cfg t).Halted) : ∃! u, tm.HaltsAt cfg u :=
  let ⟨u, _, hu⟩ := exists_haltsAt hhalt
  ⟨u, hu, fun _ h => h.unique hu⟩

/--
@isnad1 id=eq.1h6v.s5.1f2a635d5544 from=translated src=- shape=62f224b2 vocab=97f11ee5
-/
@[simp]
lemma outputSymbol_of_halt {cfg : Cfg k Symbol State input} (h_halt : cfg.state = none) :
    tm.outputSymbol cfg = none := by
  simp [outputSymbol, h_halt]

/-- The work-tape head moves by at most one cell in a single step.
@isnad1 id=le.0h7v.s5.a1a3b52f1dd4 from=translated src=- shape=b7512c9d vocab=0c9afa20
-/
lemma workTapePos_step_le (c : Cfg k Symbol State input) (i : Fin k) :
    |(tm.step c).workTapePos i - c.workTapePos i| ≤ 1 := by
  unfold step
  cases hstate : c.state with
  | none => simp
  | some q => exact workTapePos_apply_le _ c i

end Cfg

section Space
/-! Now we define space usage and add some helper lemmas. -/

/-- The set of positions visited by the head of work tape `i` in the computation starting from
configuration `cfg` up to step `t`.-/
def visitedByTapeHead (cfg : Cfg k Symbol State input) (t : ℕ) (i : Fin k) : Finset ℤ :=
  Finset.univ.image fun n : Fin (t + 1) => (tm.runFrom cfg n).workTapePos i

/--
The number of work tape cells touched by the head of tape `i` in the computation starting from
configuration `cfg` up to step `t`.-/
def spaceUsedByTape (cfg : Cfg k Symbol State input) (t : ℕ) (i : Fin k) : ℕ :=
  (tm.visitedByTapeHead cfg t i).card

/--
The number of work tape cells touched by a computation starting from configuration
`cfg` up to step `t`.-/
def spaceUsed (cfg : Cfg k Symbol State input) (t : ℕ) : ℕ := ∑ i, tm.spaceUsedByTape cfg t i

/-- A zero-tape Turing machine uses zero space.
@isnad1 id=eq.1h7v.s5.c2c09fe9eac9 from=translated src=- shape=891cb2a7 vocab=f08cfbfa
-/
@[simp]
lemma spaceUsed_zero_tapes_eq_zero (cfg : Cfg k Symbol State input) (t : ℕ) (h_zero : k = 0) :
    tm.spaceUsed cfg t = 0 := by
  unfold spaceUsed
  subst h_zero
  simp

/-- Each tape's space usage is bounded by the total space used.
@isnad1 id=le.0h8v.s5.b247924affbc from=translated src=- shape=a33326f6 vocab=9aac4bef
-/
lemma spaceUsedByTape_le_spaceUsed (cfg : Cfg k Symbol State input) (t : ℕ) (i : Fin k) :
    tm.spaceUsedByTape cfg t i ≤ tm.spaceUsed cfg t :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

end Space

open Cfg

/--
The `TransitionRelation` corresponding to a `MultiTapeTM k Symbol`
is defined by the `step` function,
which maps a configuration to its next configuration.-/
@[scoped grind =]
def TransitionRelation (c₁ c₂ : Cfg k Symbol State input) : Prop := tm.step c₁ = c₂

/-- One step appends the symbol (optionally) emitted by that step to the output tape.
@isnad1 id=eq.0h6v.s5.c3cee36514f3 from=translated src=- shape=5e1bc9ff vocab=b1d5b63e
-/
@[simp]
lemma step_output (cfg : Cfg k Symbol State input) :
    (tm.step cfg).output = cfg.output ++ (tm.outputSymbol cfg).toList := by
  unfold step outputSymbol Action.apply
  cases cfg.state <;> simp

/-- In `t` steps the input head moves at most `t` positions to the right.
@isnad1 id=le.0h7v.s6.a5c2fe3c9d8d from=translated src=- shape=e526df3c vocab=6a6cdf43
-/
lemma inputPos_runFrom_le (tm : MultiTapeTM k Symbol State)
    (cfg : Cfg k Symbol State input) (t : ℕ) :
    ((tm.runFrom cfg t).inputPos : ℕ) ≤ (cfg.inputPos : ℕ) + t := by
  induction t with
  | zero => simp [runFrom]
  | succ t ih =>
    rw [runFrom, Function.iterate_succ_apply', ← runFrom]
    by_cases hq : (tm.runFrom cfg t).state = none
    · rw [step_of_halt hq]
      omega
    · obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hq
      have h : ((tm.step (tm.runFrom cfg t)).inputPos : ℕ) ≤
          ((tm.runFrom cfg t).inputPos : ℕ) + 1 := by
        rw [step_inputPos_of_state hq]
        exact val_moveInputPos_le _ _
      omega

/-- The output does not change after the machine has halted.
@isnad1 id=eq.2h8v.s6.79a92e0e71b9 from=translated src=- shape=080f9da9 vocab=3328d0c4
-/
lemma runFrom_output_eq_of_halt
    (tm : MultiTapeTM k Symbol State)
    (cfg : Cfg k Symbol State input) {τ t : ℕ} (hle : τ ≤ t)
    (hhalt : (tm.runFrom cfg τ).state = none) :
    (tm.runFrom cfg t).output = (tm.runFrom cfg τ).output :=
  congrArg Cfg.output (tm.runFrom_eq_of_halt cfg hle hhalt)

/-- The output only grows during a run.
@isnad1 id=monotone.0h6v.s5.55ec43cc3e5f from=translated src=- shape=6b8de77d vocab=60f9e45c
-/
public lemma length_output_mono (tm : MultiTapeTM k Symbol State) (cfg : Cfg k Symbol State input) :
    Monotone fun t => (tm.runFrom cfg t).output.length :=
  monotone_nat_of_le_succ fun t => by simp [runFrom, Function.iterate_succ_apply']

/-- A machine emits at most one symbol per step.
@isnad1 id=le.0h7v.s5.dd62f118e127 from=translated src=- shape=0d031e9f vocab=b79fb45e
-/
theorem length_output_runFrom_le (tm : MultiTapeTM k Symbol State)
    (cfg : Cfg k Symbol State input) (t : ℕ) :
    (tm.runFrom cfg t).output.length ≤ cfg.output.length + t := by
  induction t with
  | zero => simp [runFrom]
  | succ t ih =>
    rw [runFrom, Function.iterate_succ_apply', ← runFrom, step_output, List.length_append]
    have := (tm.outputSymbol (tm.runFrom cfg t)).length_toList_le
    omega

/-- A proof that the Turing machine `tm` on input `input` outputs `output` in at most `t` steps
and uses exactly `s` space.
Note that this does not require the alphabet or state set to be finite.-/
def ComputesInTimeAndSpace
    (tm : MultiTapeTM k Symbol State)
    (input output : List Symbol)
    (t s : ℕ) : Prop :=
  (tm.runFrom (tm.initCfg input) t).state = none ∧
  (tm.runFrom (tm.initCfg input) t).output = output ∧
  tm.spaceUsed (tm.initCfg input) t = s

/-- A machine computes `f` between the supplied encodings, with bounds depending on the input.
The machine's alphabet and state type need not be finite.-/
def ComputesFunInTimeAndSpace {α β : Type*}
    (tm : MultiTapeTM k Symbol State)
    (encIn : α ↪ List Symbol) (encOut : β ↪ List Symbol)
    (f : α → β) (t s : α → ℕ) : Prop :=
  ∀ a, ∃ t' ≤ t a, ∃ s' ≤ s a,
    ComputesInTimeAndSpace tm (encIn a) (encOut (f a)) t' s'

/-- A function is computable within the input-indexed bounds by a machine with binary alphabet
and finitely many states.-/
def ComputableInTimeAndSpace {α β : Type*}
    (f : α → β) (encIn : α ↪ List Bool) (encOut : β ↪ List Bool)
    (t s : α → ℕ) : Prop :=
  ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State),
    ComputesFunInTimeAndSpace tm encIn encOut f t s

/-- There exists a binary Turing machine with finitely many states that, for every input `a`,
computes `encOut (f a)` from `encIn a` in at most `t (encIn a).length` steps,
using at most `s (encIn a).length` work-tape cells.-/
abbrev ComputableInTimeAndSpaceOfLength {α β : Type*}
    (f : α → β) (encIn : α ↪ List Bool) (encOut : β ↪ List Bool)
    (t s : ℕ → ℕ) : Prop :=
  ComputableInTimeAndSpace f encIn encOut
    (fun a => t (encIn a).length) (fun a => s (encIn a).length)

/-- Resource bounds can be weakened independently on every input.
@isnad1 id=computes.3h13v.s6.3aa584072c48 from=translated src=- shape=23358e0e vocab=63ef63d0
-/
theorem ComputesFunInTimeAndSpace.mono {α β : Type*}
    {tm : MultiTapeTM k Symbol State} {encIn : α ↪ List Symbol} {encOut : β ↪ List Symbol}
    {f : α → β} {t s t' s' : α → ℕ}
    (h : ComputesFunInTimeAndSpace tm encIn encOut f t s)
    (ht : ∀ a, t a ≤ t' a) (hs : ∀ a, s a ≤ s' a) :
    ComputesFunInTimeAndSpace tm encIn encOut f t' s' := fun a => by
  obtain ⟨u, hu, v, hv, hc⟩ := h a
  exact ⟨u, hu.trans (ht a), v, hv.trans (hs a), hc⟩

/-- Computability is monotone in the resource bounds.
@isnad1 id=computab.3h9v.s6.9cc9e5c305a3 from=translated src=- shape=ca57697c vocab=6cc896f8
-/
theorem ComputableInTimeAndSpace.mono {α β : Type*}
    {f : α → β} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {t s t' s' : α → ℕ}
    (h : ComputableInTimeAndSpace f encIn encOut t s)
    (ht : ∀ a, t a ≤ t' a) (hs : ∀ a, s a ≤ s' a) :
    ComputableInTimeAndSpace f encIn encOut t' s' := by
  obtain ⟨k, State, hfinite, tm, htm⟩ := h
  exact ⟨k, State, hfinite, tm, htm.mono ht hs⟩

/-- A machine emits at most one symbol per step, so the encoded result of a computation is no
longer than its time bound. This is the only bound available on the length of an intermediate
result: a machine can produce an output much longer than the space it uses.
@isnad1 id=le.1h8v.s5.fe73b69f46ad from=translated src=- shape=44ea6ecd vocab=d3a0c985
-/
theorem ComputableInTimeAndSpace.length_encOut_le {α β : Type*}
    {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {f : α → β} {t s : α → ℕ}
    (h : ComputableInTimeAndSpace f encIn encOut t s) (a : α) :
    (encOut (f a)).length ≤ t a := by
  obtain ⟨k, State, _, tm, htm⟩ := h
  obtain ⟨t', ht', s', _, _, hout, _⟩ := htm a
  have hlen := length_output_runFrom_le tm (tm.initCfg (encIn a)) t'
  rw [hout] at hlen
  have h0 : (tm.initCfg (encIn a)).output.length = 0 := rfl
  omega

open Classical in
/-- The Boolean indicator function of a set.-/
noncomputable def indicator {α : Type*} (L : Set α) : α → Bool :=
  fun x => if x ∈ L then true else false

/-- A set is decidable within the given input-indexed bounds when its Boolean indicator is.-/
def DecidableInTimeAndSpace {α : Type*} (L : Set α) (enc : α ↪ List Bool)
    (t s : α → ℕ) : Prop :=
  ComputableInTimeAndSpace (indicator L) enc ⟨fun b => [b], by intro a b h; simpa using h⟩ t s

/-- This lemma translates between the relational notion and the iterated step notion. The latter
can be more convenient especially for deterministic machines as we have here.
@isnad1 id=iff.0h8v.s5.520c54242877 from=translated src=- shape=d30c706d vocab=9da8749e
-/
@[scoped grind =]
lemma relatesInSteps_iff_runFrom_eq
    (tm : MultiTapeTM k Symbol State)
    (cfg₁ cfg₂ : Cfg k Symbol State input)
    (t : ℕ) :
    RelatesInSteps tm.TransitionRelation cfg₁ cfg₂ t ↔ tm.runFrom cfg₁ t = cfg₂ := by
  unfold runFrom
  induction t generalizing cfg₁ cfg₂ with
  | zero => simp
  | succ t ih =>
    rw [RelatesInSteps.succ_iff, Function.iterate_succ_apply']
    constructor
    · grind
    · intro h_runFrom
      use tm.step^[t] cfg₁
      grind

/-- If a deterministic machine repeats a non-halting configuration, it never halts,
because the sequence between the two configurations will loop forever.
Note that this can be applied to two arbitrary and different time steps `t` and `t + Δ`
using `Function.iterate_add_apply`.
@isnad1 id=ne.2h8v.s6.7f6670b1f338 from=translated src=- shape=517ec586 vocab=46afefec
-/
lemma not_halts_of_repeat_nonhalt
    (cfg : Cfg k Symbol State input)
    (h_not_halt : cfg.state ≠ none)
    (t : ℕ)
    (heq : tm.runFrom cfg (t + 1) = cfg) :
    ∀ t', (tm.runFrom cfg t').state ≠ none := by
  intro t'
  -- The configuration will repeat every `t + 1` steps.
  have hloop : ∀ n, tm.runFrom cfg (n * (t + 1)) = cfg := by
    intro n
    unfold runFrom
    rw [Nat.mul_comm, Function.iterate_mul]
    exact Function.iterate_fixed heq n
  by_contra hnh
  -- Assuming the machine halts at step `t'`, it is also halted at step `t' * (t + 1)`
  have h₁ : (tm.runFrom cfg (t' * (t + 1))).state = none := by
    have hle : t' ≤ t' * (t + 1) := by grind
    rwa [tm.runFrom_eq_of_halt cfg hle hnh]
  simp [hloop t', h_not_halt] at h₁

end MultiTapeTM

end Turing
