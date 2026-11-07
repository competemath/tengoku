/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Tengoku.Cslib.Cslib.Init

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Functional Labelled Transition System (FLTS)

A Functional Labelled Transition System is a special case of an `LTS` where transitions are
determined by a function.

This is a generalisation of deterministic finite-state machines.

## References

* [J. E. Hopcroft, R. Motwani, J. D. Ullman,
  *Introduction to Automata Theory, Languages, and Computation*][Hopcroft2006]
-/

@[expose] public section

namespace Cslib

/--
A Functional Labelled Transition System (`FLTS`) for a type of states (`State`) and a type of
transition labels (`Label`) consists of a labelled transition function (`tr`).-/
structure FLTS (State Label : Type*) where
  /-- The transition function.-/
  tr : State → Label → State

namespace FLTS

variable {State Label : Type*}

/-- Extended transition function.

Implementation note: compared to [Hopcroft2006], the definition consumes the input list of symbols
from the left (instead of the right), in order to match the way lists are constructed.-/
@[scoped grind =]
def mtr (flts : FLTS State Label) (s : State) (μs : List Label) := μs.foldl flts.tr s

/--
@isnad1 id=eq.0h4v.s4.f52c8d87d351 from=translated src=- shape=6f29b0b0 vocab=542ba056
-/
@[simp, scoped grind =]
theorem mtr_nil_eq {flts : FLTS State Label} {s : State} : flts.mtr s [] = s := rfl

/--
@isnad1 id=eq.0h6v.s5.1d8a23a8031f from=translated src=- shape=5554a034 vocab=fd08d5c6
-/
@[simp, scoped grind =]
theorem mtr_concat_eq {flts : FLTS State Label} {s : State} {μs : List Label} {μ : Label} :
    flts.mtr s (μs ++ [μ]) = flts.tr (flts.mtr s μs) μ := by
  grind

/--
@isnad1 id=eq.0h6v.s5.2a8591f0698f from=translated src=- shape=e848f8d8 vocab=864d9c74
-/
theorem mtr_append_eq {flts : FLTS State Label} {s : State} {μs1 μs2 : List Label} :
    flts.mtr s (μs1 ++ μs2) = flts.mtr (flts.mtr s μs1) μs2 := by
  simp [mtr]

end FLTS

end Cslib
