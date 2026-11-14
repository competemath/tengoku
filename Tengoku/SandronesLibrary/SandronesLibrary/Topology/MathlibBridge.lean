/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.Foundation
import Tengoku.Seed.Topology.Continuous

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Bridge from textbook topology to Mathlib

This module is the only permitted dependency direction: a Sandrone textbook topology may be
installed locally as a Mathlib topology.  Core textbook modules must not import this file.
-/

namespace SandronesLibrary.Topology.TextbookTopology

variable {X Y : Type*}

set_option warn.classDefReducibility false in
/-- A textbook topology gives a Mathlib topology with exactly the same open sets.  This is an
implementation bridge, not the definition used by the textbook layer.-/
def toMathlib (τ : TextbookTopology X) : TopologicalSpace X where
  IsOpen := τ.IsOpen
  isOpen_univ := τ.isOpen_univ
  isOpen_inter := τ.isOpen_inter
  isOpen_sUnion := τ.isOpen_sUnion

/-- The Mathlib bridge preserves the predicate of being open definitionally.
@isnad1 id=iff.0h3v.s4.0c8d0aecf356 from=translated src=- shape=238e1b69 vocab=567e4788
-/
@[simp]
theorem isOpen_toMathlib (τ : TextbookTopology X) (s : Set X) :
    @_root_.IsOpen X τ.toMathlib s ↔ τ.IsOpen s :=
  Iff.rfl

/-- Textbook continuity is exactly Mathlib continuity after installing the two explicit bridges.
@isnad1 id=iff.0h5v.s4.a2fc76f6640a from=translated src=- shape=8773f0bb vocab=1509c5e8
-/
theorem continuous_iff_mathlib (τX : TextbookTopology X) (τY : TextbookTopology Y) (f : X → Y) :
    Continuous τX τY f ↔ @_root_.Continuous X Y τX.toMathlib τY.toMathlib f := by
  rw [_root_.continuous_def]
  rfl

end SandronesLibrary.Topology.TextbookTopology
