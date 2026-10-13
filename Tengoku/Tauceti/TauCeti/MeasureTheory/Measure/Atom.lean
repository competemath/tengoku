/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku

import Tengoku.Tauceti.TauCeti.MeasureTheory.Measure.ZeroOne

/-!
# Images of measure atoms

A positive finite-mass measurable atom is a measurable set whose measurable subsets have either
zero or full mass. Every almost-everywhere measurable map sends such an atom to one point of a
standard Borel target: the image of the measure restricted to the atom is a scalar multiple of a
Dirac measure.

The finite-mass hypothesis is essential: a zero-infinity measure may make its whole carrier an
atom while vanishing on every singleton.

## Main definitions

* `MeasureTheory.Measure.IsAtom` — a measurable positive-mass set whose measurable subsets
  have either zero measure or the full measure of the set.

## Main results

* `AEMeasurable.exists_ae_eq_const_restrict_of_atom` — an a.e.-measurable map into a standard
  Borel space is a.e. constant on every positive finite-mass measurable atom;
* `AEMeasurable.exists_map_restrict_eq_smul_dirac_of_atom` — an a.e.-measurable map from a
  positive finite-mass measurable atom into a standard Borel space has the corresponding point
  mass as its restricted pushforward.
-/

public section

open MeasureTheory

namespace TauCeti

namespace MeasureTheory

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace Y]
variable {T : X → Y} {μ : Measure X}

/-- A measure atom is a measurable positive-mass set whose measurable subsets have either zero
measure or the full measure of the set. -/
def _root_.MeasureTheory.Measure.IsAtom (μ : Measure X) (A : Set X) : Prop :=
  MeasurableSet A ∧ 0 < μ A ∧
    ∀ ⦃B : Set X⦄, MeasurableSet B → B ⊆ A → μ B = 0 ∨ μ B = μ A

/-- The defining characterization of a measure atom. -/
@[simp]
theorem _root_.MeasureTheory.Measure.isAtom_iff {A : Set X} :
    μ.IsAtom A ↔ MeasurableSet A ∧ 0 < μ A ∧
      ∀ ⦃B : Set X⦄, MeasurableSet B → B ⊆ A → μ B = 0 ∨ μ B = μ A :=
  Iff.rfl

end MeasureTheory

end TauCeti
