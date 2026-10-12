/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Tengoku.LeanPool.LeanPool.Odlyzko.CompletedZeta.ClassThetaCenteredContinuation
public import Tengoku

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Complex Ideal MeasureTheory NumberField NumberField.InfinitePlace NumberField.Units
  NumberField.Units.dirichletUnitTheorem
open scoped nonZeroDivisors

namespace NumberField.Odlyzko

open mixedEmbedding mixedEmbedding.fundamentalCone

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

open Classical in
/-- A centered numerator translation used in the Odlyzko-bound argument. -/
noncomputable def centeredNumeratorTranslation
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    mixedEmbedding.realSpace K :=
  radialLogVector K (fractionalShapeCovolumeCenter K I) -
    denominatorLogCoordinates K I -
    radialLogVector K
      (fractionalShapeCovolumeCenter K
        (FractionalIdeal.mk0 K (fractionalIdealNumerator K I)))

omit [IsTotallyComplex K] in
open Classical in
theorem centeredFractionalShapeCoordinates_numerator
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (y : mixedEmbedding.realSpace K) :
    centeredFractionalShapeCoordinates K
        (FractionalIdeal.mk0 K (fractionalIdealNumerator K I))
        (y + centeredNumeratorTranslation K I) =
      centeredFractionalShapeCoordinates K I y -
        denominatorLogCoordinates K I := by
  rw [centeredFractionalShapeCoordinates,
    centeredFractionalShapeCoordinates,
    centeredNumeratorTranslation]
  grind

end NumberField.Odlyzko
