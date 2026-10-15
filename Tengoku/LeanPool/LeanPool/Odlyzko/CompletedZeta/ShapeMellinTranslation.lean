/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Tengoku.LeanPool.LeanPool.Odlyzko.CompletedZeta.FractionalShapeTheta
public import Tengoku.LeanPool.LeanPool.Odlyzko.CompletedZeta.UnitSlabTranslation

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Complex MeasureTheory NumberField NumberField.InfinitePlace NumberField.Units
  dirichletUnitTheorem
open scoped nonZeroDivisors

namespace NumberField.Odlyzko

open mixedEmbedding mixedEmbedding.fundamentalCone

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

open Classical in
/-- A logarithmic mellin weight used in the Odlyzko-bound argument. -/
noncomputable def logarithmicMellinWeight
    (s : ℂ) (y : mixedEmbedding.realSpace K) : ℂ :=
  Complex.exp
    (((y w₀ * (Module.finrank ℚ K : ℝ) : ℝ) : ℂ) * s)

omit [IsTotallyComplex K] in
open Classical in
/--
@isnad1 id=eq.0h3v.s6.aaae3fdca595 from=translated src=- shape=5d7705ab vocab=47d0d03f
-/
@[simp]
theorem logarithmicMellinWeight_apply
    (s : ℂ) (y : mixedEmbedding.realSpace K) :
    logarithmicMellinWeight K s y =
      Complex.exp
        (((y w₀ * (Module.finrank ℚ K : ℝ) : ℝ) : ℂ) * s) :=
  rfl

omit [IsTotallyComplex K] in
open Classical in
/--
@isnad1 id=eq.0h4v.s7.6ea1ad1269f8 from=translated src=- shape=d1363c8b vocab=cc1dcc39
-/
theorem logarithmicMellinWeight_vadd_unitCoordinateLattice
    (s : ℂ) (g : unitCoordinateLattice (K := K))
    (y : mixedEmbedding.realSpace K) :
    logarithmicMellinWeight K s
        ((g : mixedEmbedding.realSpace K) + y) =
      logarithmicMellinWeight K s y := by
  rw [logarithmicMellinWeight]
  simp only [Pi.add_apply, unitCoordinateLattice_apply_w₀, zero_add]
  simp

omit [IsTotallyComplex K] in
open Classical in
/--
@isnad1 id=eq.0h4v.s6.65238263565e from=translated src=- shape=093b1cc6 vocab=83bf3caa
-/
theorem logarithmicMellinWeight_add
    (s : ℂ) (y a : mixedEmbedding.realSpace K) :
    logarithmicMellinWeight K s (y + a) =
      logarithmicMellinWeight K s a *
        logarithmicMellinWeight K s y := by
  rw [logarithmicMellinWeight, logarithmicMellinWeight,
    logarithmicMellinWeight, ← Complex.exp_add]
  simp only [Pi.add_apply]
  push_cast
  ring_nf

end NumberField.Odlyzko
