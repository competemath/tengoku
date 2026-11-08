module

public import Tengoku.Seed.MeasureTheory.Integral.CurveIntegral.Basic
public import Tengoku.Seed.MeasureTheory.Measure.Prod
public import Tengoku.Seed.MeasureTheory.Measure.Restrict

public import Tengoku.SpherePackingExt.SpherePacking.ForMathlib.ScalarOneForm

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Convenience measures on standard intervals

This file defines repo-local convenience measures on standard intervals, used pervasively in the
sphere packing development (but too specialized for Mathlib).
-/

namespace SpherePacking.Integration

noncomputable section

open scoped Interval
open MeasureTheory Set intervalIntegral
open MagicFunction

/-- The restriction of Lebesgue measure to `Ioc (0, 1]`.-/
@[expose] public def μIoc01 : Measure ℝ :=
  (volume : Measure ℝ).restrict (Ioc (0 : ℝ) 1)

/-- The restriction of Lebesgue measure to `Ioo (0, 1)`.-/
@[expose] public def μIoo01 : Measure ℝ :=
  (volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)

attribute [irreducible] μIoo01

/-- The restriction of Lebesgue measure to `Ici 1`.-/
@[expose] public def μIciOne : Measure ℝ :=
  (volume : Measure ℝ).restrict (Ici (1 : ℝ))

/-! `μIciOne` is `SFinite`. -/

/-- The restriction of Lebesgue measure to `Ioi 0`.-/
@[expose] public def μIoi0 : Measure ℝ :=
  (volume : Measure ℝ).restrict (Ioi (0 : ℝ))

/-!
#### `μIoo01` helper lemmas

These are small, reusable facts for the frequently used measure `μIoo01`.
-/

/-!
#### `μIoc01` helper lemmas

We keep the segment/interval-integral conversion lemma here because most downstream uses of
`μIoc01` are in curve-integral arguments.
-/

end

end SpherePacking.Integration
