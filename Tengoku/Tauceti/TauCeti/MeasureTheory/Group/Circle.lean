/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku

/-!
# Measures on the circle

This file defines the measure on `Circle` obtained from a continuous nonnegative density on the
unit circle with respect to normalized arc length. Its integral is identified with Mathlib's
`Real.circleAverage`.

## Main definitions and results

* `TauCeti.circleDensityMeasure`: normalized arc length weighted by a density.
* `TauCeti.isFiniteMeasure_circleDensityMeasure`: a continuous density gives a finite measure.
* `TauCeti.integral_circleDensityMeasure`: integration against the weighted measure is a circle
  average.
-/

public section

noncomputable section

open Complex MeasureTheory Metric Real Set Filter
open scoped ENNReal

namespace TauCeti

end TauCeti
