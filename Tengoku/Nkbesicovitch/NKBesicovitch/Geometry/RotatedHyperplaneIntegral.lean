/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Geometry.PolarIntegral
public import Tengoku.Nkbesicovitch.NKBesicovitch.Geometry.SphereMeasure

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Averaging integrals over rotated hyperplanes

Polar coordinates in a hyperplane have one fewer radial power than in the
ambient space. Haar averaging makes the angular distribution uniform, so
the averaged hyperplane integral equals an ambient integral with weight
`‖x‖⁻¹` and the ratio of the two sphere areas. Positive hyperplane dimension
excludes the exceptional zero-dimensional fiber, whose volume has an atom.
-/

public section

open MeasureTheory Set Metric
open scoped ENNReal

namespace NKBesicovitch

variable {m : ℕ} [Nonempty (Fin m)] {f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ≥0∞}

end NKBesicovitch
