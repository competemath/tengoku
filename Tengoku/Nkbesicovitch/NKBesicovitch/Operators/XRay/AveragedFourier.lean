/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Operators.XRay.FourierFrame
public import Tengoku.Nkbesicovitch.NKBesicovitch.Geometry.RotatedHyperplaneIntegral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Averaged Fourier decay of the signed X-ray transform

Fiberwise Plancherel and polar averaging give the exact inverse-radius
Fourier weight, with the ratio of sphere areas as normalization. A gap of
radius `R > 0` in the Fourier support therefore gives an `R⁻¹` gain for the
squared norm, or `R⁻¹ᐟ²` for the joint direction-displacement `L²` norm.
-/

public section

open MeasureTheory Submodule Set Metric
open scoped SchwartzMap FourierTransform ENNReal NNReal

namespace NKBesicovitch.XRay

variable {m : ℕ} [Nonempty (Fin m)]
  (v : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
  (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ (v : EuclideanSpace ℝ (Fin (m + 1))))ᗮ)

end NKBesicovitch.XRay
