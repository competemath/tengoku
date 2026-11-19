/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Induction.Estimates
public import Tengoku.Nkbesicovitch.NKBesicovitch.Induction.DiagonalStep
public import Tengoku.Nkbesicovitch.NKBesicovitch.Induction.XRayExponents

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Reducing the plate deficit by a prescribed subcritical ratio

The diagonal step divides the dimension deficit by `ρ`. The available
X-ray exponent scale can always accommodate the preceding input exponent,
so this operation can be repeated any finite number of times.
-/

public section

open MeasureTheory Set Metric NKBesicovitch.Grassmannian NKBesicovitch.XRay
open scoped ENNReal NNReal

namespace NKBesicovitch.Induction

variable {n m k : ℕ} (v : sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
    (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ (v : EuclideanSpace ℝ (Fin n)))ᗮ)

end NKBesicovitch.Induction
