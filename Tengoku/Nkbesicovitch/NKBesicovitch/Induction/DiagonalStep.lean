/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Induction.Step
public import Tengoku.Nkbesicovitch.NKBesicovitch.Operators.PlateMeasurability
public import Tengoku.Nkbesicovitch.NKBesicovitch.Operators.PlatePower

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Matching diagonal plate estimates to the X-ray exponents

Increase a lower-dimensional diagonal estimate from exponent `a` to `t*a`,
then decrease its output exponent on the probability direction space.
The flag argument applies the X-ray estimate and gives another diagonal
estimate. The previous constant becomes its `1/t` power, which is the
required reduction of the thickness loss.
-/

public section

open MeasureTheory Set Metric NKBesicovitch.Grassmannian NKBesicovitch.XRay
open scoped ENNReal NNReal

namespace NKBesicovitch.Induction

variable {n m k : ℕ} (v : sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
    (b : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] (ℝ ∙ (v : EuclideanSpace ℝ (Fin n)))ᗮ)

end NKBesicovitch.Induction
