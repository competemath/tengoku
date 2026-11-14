/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tengoku.Leanmodularforms.LeanModularForms.ForMathlib.PiecewiseC1Path
import Tengoku

/-!
# Curve Utilities and Avoidance

Utility lemmas for working with `PiecewiseC1Path` partition structure and curve avoidance.

## Main definitions

* `PiecewiseC1Path.infDist` — infimum distance from `z₀` to the path image on `[0, 1]`.
-/
namespace Tengoku.Leanmodularforms end Tengoku.Leanmodularforms open Tengoku.Leanmodularforms
open Set Complex Metric

noncomputable section

variable {x y : ℂ}

namespace Tengoku.Leanmodularforms.PiecewiseC1Path

/-- Infimum distance from `z₀` to the path image on `[0, 1]`. -/
noncomputable def infDist (γ : PiecewiseC1Path x y) (z₀ : ℂ) : ℝ :=
  Metric.infDist z₀ (γ.toPath.extend '' Icc 0 1)

end Tengoku.Leanmodularforms.PiecewiseC1Path

end
-- Tengoku: root names of this library moved to Tengoku.Leanmodularforms so they do not collide with other libraries (generated)
