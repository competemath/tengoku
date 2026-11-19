/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Induction.Estimates
public import Tengoku.Nkbesicovitch.NKBesicovitch.Operators.PlateLocalization
public import Tengoku.Nkbesicovitch.NKBesicovitch.Operators.PlateTranslation
public import Tengoku.Nkbesicovitch.NKBesicovitch.Operators.BallLocalization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Extending local plate estimates to arbitrary inputs

Translation invariance applies the centered local estimate to every
moving radius-three ball. Averaging over their centers costs the ratio
of the radius-three and radius-one ball volumes, namely `3^n`, at the
level of the `p`th power. Thus the global bound has the same thickness
deficit and an extra norm factor `3^(n/p)`, uniformly for `0 < δ ≤ 1`.
-/

public section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace NKBesicovitch.Induction

variable {n k : ℕ} {δ : ℝ} {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞}

end NKBesicovitch.Induction
