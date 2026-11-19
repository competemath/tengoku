/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Grassmannian.Measure
public import Tengoku.Nkbesicovitch.NKBesicovitch.Operators.Defs
public import Tengoku.Seed.MeasureTheory.Function.LpSeminorm.Defs
public import Tengoku.Seed.Analysis.SpecialFunctions.Pow.NNReal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Local diagonal plate estimates and their dimension deficit

The estimate is uniform over positive thicknesses and Borel nonnegative
inputs supported in any fixed centered ball. The factor `δ^(-α/p)` records
the dimension deficit `α`. Applications require a finite real `p ≥ 1`.
Using positive nonnegative-real thicknesses keeps every coefficient finite.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace NKBesicovitch.Induction

end NKBesicovitch.Induction
