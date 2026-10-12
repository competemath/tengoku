/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
module

public import Tengoku
import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.Surface.Bridges

/-!
# Identity theorem, isolated fibers, open mapping, surjectivity

Unit: surfaces-and-charts (`docs/design/surfaces-and-charts.md` §3.4; Forster 1.11, 2.4, 2.7).

For holomorphic maps between Riemann surfaces:

* `map_extChartAt_nhdsNE`, `nhdsNE_neBot`: punctured-neighborhood transport through charts;
* `eventually_eq_or_eventually_ne`: local dichotomy for a pair of maps agreeing at a point;
  `eventually_eq_const_or_eventually_ne`: locally constant value or isolated in its fiber;
* `eq_of_frequently_eq`: the **identity theorem** on a connected surface;
  `eq_of_eqOn_of_accPt`: accumulation-set formulation (consumed by meromorphic-and-divisors);
* `eventually_ne_of_not_const`: nonconstant holomorphic maps have **isolated fibers**;
* `isOpenMap_of_not_const`: nonconstant holomorphic maps are **open** (Forster 2.4);
* `surjective_of_not_const`: nonconstant + compact source + connected target ⇒ surjective
  (Forster 2.7; consumed by mapping-degree and the headline).
-/

@[expose] public section

open scoped ContDiff Manifold
open Set Filter Topology IsManifold

namespace RS

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

/-! ### Punctured-neighborhood transport through charts -/

/-! ### The local dichotomy -/

/-! ### The identity theorem -/

variable [T2Space Y]   -- ℂ qualifies, so all lemmas below apply to `f g : X → ℂ`

/-! ### Isolated fibers, open mapping, surjectivity -/

end RS
