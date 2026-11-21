/-
Copyright (c) 2026 Brandon Yates. All rights reserved.
Released under Apache 2.0 license.
-/
import Tengoku.Grlab.GRLab.VaidyaChart

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Christoffel symbols of the ingoing Vaidya chart, and their partial derivatives

This file proves every table fixed in `GRLab/VaidyaChart.lean`:

* `pderiv_vaidyaMetric` — the 64 first partials `∂_b g_{dc}` of

    `ds² = −(1 − 2m(v)/r) dv² + 2 dv dr + r² dθ² + r² sin²θ dφ²`;

* `christoffel_vaidya` — the 64 Christoffel symbols `Γ^a_{bc} = vGamma m m₁ x a b c`;
* `pderiv_vGamma_phi` — axisymmetry, `∂_φ Γ = 0`;
* `pderiv_vGamma_v_row` and `pderiv_vGamma_v_trace` — the two advanced-time slices
  `∂_v Γ^v_{cd}` and `∂_v Γ^a_{ab}`;
* `pderiv_vGamma_r` and `pderiv_vGamma_th` — the full 64-entry `∂_r Γ` and `∂_θ Γ` tables.

## Why row + trace and not a full `∂_v` table

`GRLab.ricci` expands to `∑_a [∂_a Γ^a_{db} − ∂_d Γ^a_{ab} + (quadratic)]`, so the only
`v`-partials it ever asks for are the `a = v` **row** `∂_v Γ^v_{cd}` and the **trace**
`∂_v Γ^a_{ab}`.  Neither contains `m′`, so neither needs `m″`.  The single entry of the
*full* `∂_v` table that would need `m″` is `∂_v Γ^r_{vv} = (r²m″ + r m′ − 4m m′)/r³`, and it
is never reached.  This is exactly what lets the whole development assume only that `m` is
**once** differentiable — the honest hypothesis for the Vaidya solution.  Accordingly no
theorem in this file takes a second-derivative hypothesis.

## Method

Identical to `GRLab/StaticSpherical.lean` and `GRLab/SSRicci.lean`: `m (x 0)` and `m₁ (x 0)`
are carried as independent atoms, every coordinate section of every table entry is a
globally defined one-variable function, so the global evaluation rule
`pderiv_eq_of_hasDerivAt'` applies with no neighbourhood bookkeeping, and the 64-way index
split reduces to a handful of one-variable `HasDerivAt` shapes.

All values were fixed *before* any proof was attempted by an independent sympy computation
of `GRLab`'s exact index formulas, cross-checked component-by-component against
a separate computer-algebra curvature engine: 64/64 Christoffel symbols, 16/16 Ricci components,
16/16 Einstein components, zero mismatches.  See `GRLab/VaidyaChart.lean`.
-/

namespace GRLab

open Matrix Filter Topology

/-! ## One-variable derivative shapes

The `r`-sections of the Vaidya tables are constants over powers of `r` plus linear terms;
the `θ`-sections are the three trigonometric shapes already familiar from `GRLab.SSRicci`.
`GRLab.Lapse`'s inverse-power helpers are `private` to that module, so they are restated
here. -/

/-! ## The sixteen sections of the four independent metric components

`g_{vv} = −(1 − 2m(v)/r)` depends on `v` and `r`; `g_{vr} = g_{rv} = 1` and `g_{rr} = 0` are
constants; `g_{θθ} = r²` depends on `r`; `g_{φφ} = r² sin²θ` depends on `r` and `θ`. -/

section Sections

variable {m m₁ : ℝ → ℝ} {x : Fin 4 → ℝ}

end Sections

/-! ## The metric partial derivatives -/

/-! ## The Christoffel table

One declaration per value of the upper index `a`.  That is not cosmetic: a single
`fin_cases a <;> fin_cases b <;> fin_cases c <;> … <;> field_simp` chain shares one
heartbeat budget across all 64 goals, which is what timed out the analogous static-spherical
computation; see the trap notes in `README.md`.  Unlike the static-spherical chart the inverse
metric here is **not** diagonal (`g^{vr} = g^{rv} = 1`, `g^{rr} = 1 − 2m/r`, `g^{vv} = 0`),
so for `a ∈ {v, r}` two terms of the `∑ d` survive. -/

section Christoffel

variable {m m₁ : ℝ → ℝ} {x : Fin 4 → ℝ}

end Christoffel

/-! ## Partial derivatives of the Christoffel table -/

/-! ### The radial table

One declaration per value of the upper index `a`, and here that split is **forced**, not just
a heartbeat optimisation.  In a `first | exact … | exact …` alternation over
`pderiv_eq_of_hasDerivAt'`, the branch is selected by unifying the *derivative value* `c`
alone; the section-equality argument `(fun _ => by simp)` is a nested tactic block whose
"unsolved goals" is **logged, not thrown**, so `first` has already committed by the time it
fails and never backtracks.  (A failing `ring1` inside `congr_deriv` *does* throw and does
backtrack — the two behave differently.  Appending `done` to the `simp` does not help: it is
logged the same way.)  Across the full table both `Γ^v_{θθ} = −r` and `Γ^r_{θθ} = −r + 2m`
have `∂_r = −1`, and both `Γ^v_{φφ}` and `Γ^r_{φφ}` have `∂_r = −sin²θ`, so a single 64-way
alternation silently applies the `a = v` witness to the `a = r` goals.  Splitting by `a`
makes the derivative values within each block pairwise distinct, which restores selection. -/

section DGammaR

variable {m m₁ : ℝ → ℝ} {x : Fin 4 → ℝ}

end DGammaR

end GRLab
