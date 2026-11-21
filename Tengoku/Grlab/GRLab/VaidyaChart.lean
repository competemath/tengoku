/-
Copyright (c) 2026 Brandon Yates. All rights reserved.
Released under Apache 2.0 license.
-/
import Tengoku.Grlab.GRLab.SSRicci

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The ingoing Vaidya chart

Coordinates are `x 0 = v`, `x 1 = r`, `x 2 = θ`, `x 3 = φ`, and the metric is

  `ds² = −(1 − 2m(v)/r) dv² + 2 dv dr + r² dθ² + r² sin²θ dφ²`,

the ingoing Eddington–Finkelstein form of the Vaidya radiating solution, for an
**arbitrary** differentiable mass function `m : ℝ → ℝ`.  Unlike everything else in `GRLab`
so far this metric is *not* static and *not* diagonal, so it cannot be routed through
`GRLab.ssMetric`; it is built directly on the general 4D definitions in `GRLab.Curvature`.

This file fixes the definitional surface: the metric, its inverse, the Christoffel table
and the partial-derivative tables.  `GRLab/VaidyaGamma.lean` proves the tables and
`GRLab/Vaidya.lean` assembles the Ricci tensor.

## Why `m` and `m₁` are carried as separate atoms

Exactly as `GRLab.SSRicci` carries `f, f₁, f₂`: with `m (x 0)` and `m₁ (x 0)` opaque to
`ring` and `field_simp`, the 4×4×4 Christoffel expansion never turns into
rational-function normalisation.

## Why there is no full `∂_v Γ` table

`GRLab.ricci` expands to `∑_a [∂_a Γ^a_{db} − ∂_d Γ^a_{ab} + (quadratic)]`, so the only
`v`-partials it ever asks for are `∂_v Γ^v_{cd}` (the `a = v` **row**) and `∂_v Γ^a_{ab}`
(the **trace**).  Neither contains `m′`, so neither needs `m″`.  The one entry of the full
`∂_v` table that *would* need `m″` is

  `∂_v Γ^r_{vv} = (r² m″ + r m′ − 4 m m′)/r³`,

and it is never reached.  Splitting the `v`-table into row + trace is therefore what lets
this development assume only that `m` is **once** differentiable, which is the honest
hypothesis for the Vaidya solution.  (Verified by the symbolic oracle: see
`README.md`.)

## Sign conventions

Signature `(−,+,+,+)`, `G = c = 1`, `∂_v` and `∂_r` as in `GRLab.pderiv`.  With these,
`R_{μν} = (2 m′(v)/r²) δ^v_μ δ^v_ν`: **increasing** mass (`m′ > 0`) is ingoing radiation
with positive energy density, which is the standard orientation for the *ingoing* chart.
-/

namespace GRLab

open Matrix Filter Topology

/-! ## The metric -/

/-- **The ingoing Vaidya metric** `diag`-free form
`[[−(1 − 2m/r), 1, 0, 0], [1, 0, 0, 0], [0, 0, r², 0], [0, 0, 0, r² sin²θ]]`
in coordinates `(v, r, θ, φ)`.-/
noncomputable def vaidyaMetric (m : ℝ → ℝ) : MetricFn 4 := fun x =>
  Matrix.of ![![-(1 - 2 * m (x 0) / x 1), 1, 0, 0],
              ![1, 0, 0, 0],
              ![0, 0, (x 1) ^ 2, 0],
              ![0, 0, 0, (x 1) ^ 2 * Real.sin (x 2) ^ 2]]

/-- The inverse Vaidya metric `[[0, 1, 0, 0], [1, 1 − 2m/r, 0, 0], [0, 0, r⁻², 0],
[0, 0, 0, (r² sin²θ)⁻¹]]`.  Note `g^{vv} = 0` and `g^{rr} = 1 − 2m/r`: the *inverse*
carries the lapse, and no `f ≠ 0` hypothesis is needed anywhere — the ingoing chart is
regular across the horizon, which is the whole point of Eddington–Finkelstein coordinates.-/
noncomputable def vaidyaInv (m : ℝ → ℝ) (x : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of ![![0, 1, 0, 0],
              ![1, 1 - 2 * m (x 0) / x 1, 0, 0],
              ![0, 0, ((x 1) ^ 2)⁻¹, 0],
              ![0, 0, 0, ((x 1) ^ 2 * Real.sin (x 2) ^ 2)⁻¹]]

/-! ## The good region

The ingoing chart degenerates only where the *angular* part does: at `r = 0` and on the
polar axis.  There is **no horizon condition** — contrast `GRLab.ssGood`, which also
demands `f (y 1) ≠ 0`. -/

/-- The open region on which the Vaidya chart is a chart and the Christoffel table is
valid: `r ≠ 0`, `sin θ ≠ 0`, and `m` differentiable at `v`.-/
def vGood (m m₁ : ℝ → ℝ) : Set (Fin 4 → ℝ) :=
  {y | y 1 ≠ 0 ∧ Real.sin (y 2) ≠ 0 ∧ HasDerivAt m (m₁ (y 0)) (y 0)}

variable {m m₁ : ℝ → ℝ} {x : Fin 4 → ℝ}

/-! ## The tables

All of these were fixed by an independent sympy computation of `GRLab`'s exact index
formulas and cross-checked component-by-component against a separate computer-algebra curvature engine
(64/64 Christoffel symbols, 16/16 Ricci components, zero mismatches).  See
`README.md`. -/

/-- Table of metric partial derivatives, indexed `vDMetric m m₁ x b d c = ∂_b g_{dc}`.

Nonzero entries: `∂_v g_{vv} = 2m′/r`, `∂_r g_{vv} = −2m/r²`, `∂_r g_{θθ} = 2r`,
`∂_r g_{φφ} = 2r sin²θ`, `∂_θ g_{φφ} = 2r² sinθ cosθ`.-/
noncomputable def vDMetric (m m₁ : ℝ → ℝ) (x : Fin 4 → ℝ) : Fin 4 → Fin 4 → Fin 4 → ℝ :=
  ![ -- b = 0  (v)
     ![![2 * m₁ (x 0) / x 1, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
     -- b = 1  (r)
     ![![-(2 * m (x 0) / (x 1) ^ 2), 0, 0, 0],
       ![0, 0, 0, 0],
       ![0, 0, 2 * x 1, 0],
       ![0, 0, 0, 2 * x 1 * Real.sin (x 2) ^ 2]],
     -- b = 2  (θ)
     ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0],
       ![0, 0, 0, 2 * (x 1) ^ 2 * Real.sin (x 2) * Real.cos (x 2)]],
     -- b = 3  (φ)
     ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]]

/-- **The Christoffel table** for the ingoing Vaidya chart, indexed
`vGamma m m₁ x a b c = Γ^a_{bc}`.

Nonzero entries (all others are zero):

| symbol | value |
|---|---|
| `Γ^v_{vv}` | `m/r²` |
| `Γ^v_{θθ}` | `−r` |
| `Γ^v_{φφ}` | `−r sin²θ` |
| `Γ^r_{vv}` | `m′/r + m/r² − 2m²/r³` |
| `Γ^r_{vr} = Γ^r_{rv}` | `−m/r²` |
| `Γ^r_{θθ}` | `−r + 2m` |
| `Γ^r_{φφ}` | `(−r + 2m) sin²θ` |
| `Γ^θ_{rθ} = Γ^θ_{θr}` | `1/r` |
| `Γ^θ_{φφ}` | `−sinθ cosθ` |
| `Γ^φ_{rφ} = Γ^φ_{φr}` | `1/r` |
| `Γ^φ_{θφ} = Γ^φ_{φθ}` | `cosθ/sinθ` |

`Γ^r_{vv}` is the only entry containing `m′`; see the module docstring.-/
noncomputable def vGamma (m m₁ : ℝ → ℝ) (x : Fin 4 → ℝ) : Fin 4 → Fin 4 → Fin 4 → ℝ :=
  ![ -- a = 0  (v)
     ![![m (x 0) / (x 1) ^ 2, 0, 0, 0],
       ![0, 0, 0, 0],
       ![0, 0, -(x 1), 0],
       ![0, 0, 0, -(x 1 * Real.sin (x 2) ^ 2)]],
     -- a = 1  (r)
     ![![m₁ (x 0) / x 1 + m (x 0) / (x 1) ^ 2 - 2 * m (x 0) ^ 2 / (x 1) ^ 3,
         -(m (x 0) / (x 1) ^ 2), 0, 0],
       ![-(m (x 0) / (x 1) ^ 2), 0, 0, 0],
       ![0, 0, -(x 1) + 2 * m (x 0), 0],
       ![0, 0, 0, (-(x 1) + 2 * m (x 0)) * Real.sin (x 2) ^ 2]],
     -- a = 2  (θ)
     ![![0, 0, 0, 0],
       ![0, 0, 1 / x 1, 0],
       ![0, 1 / x 1, 0, 0],
       ![0, 0, 0, -(Real.sin (x 2) * Real.cos (x 2))]],
     -- a = 3  (φ)
     ![![0, 0, 0, 0],
       ![0, 0, 0, 1 / x 1],
       ![0, 0, 0, Real.cos (x 2) / Real.sin (x 2)],
       ![0, 1 / x 1, Real.cos (x 2) / Real.sin (x 2), 0]]]

/-- `∂_v Γ^v_{cd}` — the `a = v` **row** of the advanced-time table, indexed `[c][d]`.
Only `∂_v Γ^v_{vv} = m′/r²` is nonzero.-/
noncomputable def vDGammaV (m₁ : ℝ → ℝ) (x : Fin 4 → ℝ) : Fin 4 → Fin 4 → ℝ :=
  ![![m₁ (x 0) / (x 1) ^ 2, 0, 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

/-- `∂_v Γ^a_{ab}` — the **trace** of the advanced-time table, indexed `[a][b]`.
Only `∂_v Γ^v_{vv} = m′/r²` and `∂_v Γ^r_{rv} = −m′/r²` are nonzero; note they cancel,
which is the statement that `√|g| = r² sinθ` does not depend on `v`.-/
noncomputable def vDGammaVtr (m₁ : ℝ → ℝ) (x : Fin 4 → ℝ) : Fin 4 → Fin 4 → ℝ :=
  ![![m₁ (x 0) / (x 1) ^ 2, 0, 0, 0],
    ![-(m₁ (x 0) / (x 1) ^ 2), 0, 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

/-- `∂_r Γ^a_{cd}`, indexed `[a][c][d]`.-/
noncomputable def vDGammaR (m m₁ : ℝ → ℝ) (x : Fin 4 → ℝ) : Fin 4 → Fin 4 → Fin 4 → ℝ :=
  ![ -- a = 0  (v)
     ![![-(2 * m (x 0) / (x 1) ^ 3), 0, 0, 0],
       ![0, 0, 0, 0],
       ![0, 0, -1, 0],
       ![0, 0, 0, -(Real.sin (x 2) ^ 2)]],
     -- a = 1  (r)
     ![![-(m₁ (x 0) / (x 1) ^ 2) - 2 * m (x 0) / (x 1) ^ 3 + 6 * m (x 0) ^ 2 / (x 1) ^ 4,
         2 * m (x 0) / (x 1) ^ 3, 0, 0],
       ![2 * m (x 0) / (x 1) ^ 3, 0, 0, 0],
       ![0, 0, -1, 0],
       ![0, 0, 0, -(Real.sin (x 2) ^ 2)]],
     -- a = 2  (θ)
     ![![0, 0, 0, 0],
       ![0, 0, -(1 / (x 1) ^ 2), 0],
       ![0, -(1 / (x 1) ^ 2), 0, 0],
       ![0, 0, 0, 0]],
     -- a = 3  (φ)
     ![![0, 0, 0, 0],
       ![0, 0, 0, -(1 / (x 1) ^ 2)],
       ![0, 0, 0, 0],
       ![0, -(1 / (x 1) ^ 2), 0, 0]]]

/-- `∂_θ Γ^a_{cd}`, indexed `[a][c][d]`.-/
noncomputable def vDGammaT (m : ℝ → ℝ) (x : Fin 4 → ℝ) : Fin 4 → Fin 4 → Fin 4 → ℝ :=
  ![ -- a = 0  (v)
     ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0],
       ![0, 0, 0, -(2 * x 1 * Real.sin (x 2) * Real.cos (x 2))]],
     -- a = 1  (r)
     ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0],
       ![0, 0, 0, 2 * (-(x 1) + 2 * m (x 0)) * Real.sin (x 2) * Real.cos (x 2)]],
     -- a = 2  (θ)
     ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0],
       ![0, 0, 0, Real.sin (x 2) ^ 2 - Real.cos (x 2) ^ 2]],
     -- a = 3  (φ)
     ![![0, 0, 0, 0],
       ![0, 0, 0, 0],
       ![0, 0, 0, -(1 / Real.sin (x 2) ^ 2)],
       ![0, 0, -(1 / Real.sin (x 2) ^ 2), 0]]]

/-- **The Ricci tensor of the ingoing Vaidya metric**, indexed `[b][d]`.
Rank one and null: `R_{μν} = (2 m′(v)/r²) δ^v_μ δ^v_ν`.-/
noncomputable def vRicci (m₁ : ℝ → ℝ) (x : Fin 4 → ℝ) : Fin 4 → Fin 4 → ℝ :=
  ![![2 * m₁ (x 0) / (x 1) ^ 2, 0, 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

end GRLab
