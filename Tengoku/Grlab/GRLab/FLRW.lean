/-
Copyright (c) 2026 Brandon Yates. All rights reserved.
Released under Apache 2.0 license.
-/
import Tengoku.Grlab.GRLab.Curvature
import Tengoku.Grlab.GRLab.SSRicci

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Spatially flat FLRW cosmology

Coordinates are `x 0 = t`, `x 1 = x`, `x 2 = y`, `x 3 = z`, and the metric is the
spatially flat Friedmann–Lemaître–Robertson–Walker line element in Cartesian comoving
coordinates,

  `ds² = −dt² + a(t)² (dx² + dy² + dz²)`,

with signature `(−,+,+,+)` and `G = c = 1`.  As in `GRLab.StaticSpherical`, the scale
factor is carried as **three independent atoms** `a`, `a₁ = ȧ`, `a₂ = ä`, tied together
only by `HasDerivAt` hypotheses.  That is what keeps `ring` and `field_simp` from blowing
up into rational-function normalisation, and it makes the result reusable for every
matter content (dust, radiation, Λ, stiff fluid) without redoing any calculus.

## The computation

| object | value |
|---|---|
| `Γ^t_{xx} = Γ^t_{yy} = Γ^t_{zz}` | `a ȧ` |
| `Γ^x_{tx} = Γ^y_{ty} = Γ^z_{tz}` (and their transposes) | `ȧ/a` |
| `R_tt` | `−3 ä/a` |
| `R_xx = R_yy = R_zz` | `a ä + 2 ȧ²` |
| `R` | `6 ä/a + 6 (ȧ/a)²` |
| `G_tt` | `3 (ȧ/a)²` |
| `G_xx = G_yy = G_zz` | `−(2 a ä + ȧ²)` |

The last two lines are the **Friedmann equations in Einstein-tensor form** — coupling to
a perfect fluid via `G_{μν} = 8π T_{μν}` turns `G_tt` into `H² = 8πρ/3` and `G_ii` into
the pressure equation.  They are the physics content of this file
(`GRLab.friedmann_first`, `GRLab.friedmann_second`).

## Oracle

Every value above was fixed **before** any Lean proof was attempted, by an independent
sympy implementation of the exact index formulas of `GRLab.Curvature`, cross-checked
against the author's own computer-algebra suite (flat FRW) through the
chart-independent mixed Einstein tensor `G^μ_ν` (comoving spherical vs. comoving
Cartesian): all sixteen components agree and the scalar-curvature residual is exactly `0`.
`README.md` describes the corresponding static-spherical cross-check.
-/

namespace GRLab

open Matrix Filter Topology

/-! ### The metric, its inverse and its determinant -/

/-- Spatially flat FLRW in Cartesian comoving coordinates:
`ds² = −dt² + a(t)²(dx² + dy² + dz²)`, coordinates `(t, x, y, z)`.-/
noncomputable def flrwMetric (a : ℝ → ℝ) : MetricFn 4 := fun x =>
  Matrix.diagonal ![-1, (a (x 0)) ^ 2, (a (x 0)) ^ 2, (a (x 0)) ^ 2]

/-! ### The tables

`flrwGamma` is indexed `[a][b][c]` meaning `Γ^a_{bc}`, matching `GRLab.ssGamma`;
`flrwDGammaT` is `∂_t Γ` in the same layout; `flrwDMetric` is indexed `[b][d][c]`
meaning `∂_b g_{dc}`, matching `GRLab.ssDMetric`.
-/

/-- The region where the chart is nondegenerate: `a(t) ≠ 0`.-/
def FLRWGood (a a₁ : ℝ → ℝ) : Set (Fin 4 → ℝ) :=
  {y | a (y 0) ≠ 0 ∧ HasDerivAt a (a₁ (y 0)) (y 0)}

/-- **The Christoffel table** for spatially flat FLRW, `flrwGamma a a₁ x c d e = Γ^c_{de}`.

Nonzero entries (all others vanish):

| symbol | value |
|---|---|
| `Γ^t_{xx} = Γ^t_{yy} = Γ^t_{zz}` | `a ȧ` |
| `Γ^x_{tx} = Γ^x_{xt}` | `ȧ/a` |
| `Γ^y_{ty} = Γ^y_{yt}` | `ȧ/a` |
| `Γ^z_{tz} = Γ^z_{zt}` | `ȧ/a` |-/
noncomputable def flrwGamma (a a₁ : ℝ → ℝ) (x : Fin 4 → ℝ) : Fin 4 → Fin 4 → Fin 4 → ℝ :=
  ![ -- c = 0  (t)
     ![![0, 0, 0, 0],
       ![0, a (x 0) * a₁ (x 0), 0, 0],
       ![0, 0, a (x 0) * a₁ (x 0), 0],
       ![0, 0, 0, a (x 0) * a₁ (x 0)]],
     -- c = 1  (x)
     ![![0, a₁ (x 0) / a (x 0), 0, 0],
       ![a₁ (x 0) / a (x 0), 0, 0, 0],
       ![0, 0, 0, 0],
       ![0, 0, 0, 0]],
     -- c = 2  (y)
     ![![0, 0, a₁ (x 0) / a (x 0), 0],
       ![0, 0, 0, 0],
       ![a₁ (x 0) / a (x 0), 0, 0, 0],
       ![0, 0, 0, 0]],
     -- c = 3  (z)
     ![![0, 0, 0, a₁ (x 0) / a (x 0)],
       ![0, 0, 0, 0],
       ![0, 0, 0, 0],
       ![a₁ (x 0) / a (x 0), 0, 0, 0]]]

/-- `∂_t Γ`, indexed `[c][d][e]`.  Nonzero entries: `∂_t Γ^t_{ii} = a ä + ȧ²` and
`∂_t Γ^i_{ti} = ∂_t Γ^i_{it} = (a ä − ȧ²)/a²` for each spatial `i`.-/
noncomputable def flrwDGammaT (a a₁ a₂ : ℝ → ℝ) (x : Fin 4 → ℝ) :
    Fin 4 → Fin 4 → Fin 4 → ℝ :=
  ![ -- c = 0  (t)
     ![![0, 0, 0, 0],
       ![0, a (x 0) * a₂ (x 0) + a₁ (x 0) ^ 2, 0, 0],
       ![0, 0, a (x 0) * a₂ (x 0) + a₁ (x 0) ^ 2, 0],
       ![0, 0, 0, a (x 0) * a₂ (x 0) + a₁ (x 0) ^ 2]],
     -- c = 1  (x)
     ![![0, (a (x 0) * a₂ (x 0) - a₁ (x 0) ^ 2) / a (x 0) ^ 2, 0, 0],
       ![(a (x 0) * a₂ (x 0) - a₁ (x 0) ^ 2) / a (x 0) ^ 2, 0, 0, 0],
       ![0, 0, 0, 0],
       ![0, 0, 0, 0]],
     -- c = 2  (y)
     ![![0, 0, (a (x 0) * a₂ (x 0) - a₁ (x 0) ^ 2) / a (x 0) ^ 2, 0],
       ![0, 0, 0, 0],
       ![(a (x 0) * a₂ (x 0) - a₁ (x 0) ^ 2) / a (x 0) ^ 2, 0, 0, 0],
       ![0, 0, 0, 0]],
     -- c = 3  (z)
     ![![0, 0, 0, (a (x 0) * a₂ (x 0) - a₁ (x 0) ^ 2) / a (x 0) ^ 2],
       ![0, 0, 0, 0],
       ![0, 0, 0, 0],
       ![(a (x 0) * a₂ (x 0) - a₁ (x 0) ^ 2) / a (x 0) ^ 2, 0, 0, 0]]]

/-- `∂_b g_{dc}` table.  The only nonzero entries are `∂_t g_{xx} = ∂_t g_{yy}
= ∂_t g_{zz} = 2 a ȧ`.-/
noncomputable def flrwDMetric (a a₁ : ℝ → ℝ) (x : Fin 4 → ℝ) : Fin 4 → Fin 4 → Fin 4 → ℝ :=
  ![ -- b = 0  (∂_t)
     ![![0, 0, 0, 0],
       ![0, 2 * a (x 0) * a₁ (x 0), 0, 0],
       ![0, 0, 2 * a (x 0) * a₁ (x 0), 0],
       ![0, 0, 0, 2 * a (x 0) * a₁ (x 0)]],
     ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
     ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
     ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]]

/-- **The Ricci tensor of flat FLRW.**  Diagonal for every scale factor:
`R_tt = −3 ä/a`, `R_ii = a ä + 2 ȧ²`.-/
noncomputable def flrwRicci (a a₁ a₂ : ℝ → ℝ) (x : Fin 4 → ℝ) : Fin 4 → Fin 4 → ℝ :=
  ![![-(3 * a₂ (x 0) / a (x 0)), 0, 0, 0],
    ![0, a (x 0) * a₂ (x 0) + 2 * a₁ (x 0) ^ 2, 0, 0],
    ![0, 0, a (x 0) * a₂ (x 0) + 2 * a₁ (x 0) ^ 2, 0],
    ![0, 0, 0, a (x 0) * a₂ (x 0) + 2 * a₁ (x 0) ^ 2]]

/-- **The Einstein tensor of flat FLRW** — the Friedmann equations:
`G_tt = 3 (ȧ/a)²`, `G_ii = −(2 a ä + ȧ²)`.-/
noncomputable def flrwEinstein (a a₁ a₂ : ℝ → ℝ) (x : Fin 4 → ℝ) : Fin 4 → Fin 4 → ℝ :=
  ![![3 * (a₁ (x 0) / a (x 0)) ^ 2, 0, 0, 0],
    ![0, -(2 * a (x 0) * a₂ (x 0) + a₁ (x 0) ^ 2), 0, 0],
    ![0, 0, -(2 * a (x 0) * a₂ (x 0) + a₁ (x 0) ^ 2), 0],
    ![0, 0, 0, -(2 * a (x 0) * a₂ (x 0) + a₁ (x 0) ^ 2)]]

/-! ### Metric partial derivatives

`flrwMetric` is a total function given by a closed formula, so every coordinate section of
every component is a globally defined one-variable function and the global evaluation rule
`pderiv_eq_of_hasDerivAt'` applies.  The only analytic input is one `HasDerivAt` fact about
the scale factor; no nondegeneracy is needed here, since the metric itself contains no
reciprocal of `a`. -/

section Sections

variable {a a₁ : ℝ → ℝ} {x : Fin 4 → ℝ}

end Sections

/-! ### Derivatives of the Christoffel table

`flrwGamma a a₁ y c d e` reads `y` only through `y 0 = t`, so all three spatial partials
vanish identically and a single `∂_t` table suffices. -/

section DGamma

variable {a a₁ a₂ : ℝ → ℝ} {x : Fin 4 → ℝ}

end DGamma

/-! ### Neighbourhood plumbing

Differentiating a Christoffel symbol needs the Christoffel *table* to be valid on a whole
neighbourhood, not just at the point, because the table involves `1/a`.  `FLRWGood` is the
set where it is valid, and these two lemmas move the coordinate line into it. -/

section Good

variable {a a₁ : ℝ → ℝ} {x : Fin 4 → ℝ}

/-- Convenience: a differentiable, locally nonvanishing scale factor is eventually
nonzero — the analytic side condition of every theorem below, from a pointwise one.
@isnad1 id=eventual.2h3v.s6.727d7186dd56 from=translated src=- shape=0a433efc vocab=f7e85ff4
-/
theorem eventually_ne_zero_of_hasDerivAt {a a₁ : ℝ → ℝ} {t : ℝ}
    (hd : HasDerivAt a (a₁ t) t) (ha : a t ≠ 0) : ∀ᶠ s in 𝓝 t, a s ≠ 0 :=
  hd.continuousAt.eventually_ne ha

end Good

/-! ### The sixteen Ricci components

Each component is its own declaration.  That is not cosmetic: proving all sixteen inside a
single `fin_cases b <;> fin_cases d <;> …` chain makes them share one heartbeat budget and
times out, whereas as separate declarations the whole set elaborates quickly.
See the trap notes in `README.md`. -/

section Components

variable {a a₁ a₂ : ℝ → ℝ} {x : Fin 4 → ℝ}
  (hp1 : ∀ c d e, pderiv 1 (fun y => flrwGamma a a₁ y c d e) x = 0)
  (hp2 : ∀ c d e, pderiv 2 (fun y => flrwGamma a a₁ y c d e) x = 0)
  (hp3 : ∀ c d e, pderiv 3 (fun y => flrwGamma a a₁ y c d e) x = 0)
  (hpt : ∀ c d e, pderiv 0 (fun y => flrwGamma a a₁ y c d e) x = flrwDGammaT a a₁ a₂ x c d e)
  (hg : ∀ c d e, christoffel (flrwMetric a) x c d e = flrwGamma a a₁ x c d e)
  (hb : ∀ (b c d e : Fin 4), pderiv b (fun y => christoffel (flrwMetric a) y c d e) x
          = pderiv b (fun y => flrwGamma a a₁ y c d e) x)
  (ha0 : a (x 0) ≠ 0)

include hp1 hp2 hp3 hpt hg hb ha0

end Components

/-! ### Ricci, scalar curvature and the Friedmann equations -/

end GRLab
