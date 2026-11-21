/-
Copyright (c) 2026 Brandon Yates. All rights reserved.
Released under Apache 2.0 license.
-/
import Tengoku.Grlab.GRLab.VaidyaGamma

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Vaidya solution: Ricci is rank-at-most-one null dust (rank one wherever m′(v) ≠ 0)

**The non-static flagship of `GRLab`.**  For the ingoing Eddington–Finkelstein metric

  `ds² = −(1 − 2m(v)/r) dv² + 2 dv dr + r² dθ² + r² sin²θ dφ²`

with an arbitrary differentiable mass function `m : ℝ → ℝ`,

  `R_{μν} = (2 m′(v)/r²) δ^v_μ δ^v_ν`,   `R = 0`,   `G_{μν} = R_{μν}`.

The Ricci tensor is **null** and of **rank at most one** (rank one wherever m′(v) ≠ 0): it is a positive multiple of `l_μ l_ν` with
`l_μ = δ^v_μ` the ingoing null covector (`g^{μν} l_μ l_ν = g^{vv} = 0`).  That is precisely
the statement that Vaidya is the field of a radial flux of null dust with energy density
`m′(v)/(4π r²)`.  The vanishing of the scalar curvature is not an extra computation: it is
`R = g^{μν}R_{μν} = g^{vv} R_{vv}`, and `g^{vv} = 0`.

This is the metric the author's junction-condition programme glues across null and
timelike shells, so the sign conventions matter and are stated explicitly:
signature `(−,+,+,+)`, `G = c = 1`, coordinates `x 0 = v`, `x 1 = r`, `x 2 = θ`, `x 3 = φ`,
and `m′ > 0` is **ingoing** radiation (the mass grows to the future).

Every value was fixed by an independent sympy computation of `GRLab`'s exact index formulas
and cross-checked component-by-component against a separate computer-algebra curvature engine:
64/64 Christoffel symbols, 16/16 Ricci components, 16/16 Einstein components, zero
mismatches.  See `README.md`.

## Regularity

`m` is assumed only **once** differentiable, on a neighbourhood of `v`.  See
`GRLab/VaidyaChart.lean` for why that suffices even though the full `∂_v Γ` table contains
an `m″`.
-/

namespace GRLab

open Matrix Filter Topology

/-! ### The sixteen Ricci components

One declaration per component.  A single `fin_cases b <;> fin_cases d <;> … <;> field_simp
<;> ring` chain shares one heartbeat budget across all sixteen goals and times out; split
into declarations it elaborates quickly.  See the trap notes in `README.md`. -/

section Components
variable {m m₁ : ℝ → ℝ} {x : Fin 4 → ℝ}
  (hp3 : ∀ a c d, pderiv 3 (fun y => vGamma m m₁ y a c d) x = 0)
  (hp0r : ∀ c d, pderiv 0 (fun y => vGamma m m₁ y 0 c d) x = vDGammaV m₁ x c d)
  (hp0t : ∀ a b, pderiv 0 (fun y => vGamma m m₁ y a a b) x = vDGammaVtr m₁ x a b)
  (hpr : ∀ a c d, pderiv 1 (fun y => vGamma m m₁ y a c d) x = vDGammaR m m₁ x a c d)
  (hpt : ∀ a c d, pderiv 2 (fun y => vGamma m m₁ y a c d) x = vDGammaT m x a c d)
  (hg  : ∀ a c d, christoffel (vaidyaMetric m) x a c d = vGamma m m₁ x a c d)
  (hb  : ∀ (c a e g : Fin 4), pderiv c (fun y => christoffel (vaidyaMetric m) y a e g) x
          = pderiv c (fun y => vGamma m m₁ y a e g) x)
  (hr0 : x 1 ≠ 0) (hs0 : Real.sin (x 2) ≠ 0)

/-! #### The twelve components with `d ≠ v`

For these the `∂_v` **trace** table is never reached: the only `pderiv 0` the contraction
produces is `∂_v Γ^v_{db}` from the `a = v` row, and the trace term `∂_d Γ^a_{ab}` carries
`d ≠ 0`.  So `hp0t` is genuinely absent from their hypotheses — the linter confirms it. -/

section OffTime
include hp3 hp0r hpr hpt hg hb hr0 hs0

end OffTime

/-! #### The four components with `d = v`

Here the trace term is `∂_v Γ^a_{ab}`, so `hp0t` is required.  `R_{vv}` is the only
nonvanishing component of the whole tensor. -/

section OnTime
include hp3 hp0r hp0t hpr hpt hg hb hr0 hs0

end OnTime

end Components

/-! ### The Ricci tensor of the Vaidya metric -/

end GRLab
