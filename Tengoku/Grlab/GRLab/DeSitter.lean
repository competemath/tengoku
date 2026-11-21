/-
Copyright (c) 2026 Brandon Yates. All rights reserved.
Released under Apache 2.0 license.
-/
import Tengoku.Grlab.GRLab.SSEinstein

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Two cheap instantiations of `ricci_ss`

Both are one-line specialisations of `GRLab.ricci_ss` — the Ricci tensor of the static
spherically symmetric chart for an *arbitrary* lapse — followed by scalar algebra.  They
cost almost nothing and they pin the framework from two opposite directions.

* **Static de Sitter**, `f = 1 − r²/L²`.  An **Einstein space**: `R_{μν} = (3/L²) g_{μν}`,
  scalar curvature `12/L²`.  This is the maximally symmetric positive-curvature vacuum, and
  it certifies that `GRLab.ricci` returns a genuinely nonzero, correctly-signed tensor.
* **Minkowski in spherical coordinates**, `f = 1`.  Ricci-flat.  The sanity check at the
  other end: the areal-radius chart of flat space has nine nonvanishing Christoffel
  symbols, so "all the Γ's are zero" is *not* why the Schwarzschild computation gives zero.

## Brackets

`GRLab.ricci_ss` reduces everything to the two scalars `A = 1 − f − r f′` (angular block)
and `B = f″/2 + f′/r` (radial block), with

  `R_tt = f · B`, `R_rr = −B/f`, `R_θθ = A`, `R_φφ = sin²θ · A`,   `R = 2A/r² − 2B`.

| solution | `f` | `A` | `B` | `R` |
|---|---|---|---|---|
| Minkowski (spherical) | `1` | `0` | `0` | `0` |
| static de Sitter | `1 − r²/L²` | `3r²/L²` | `−3/L²` | `12/L²` |

Both rows were produced by an independent sympy computation of `GRLab`'s exact index
formulas and cross-checked against a separate computer-algebra curvature engine (the static de Sitter and Minkowski entry points); see `README.md`.
-/

namespace GRLab

open Matrix Filter Topology

/-! ## Static de Sitter -/

/-- The static de Sitter lapse `f(r) = 1 − r²/L²`, with its first and second derivatives.-/
noncomputable def dsF (L : ℝ) : ℝ → ℝ := fun s => 1 - s ^ 2 / L ^ 2
noncomputable def dsF₁ (L : ℝ) : ℝ → ℝ := fun s => -(2 * s / L ^ 2)
noncomputable def dsF₂ (L : ℝ) : ℝ → ℝ := fun _ => -(2 / L ^ 2)

/-- **The static de Sitter metric** with Hubble length `L`.-/
noncomputable def deSitterStatic (L : ℝ) : MetricFn 4 := ssMetric (dsF L)

/-- The region on which the static patch chart is a chart: `r > 0`, off the cosmological
horizon `r = L`, off the poles.-/
def DSRegion (L : ℝ) : Set (Fin 4 → ℝ) :=
  {x | 0 < x 1 ∧ dsF L (x 1) ≠ 0 ∧ Real.sin (x 2) ≠ 0}

/--
@isnad1 id=hasderiv.0h2v.s5.acb9f2da2c54 from=translated src=- shape=d9353bef vocab=fd3aa7a6
-/
theorem hasDerivAt_dsF (L : ℝ) (r : ℝ) : HasDerivAt (dsF L) (dsF₁ L r) r := by
  have h1 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * r) r := by
    simpa using hasDerivAt_pow 2 r
  exact ((h1.div_const (L ^ 2)).const_sub 1).congr_deriv (by simp only [dsF₁])

/--
@isnad1 id=hasderiv.0h2v.s5.9b7b2595a0f7 from=translated src=- shape=d9353bef vocab=608aa525
-/
theorem hasDerivAt_dsF' (L : ℝ) (r : ℝ) : HasDerivAt (dsF₁ L) (dsF₂ L r) r :=
  ((((hasDerivAt_id' r).const_mul 2).div_const (L ^ 2)).neg).congr_deriv (by
    simp only [dsF₂]
    ring)

/--
@isnad1 id=issymmet.0h1v.s3.35fa473a1b82 from=translated src=- shape=6e63af07 vocab=e09ca73d
-/
theorem deSitterStatic_isSymm (L : ℝ) : IsSymmetricMetric (deSitterStatic L) :=
  ssMetric_isSymm _

/-- The static patch is open in the radial direction.
@isnad1 id=eventual.1h2v.s5.a2a684b09992 from=translated src=- shape=42c98aa2 vocab=86d5ee94
-/
theorem eventually_dsF_ne_zero {L r : ℝ} (h : dsF L r ≠ 0) : ∀ᶠ s in 𝓝 r, dsF L s ≠ 0 :=
  (hasDerivAt_dsF L r).continuousAt.eventually_ne h

/-- The angular bracket for static de Sitter: `1 − f − r f′ = 3r²/L²`.
@isnad1 id=eq.1h2v.s6.c1eca90fe19e from=translated src=- shape=ad62b321 vocab=99f0bce8
-/
theorem dsLapse_areal (L : ℝ) {r : ℝ} (hL : L ≠ 0) :
    1 - dsF L r - r * dsF₁ L r = 3 * r ^ 2 / L ^ 2 := by
  simp only [dsF, dsF₁]
  field_simp
  ring

/-- The radial bracket for static de Sitter: `f″/2 + f′/r = −3/L²`.
@isnad1 id=eq.2h2v.s6.632f6c581ff6 from=translated src=- shape=9f7540f5 vocab=f36dfb50
-/
theorem dsLapse_radial (L : ℝ) {r : ℝ} (hL : L ≠ 0) (hr : r ≠ 0) :
    dsF₂ L r / 2 + dsF₁ L r / r = -(3 / L ^ 2) := by
  simp only [dsF₁, dsF₂]
  field_simp
  ring

/-! ## Minkowski in spherical coordinates -/

/-- The constant lapse `f = 1`.-/
noncomputable def flatF : ℝ → ℝ := fun _ => 1
noncomputable def flatF₁ : ℝ → ℝ := fun _ => 0

/-- **Minkowski space in spherical coordinates**,
`ds² = −dt² + dr² + r²dθ² + r² sin²θ dφ²`.-/
noncomputable def minkowskiSpherical : MetricFn 4 := ssMetric flatF

/--
@isnad1 id=issymmet.0h0v.s2.3704f2bed552 from=translated src=- shape=cef8a6bf vocab=8801e9a7
-/
theorem minkowskiSpherical_isSymm : IsSymmetricMetric minkowskiSpherical :=
  ssMetric_isSymm _

end GRLab
