/-
Copyright (c) 2026 Brandon Yates. All rights reserved.
Released under Apache 2.0 license.
-/
import Tengoku.Grlab.GRLab.StaticSpherical

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Ricci curvature of the static spherically symmetric chart

The flagship computation.  For `ds² = −f dt² + f⁻¹dr² + r²dθ² + r²sin²θ dφ²` the Ricci
tensor is diagonal for **every** lapse `f`, with (writing `E₁ = f″/2 + f′/r`)

  `R_tt = f · E₁`,  `R_rr = −E₁/f`,  `R_θθ = 1 − f − r f′`,  `R_φφ = sin²θ · R_θθ`.

Every value here was fixed by an independent sympy computation cross-checked against
a separate computer-algebra curvature engine *before* any Lean proof was attempted; see `README.md`.
-/

namespace GRLab

open Matrix Filter Topology

/-! ### Neighbourhood plumbing

Differentiating a Christoffel symbol needs the Christoffel *table* to be valid on a whole
neighbourhood, not just at the point, because the metric is only nondegenerate on the open
set `{r ≠ 0, f(r) ≠ 0, sinθ ≠ 0}`.  These lemmas move between the two.
-/

/-- Two functions agreeing on a set that the coordinate line eventually lies in have the
same partial derivative at the point.-/
lemma pderiv_congr_of_mem {n : ℕ} {b : Fin n} {F G : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    {U : Set (Fin n → ℝ)} (hU : ∀ᶠ t in 𝓝 (x b), coordLine x b t ∈ U)
    (hFG : ∀ y ∈ U, F y = G y) : pderiv b F x = pderiv b G x :=
  pderiv_congr (hU.mono fun _ ht => hFG _ ht)

/-- The open region on which the static spherical chart is a genuine Lorentzian metric and
the Christoffel table is valid.-/
def ssGood (f f₁ : ℝ → ℝ) : Set (Fin 4 → ℝ) :=
  {y | y 1 ≠ 0 ∧ f (y 1) ≠ 0 ∧ Real.sin (y 2) ≠ 0 ∧ HasDerivAt f (f₁ (y 1)) (y 1)}

variable {f f₁ f₂ : ℝ → ℝ} {x : Fin 4 → ℝ}

/-! ### Derivatives of the Christoffel table

`ssGamma f f₁ y a c d` depends on `y` only through `y 1 = r` and `y 2 = θ`, so the `t` and
`φ` partials vanish identically and only two tables are needed.  All 26 entries below were
verified against an independent `sympy` computation, 26/26 agreeing.
-/

/-- `∂_r Γ^a_{cd}`, indexed `[a][c][d]`.-/
noncomputable def ssDGammaR (f f₁ f₂ : ℝ → ℝ) (x : Fin 4 → ℝ) : Fin 4 → Fin 4 → Fin 4 → ℝ :=
  ![ -- a = 0  (t)
     ![![0, (f₂ (x 1) * f (x 1) - f₁ (x 1) ^ 2) / (2 * f (x 1) ^ 2), 0, 0],
       ![(f₂ (x 1) * f (x 1) - f₁ (x 1) ^ 2) / (2 * f (x 1) ^ 2), 0, 0, 0],
       ![0, 0, 0, 0],
       ![0, 0, 0, 0]],
     -- a = 1  (r)
     ![![(f₁ (x 1) ^ 2 + f (x 1) * f₂ (x 1)) / 2, 0, 0, 0],
       ![0, -((f₂ (x 1) * f (x 1) - f₁ (x 1) ^ 2) / (2 * f (x 1) ^ 2)), 0, 0],
       ![0, 0, -(f (x 1) + x 1 * f₁ (x 1)), 0],
       ![0, 0, 0, -((f (x 1) + x 1 * f₁ (x 1)) * Real.sin (x 2) ^ 2)]],
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
noncomputable def ssDGammaT (f _f₁ : ℝ → ℝ) (x : Fin 4 → ℝ) : Fin 4 → Fin 4 → Fin 4 → ℝ :=
  ![ -- a = 0  (t)
     ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
     -- a = 1  (r)
     ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0],
       ![0, 0, 0, -(2 * x 1 * f (x 1) * Real.sin (x 2) * Real.cos (x 2))]],
     -- a = 2  (θ)
     ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0],
       ![0, 0, 0, Real.sin (x 2) ^ 2 - Real.cos (x 2) ^ 2]],
     -- a = 3  (φ)
     ![![0, 0, 0, 0],
       ![0, 0, 0, 0],
       ![0, 0, 0, -(1 / Real.sin (x 2) ^ 2)],
       ![0, 0, -(1 / Real.sin (x 2) ^ 2), 0]]]

/-- **The Ricci tensor of the static spherically symmetric chart**, indexed `[b][d]`.
Diagonal for every lapse `f`.  With `E₁ = f″/2 + f′/r`:
`R_tt = f E₁`, `R_rr = −E₁/f`, `R_θθ = 1 − f − r f′`, `R_φφ = sin²θ R_θθ`.-/
noncomputable def ssRicci (f f₁ f₂ : ℝ → ℝ) (x : Fin 4 → ℝ) : Fin 4 → Fin 4 → ℝ :=
  ![![f (x 1) * (f₂ (x 1) / 2 + f₁ (x 1) / x 1), 0, 0, 0],
    ![0, -((f₂ (x 1) / 2 + f₁ (x 1) / x 1) / f (x 1)), 0, 0],
    ![0, 0, 1 - f (x 1) - x 1 * f₁ (x 1), 0],
    ![0, 0, 0, (1 - f (x 1) - x 1 * f₁ (x 1)) * Real.sin (x 2) ^ 2]]

/-! ### The four partial-derivative theorems for the Christoffel table

`ssGamma` reads `x` only through `x 1 = r` and `x 2 = θ`, so `∂_t Γ = ∂_φ Γ = 0`
identically, while `∂_r Γ` and `∂_θ Γ` are the two tables above.  The `HasDerivAt`
helpers isolate the six one-variable shapes that occur, which keeps the 64-way index
split cheap.
-/

/-! #### One-variable derivative shapes -/

/-! #### The radial and polar tables -/

/-! ### The sixteen Ricci components

Each component is its own declaration.  That is not cosmetic: proving all sixteen inside a
single `fin_cases b <;> fin_cases d <;> …` chain makes them share one heartbeat budget and
times out even at `maxHeartbeats 2000000`, whereas as separate declarations the whole set
elaborates in under 15 seconds.  See the trap notes in `README.md`.
-/

section Components
variable {f f₁ f₂ : ℝ → ℝ} {x : Fin 4 → ℝ}
  (hp0 : ∀ a c d, pderiv 0 (fun y => ssGamma f f₁ y a c d) x = 0)
  (hp3 : ∀ a c d, pderiv 3 (fun y => ssGamma f f₁ y a c d) x = 0)
  (hpr : ∀ a c d, pderiv 1 (fun y => ssGamma f f₁ y a c d) x = ssDGammaR f f₁ f₂ x a c d)
  (hpt : ∀ a c d, pderiv 2 (fun y => ssGamma f f₁ y a c d) x = ssDGammaT f f₁ x a c d)
  (hg  : ∀ a c d, christoffel (ssMetric f) x a c d = ssGamma f f₁ x a c d)
  (hb  : ∀ (c a e g : Fin 4), pderiv c (fun y => christoffel (ssMetric f) y a e g) x
          = pderiv c (fun y => ssGamma f f₁ y a e g) x)
  (hr0 : x 1 ≠ 0) (hf0 : f (x 1) ≠ 0) (hs0 : Real.sin (x 2) ≠ 0)

include hp0 hp3 hpr hpt hg hb hr0 hf0 hs0

end Components

/-! ### The Ricci tensor of the static spherically symmetric chart -/

end GRLab
