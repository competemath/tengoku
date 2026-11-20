/-
Copyright (c) 2026 Brandon Yates. All rights reserved.
Released under Apache 2.0 license.
-/
import Tengoku.Grlab.GRLab.Curvature

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The static spherically symmetric chart

Coordinates are `x 0 = t`, `x 1 = r`, `x 2 = θ`, `x 3 = φ`, and the metric is

  `ds² = −f(r) dt² + f(r)⁻¹ dr² + r² dθ² + r² sin²θ dφ²`,

the general static spherically symmetric line element in "areal radius" gauge.  Every
vacuum-type spherical solution used in the junction-condition literature is of this form
(`f = 1 − 2M/r` Schwarzschild, `f = 1 − 2M/r + Q²/r²` Reissner–Nordström,
`f = 1 − 2M/r − Λr²/3` Schwarzschild–de Sitter, `f = 1 − 2M/r − c/r^{3w+1}` Kiselev).

Working with a general lapse `f` rather than a specific rational function is a deliberate
tractability choice: `ring` and `field_simp` see `f (x 1)`, `f₁ (x 1)`, `f₂ (x 1)` as
*atoms*, so the curvature computation never blows up into rational-function normalisation.
Specialisation to a particular solution is then pure scalar algebra with no calculus.
-/

namespace GRLab

open Matrix Filter Topology

/-- The general static spherically symmetric metric with lapse `f`:
`diag(−f(r), 1/f(r), r², r² sin²θ)` in coordinates `(t, r, θ, φ)`.-/
noncomputable def ssMetric (f : ℝ → ℝ) : MetricFn 4 := fun x =>
  Matrix.diagonal ![-(f (x 1)), (f (x 1))⁻¹, (x 1) ^ 2, (x 1) ^ 2 * Real.sin (x 2) ^ 2]

lemma ssMetric_apply (f : ℝ → ℝ) (x : Fin 4 → ℝ) (i j : Fin 4) :
    ssMetric f x i j =
      if i = j then ![-(f (x 1)), (f (x 1))⁻¹, (x 1) ^ 2, (x 1) ^ 2 * Real.sin (x 2) ^ 2] i
      else 0 := by
  simp [ssMetric, Matrix.diagonal_apply]

/-- A diagonal metric is symmetric.-/
theorem ssMetric_isSymm (f : ℝ → ℝ) : IsSymmetricMetric (ssMetric f) := by
  intro y i j
  rcases eq_or_ne i j with h | h
  · rw [h]
  · rw [ssMetric_apply, ssMetric_apply, ite_eq_right h, ite_eq_right h.symm]

/-- **The Christoffel table** for the static spherically symmetric chart, indexed
`ssGamma f f₁ x a b c = Γ^a_{bc}`, where `f₁` is the derivative of `f`.

Nonzero entries (all others are zero), verified against an independent sympy computation
and against a separate computer-algebra curvature engine:

| symbol | value |
|---|---|
| `Γ^t_{tr} = Γ^t_{rt}` | `f′/(2f)` |
| `Γ^r_{tt}` | `f f′/2` |
| `Γ^r_{rr}` | `−f′/(2f)` |
| `Γ^r_{θθ}` | `−r f` |
| `Γ^r_{φφ}` | `−r f sin²θ` |
| `Γ^θ_{rθ} = Γ^θ_{θr}` | `1/r` |
| `Γ^θ_{φφ}` | `−sinθ cosθ` |
| `Γ^φ_{rφ} = Γ^φ_{φr}` | `1/r` |
| `Γ^φ_{θφ} = Γ^φ_{φθ}` | `cosθ/sinθ` |-/
noncomputable def ssGamma (f f₁ : ℝ → ℝ) (x : Fin 4 → ℝ) : Fin 4 → Fin 4 → Fin 4 → ℝ :=
  ![ -- a = 0  (t)
     ![![0, f₁ (x 1) / (2 * f (x 1)), 0, 0],
       ![f₁ (x 1) / (2 * f (x 1)), 0, 0, 0],
       ![0, 0, 0, 0],
       ![0, 0, 0, 0]],
     -- a = 1  (r)
     ![![f (x 1) * f₁ (x 1) / 2, 0, 0, 0],
       ![0, -(f₁ (x 1) / (2 * f (x 1))), 0, 0],
       ![0, 0, -(x 1 * f (x 1)), 0],
       ![0, 0, 0, -(x 1 * f (x 1) * Real.sin (x 2) ^ 2)]],
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

/-! ## Metric partial derivatives

The `ssMetric` is a *total* function given by a closed formula, so every coordinate section
of every component is a globally defined one-variable function.  That means the global form
`pderiv_eq_of_hasDerivAt'` applies — no neighbourhood bookkeeping is needed here, and the
only analytic hypothesis is `HasDerivAt f (f₁ (x 1)) (x 1)` (plus `f (x 1) ≠ 0` for the
`g_{rr}` section, which is `1/f`).
-/

/-- Table of metric partial derivatives, indexed `ssDMetric f f₁ x b d c = ∂_b g_{dc}`.

The nonzero entries are `∂_r g_{tt} = −f′`, `∂_r g_{rr} = −f′/f²`, `∂_r g_{θθ} = 2r`,
`∂_r g_{φφ} = 2r sin²θ` and `∂_θ g_{φφ} = 2r² sinθ cosθ`.-/
noncomputable def ssDMetric (f f₁ : ℝ → ℝ) (x : Fin 4 → ℝ) : Fin 4 → Fin 4 → Fin 4 → ℝ :=
  ![ ![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]],
     ![![-(f₁ (x 1)), 0, 0, 0],
       ![0, -(f₁ (x 1) / (f (x 1))^2), 0, 0],
       ![0, 0, 2 * x 1, 0],
       ![0, 0, 0, 2 * x 1 * Real.sin (x 2)^2]],
     ![![0,0,0,0],![0,0,0,0],![0,0,0,0],
       ![0, 0, 0, 2 * (x 1)^2 * Real.sin (x 2) * Real.cos (x 2)]],
     ![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]]

section Sections

variable {f f₁ : ℝ → ℝ} {x : Fin 4 → ℝ}

/-! The sixteen sections of the four diagonal components.  `g_{tt} = −f(r)`,
`g_{rr} = f(r)⁻¹` and `g_{θθ} = r²` depend on `r` alone; `g_{φφ} = r² sin²θ` depends on
`r` and `θ`. -/

end Sections

end GRLab
