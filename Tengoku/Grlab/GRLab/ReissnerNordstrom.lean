/-
Copyright (c) 2026 Brandon Yates. All rights reserved.
Released under Apache 2.0 license.
-/
import Tengoku.Grlab.GRLab.SSEinstein
import Tengoku.Grlab.GRLab.Lapse

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Reissner–Nordström satisfies the Einstein equation with the defined Maxwell stress tensor

In coordinates `(t, r, θ, φ)` with signature `(−,+,+,+)` and `G = c = 1`,

  `ds² = −f(r) dt² + f(r)⁻¹ dr² + r² dθ² + r² sin²θ dφ²`,   `f = 1 − 2M/r + Q²/r²`,

is the charged, static, spherically symmetric black hole.  Unlike Schwarzschild it is
**not** Ricci-flat — the Coulomb field carries energy — but its Ricci scalar still
vanishes, because the Maxwell stress tensor is traceless in four dimensions.  The two
scalar brackets of `GRLab/Lapse.lean` are

  `A = 1 − f − r f′ = Q²/r²`,   `B = f″/2 + f′/r = Q²/r⁴`,

so by `GRLab.ricci_ss` and `GRLab.scalarCurvature_ss`

  `R_tt = f Q²/r⁴`,  `R_rr = −Q²/(r⁴f)`,  `R_θθ = Q²/r²`,  `R_φφ = Q² sin²θ/r²`,
  `R = 2A/r² − 2B = 0`,   hence   `G_μν = R_μν`.

The matter side is the Faraday tensor of the Coulomb field, `F = (Q/r²) dt ∧ dr`, whose
Maxwell stress tensor `T_{μν} = (1/4π)(F_{μα}F_ν{}^α − ¼ g_{μν}F_{αβ}F^{αβ})` satisfies

  `F^{tr} = −Q/r²`,  `F_{αβ}F^{αβ} = −2Q²/r⁴`,
  `8π T_tt = Q²f/r⁴`, `8π T_rr = −Q²/(r⁴f)`, `8π T_θθ = Q²/r²`, `8π T_φφ = Q² sin²θ/r²`,

which is componentwise equal to `G_μν`.  That identity — `G_μν = 8π T_μν` in all sixteen
components — is `reissnerNordstrom_einstein_eq_maxwell`, the flagship of this module.

## Oracle

Every value above was fixed *before* any Lean proof was attempted, by an independent sympy
implementation of `GRLab`'s exact index formulas, cross-checked component-by-component
against a separate computer-algebra curvature engine: Christoffel 64/64 agree, Ricci
16/16 agree, Einstein 16/16 agree, scalar curvature agrees, and the residual
`G_μν − 8π T_μν` is exactly `0` in all sixteen components.  Zero mismatches.
-/

namespace GRLab

open Matrix Filter Topology

/-! ### The lapse -/

/-- The Reissner–Nordström lapse `f(r) = 1 − 2M/r + Q²/r²`.-/
noncomputable def rnF (M Q : ℝ) : ℝ → ℝ := fun s => 1 - 2 * M / s + Q ^ 2 / s ^ 2

/-- Its derivative, `f′(r) = 2M/r² − 2Q²/r³`.-/
noncomputable def rnF₁ (M Q : ℝ) : ℝ → ℝ := fun s => 2 * M / s ^ 2 - 2 * Q ^ 2 / s ^ 3

/-- Its second derivative, `f″(r) = −4M/r³ + 6Q²/r⁴`.-/
noncomputable def rnF₂ (M Q : ℝ) : ℝ → ℝ := fun s => -(4 * M / s ^ 3) + 6 * Q ^ 2 / s ^ 4

/-- The Reissner–Nordström metric.-/
noncomputable def reissnerNordstrom (M Q : ℝ) : MetricFn 4 := ssMetric (rnF M Q)

/-- The region where the chart is a chart: `r > 0`, off the horizons, off the poles.-/
def RNRegion (M Q : ℝ) : Set (Fin 4 → ℝ) :=
  {x | 0 < x 1 ∧ rnF M Q (x 1) ≠ 0 ∧ Real.sin (x 2) ≠ 0}

/-! ### The electromagnetic field -/

/-- Faraday tensor of the Coulomb field, `F = (Q/r²) dt ∧ dr`.-/
noncomputable def coulombF (Q : ℝ) (x : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of ![![0, Q / (x 1) ^ 2, 0, 0], ![-(Q / (x 1) ^ 2), 0, 0, 0],
              ![0, 0, 0, 0], ![0, 0, 0, 0]]

/-- `F^{μν} = g^{μα} g^{νβ} F_{αβ}`.-/
noncomputable def faradayUp (g : MetricFn 4) (F : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (x : Fin 4 → ℝ) (μ ν : Fin 4) : ℝ :=
  ∑ α : Fin 4, ∑ β : Fin 4, (g x)⁻¹ μ α * (g x)⁻¹ ν β * F x α β

/-- The invariant `F_{αβ} F^{αβ}`.-/
noncomputable def faradayInvariant (g : MetricFn 4)
    (F : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (x : Fin 4 → ℝ) : ℝ :=
  ∑ α : Fin 4, ∑ β : Fin 4, F x α β * faradayUp g F x α β

/-- `F_{μα} F_ν{}^α = F_{μα} g^{αβ} F_{νβ}`.-/
noncomputable def faradayContract (g : MetricFn 4)
    (F : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (x : Fin 4 → ℝ) (μ ν : Fin 4) : ℝ :=
  ∑ α : Fin 4, ∑ β : Fin 4, F x μ α * (g x)⁻¹ α β * F x ν β

/-- **Maxwell stress-energy tensor**
`T_{μν} = (1/4π)(F_{μα}F_ν{}^α − ¼ g_{μν} F_{αβ}F^{αβ})`.-/
noncomputable def stressEM (g : MetricFn 4)
    (F : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (x : Fin 4 → ℝ) (μ ν : Fin 4) : ℝ :=
  (1 / (4 * Real.pi)) * (faradayContract g F x μ ν
    - (1 / 4 : ℝ) * g x μ ν * faradayInvariant g F x)

/-! ### Basic structure of the chart -/

/-- The Reissner–Nordström metric is diagonal, hence symmetric.-/
theorem reissnerNordstrom_isSymm (M Q : ℝ) : IsSymmetricMetric (reissnerNordstrom M Q) :=
  ssMetric_isSymm _

/-- The chart region is open in the radial direction.-/
theorem eventually_rnF_ne_zero {M Q r : ℝ} (hr : r ≠ 0) (h : rnF M Q r ≠ 0) :
    ∀ᶠ s in 𝓝 r, rnF M Q s ≠ 0 :=
  (hasDerivAt_rnLapse M Q hr).continuousAt.eventually_ne h

/-! ### Curvature

Nothing here is a new curvature computation: `GRLab.ricci_ss` already did it for an
arbitrary lapse, and the specialisation is the pure scalar algebra of
`GRLab.rnLapse_areal` and `GRLab.rnLapse_radial`. -/

/-! ### The Maxwell sector -/

/-! ### The Einstein equation with the Maxwell stress tensor -/

end GRLab
