/-
Copyright (c) 2026 Brandon Yates. All rights reserved.
Released under Apache 2.0 license.
-/
import Tengoku.Grlab.GRLab.SSRicci
import Tengoku.Grlab.GRLab.Lapse

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Schwarzschild metric is Ricci-flat

**The flagship theorem of `GRLab`.**  In Schwarzschild coordinates `(t, r, θ, φ)`,

  `ds² = −(1 − 2M/r) dt² + (1 − 2M/r)⁻¹ dr² + r² dθ² + r² sin²θ dφ²`

satisfies the vacuum Einstein equations `R_{μν} = 0` on the exterior region `r > 2M`
(with `θ` away from the coordinate poles, where the chart itself degenerates).

The proof carries no calculus of its own.  All of it lives in `GRLab.ricci_ss`, which
computes the Ricci tensor of a static spherically symmetric metric for an *arbitrary*
lapse `f`; here that general answer is specialised to `f = 1 − 2M/r` and the two resulting
brackets are killed by the scalar identities `GRLab.schwLapse_areal` and
`GRLab.schwLapse_radial`.
-/

namespace GRLab

open Matrix Filter Topology

/-- The Schwarzschild lapse `f(r) = 1 − 2M/r`, its derivative and its second derivative.-/
noncomputable def schwF (M : ℝ) : ℝ → ℝ := fun s => 1 - 2 * M / s
noncomputable def schwF₁ (M : ℝ) : ℝ → ℝ := fun s => 2 * M / s ^ 2
noncomputable def schwF₂ (M : ℝ) : ℝ → ℝ := fun s => -(4 * M / s ^ 3)

/-- **The Schwarzschild metric** in Schwarzschild coordinates, mass `M`, `G = c = 1`.-/
noncomputable def schwarzschild (M : ℝ) : MetricFn 4 := ssMetric (schwF M)

/--
@isnad1 id=issymmet.0h1v.s3.ad21b8591923 from=translated src=- shape=6e63af07 vocab=097e4618
-/
theorem schwarzschild_isSymm (M : ℝ) : IsSymmetricMetric (schwarzschild M) :=
  ssMetric_isSymm _

/-! ### The exterior region -/

/-- The Schwarzschild exterior: `r > 2M`, `r > 0`, and `θ` off the coordinate poles.-/
def SchwExterior (M : ℝ) : Set (Fin 4 → ℝ) :=
  {x | 0 < x 1 ∧ 2 * M < x 1 ∧ Real.sin (x 2) ≠ 0}

/-! ### The vacuum field equations -/

/-! ### Schwarzschild–de Sitter: a Λ-vacuum, and a nonvanishing-curvature check

Two jobs at once.  Mathematically this is the `Λ`-vacuum solution used throughout the
junction-condition literature.  Methodologically it certifies that `GRLab.ricci` is not
accidentally identically zero, and it pins the **sign** of the curvature convention inside
Lean: `R_{μν} = +Λ g_{μν}`, so positive `Λ` gives positive curvature. -/

/-- The Schwarzschild–de Sitter lapse `f(r) = 1 − 2M/r − Λr²/3` and its derivatives.-/
noncomputable def sdsF (M Λ : ℝ) : ℝ → ℝ := fun s => 1 - 2 * M / s - Λ * s ^ 2 / 3
noncomputable def sdsF₁ (M Λ : ℝ) : ℝ → ℝ := fun s => 2 * M / s ^ 2 - 2 * Λ * s / 3
noncomputable def sdsF₂ (M Λ : ℝ) : ℝ → ℝ := fun s => -(4 * M / s ^ 3) - 2 * Λ / 3

end GRLab
