import Tengoku.SingularityCompleteLean.Singularity.ReflectedMartin
import Tengoku.SingularityCompleteLean.Singularity.OrbitGreenBoundary

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Canonical Green normalizers and a subsequential Naïm-type pairing

This module uses the actual denominators G(x,o)G(o,y), proves their positivity,
and extracts a common subsequence instead of assuming coordinate limits.
Exponential bounds and finite-path separation remain explicit hypotheses.

This is a subsequential limit theorem. It does not prove uniqueness, dependence
only on geometric boundary endpoints, or existence of the full Naïm limit.
-/

noncomputable section
open Filter
open scoped Topology

namespace Singularity

variable {Γ : Type*} [Group Γ]

/-- The finite Green quotient whose off-diagonal boundary limit is sought.-/
def finiteNaimQuotient (s : Finset Γ) (μ : Γ → ℝ) (o x y : Γ) : ℝ :=
  walkGreen s μ x y / (walkGreen s μ x o * walkGreen s μ o y)

variable [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]

variable [Countable Γ] {J : Type*}
variable (s : Finset Γ) (μ : Γ → ℝ) (hμ : ∀ g ∈ s, 0 ≤ μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
  {A : Set Γ} (e : (ℤ × J) ≃ A)

end Singularity
