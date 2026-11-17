import Tengoku.SingularityCompleteLean.Singularity.EntranceRepresentation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# From entrance-kernel comparison to boundary Harnack comparison

A real L² harmonic function is the absolutely convergent entrance average of
its boundary values. Comparing two rows of the actual entrance kernel thus
compares every nonnegative boundary datum with the same constants. Geometric
estimates for those kernel rows are still needed for the nested domains.
-/

noncomputable section
open MeasureTheory
open scoped Classical
namespace Singularity

variable {Γ : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableMul Γ]
  [MeasurableSingletonClass Γ] [Countable Γ]
variable (s : Finset Γ) (μ : Γ → ℝ) (hμ : ∀ g ∈ s, 0 ≤ μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (A : Set Γ)

end Singularity
