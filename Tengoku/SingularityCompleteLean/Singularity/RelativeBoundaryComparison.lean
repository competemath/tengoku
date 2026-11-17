import Tengoku.SingularityCompleteLean.Singularity.RelativeExitFlux
import Tengoku.SingularityCompleteLean.Singularity.HarmonicEntranceComparison

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# From relative Green bounds to boundary comparison

Only Green values on the additional stopping set enter the last-exit flux.
Two-sided comparison on that set therefore transfers to entrance probabilities
when the direct term vanishes, and then to nonnegative L² harmonic data.
The geometric comparison and separator hypotheses remain explicit.
-/

noncomputable section
open MeasureTheory
open scoped Classical
namespace Singularity

variable {Γ : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableMul Γ]
  [MeasurableSingletonClass Γ] [Countable Γ]
variable (s : Finset Γ) (μ : Γ → ℝ) (hμ : ∀ g ∈ s, 0 ≤ μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
  (A B : Set Γ)

end Singularity
