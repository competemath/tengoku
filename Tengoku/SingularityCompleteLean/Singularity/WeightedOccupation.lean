import Tengoku.SingularityCompleteLean.Singularity.InfiniteWalkProcess
import Tengoku.SingularityCompleteLean.Singularity.GreenAdjoint
import Tengoku.SingularityCompleteLean.Singularity.CountingSequence
import Tengoku.Seed.MeasureTheory.Integral.Lebesgue.Countable

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Weighted occupation and square-summable Green rows

Tonelli identifies the expected accumulated nonnegative vertex weight with its
Green-weighted sum. A finite sum gives almost-sure summability along the actual
sample path. In particular, a weight bounded by a Green row is summable along
the walk under the operator spectral-gap hypothesis.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal Classical

namespace Singularity

variable {Γ : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
  [MeasurableMul Γ]

/-- Every Green row is square summable, since it is an adjoint Green column.-/
theorem walkGreen_row_square_summable (s : Finset Γ) (μ : Γ → ℝ)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (x : Γ) :
    Summable (fun y => walkGreen s μ x y ^ 2) := by
  have h := counting_square_summable ((green (rightMarkov s μ)).adjoint (countingDelta x))
  simpa only [green_adjoint_coefficient s μ hgap, Complex.norm_real, Real.norm_eq_abs,
    sq_abs] using h

variable [Countable Γ]

end Singularity
