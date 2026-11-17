import Tengoku.SingularityCompleteLean.Singularity.RelativeLastEntrance

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The final jump into a stopping set

First entrance at a boundary vertex consists of the time-zero contribution
and a path killed on that set followed by one final jump. We derive the formula
from uniqueness of the counting-L² Dirichlet problem.
-/

noncomputable section
open MeasureTheory
open scoped Classical
namespace Singularity

variable {Γ : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableMul Γ]
  [MeasurableSingletonClass Γ] [Countable Γ]

omit [Countable Γ] in
/-- A Markov operator sends a point source to its finitely many predecessors.
@isnad1 id=eq.0h4v.s13.eed070e2e649 from=translated src=- shape=1b8ec475 vocab=496d630a
-/
theorem rightMarkov_delta_predecessors (s : Finset Γ) (μ : Γ → ℝ) (a : Γ) :
    rightMarkov s μ (countingDelta a) =
      ∑ g ∈ s, (μ g : ℂ) • countingDelta (a * g⁻¹) := by
  apply Lp.ext
  apply Measure.ae_count_iff.mpr
  intro x
  rw [rightMarkov_apply, ← countingEvaluation_apply]
  simp only [map_sum, map_smul, countingEvaluation_apply, countingDelta_apply,
    smul_eq_mul]
  apply Finset.sum_congr rfl
  intro g hg
  rw [eq_mul_inv_iff_mul_eq]

variable (s : Finset Γ) (μ : Γ → ℝ) (hμ : ∀ g ∈ s, 0 ≤ μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
  (A : Set Γ)

end Singularity
