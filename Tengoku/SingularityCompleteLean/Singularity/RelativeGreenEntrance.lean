import Tengoku.SingularityCompleteLean.Singularity.EntranceRepresentation
import Tengoku.SingularityCompleteLean.Singularity.GreenSeparator

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Entrance identities inside an already killed domain

Paths may be killed on A before stopping on B. Their first-entrance weights are
exactly F_(A∪B)(x,b) for b in B\A. L² Dirichlet uniqueness gives the exact
relative Green decomposition, with absolutely convergent infinite sums.
-/

noncomputable section
open MeasureTheory
open scoped Classical
namespace Singularity

/-- A killed path cannot end in the killing set.-/
theorem killedGreen_target_mem {Γ : Type*} [Group Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (A : Set Γ) (x y : Γ) (hy : y ∈ A) :
    killedGreen s μ A x y = 0 := by
  simp [killedGreen, killedWeight, hy]

variable {Γ : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableMul Γ]
  [MeasurableSingletonClass Γ] [Countable Γ]
variable (s : Finset Γ) (μ : Γ → ℝ) (hμ : ∀ g ∈ s, 0 ≤ μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
  (A B : Set Γ)

end Singularity
