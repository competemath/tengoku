import Tengoku.SingularityCompleteLean.Singularity.GreenJumpBounds
import Tengoku.SingularityCompleteLean.Singularity.GreenProductBounds
import Tengoku.SingularityCompleteLean.Singularity.ReflectedSupport

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Green distance and its coarse comparison with permitted word length

The Green distance is minus the logarithm of the normalized Green kernel.
For nonsymmetric walks it is a directed distance; no symmetric metric instance
is claimed. The checked exponential bounds give uniform linear upper and lower
bounds in shortest jump length, with an additive constant in the lower bound.
-/

noncomputable section
open Set
open scoped Classical

namespace Singularity

variable {Γ : Type*} [Group Γ]

/-- The possibly asymmetric Green distance of the actual random walk.-/
def greenDistance (s : Finset Γ) (μ : Γ → ℝ) (x y : Γ) : ℝ :=
  -Real.log (walkGreen s μ x y / walkGreen s μ 1 1)

/-- All diagonal Green entries have the same value.
@isnad1 id=eq.0h4v.s5.4d58f55c9e8d from=translated src=- shape=7aeb0b12 vocab=8db0b60b
-/
theorem walkGreen_diagonal_eq (s : Finset Γ) (μ : Γ → ℝ) (x : Γ) :
    walkGreen s μ x x = walkGreen s μ 1 1 := by
  simpa only [mul_one] using walkGreen_left s μ x 1 1

/-- The Green distance is left invariant.
@isnad1 id=eq.0h6v.s6.8f363c7702ea from=translated src=- shape=c658a447 vocab=c58b1d5b
-/
theorem greenDistance_left (s : Finset Γ) (μ : Γ → ℝ) (g x y : Γ) :
    greenDistance s μ (g * x) (g * y) = greenDistance s μ x y := by
  simp only [greenDistance, walkGreen_left]

variable [MeasurableSpace Γ] [MeasurableSingletonClass Γ] [MeasurableMul Γ]
  (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)

end Singularity
