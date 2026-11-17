import Tengoku.SingularityCompleteLean.Singularity.MartinCompactness

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Reflected Martin quotients and simultaneous subsequences

The row normalizer G(x,o) belongs to the reflected walk. We transfer the proved
compactness result using the actual transposed Green kernel and the proved
reflection of semigroup generation, then extract a common row/column subsequence.
-/

noncomputable section
open Filter
open scoped Topology

namespace Singularity

variable {Γ : Type*} [Group Γ]

/-- The row quotient is the Martin quotient for the reflected law.-/
def reverseMartinQuotient (s : Finset Γ) (μ : Γ → ℝ) (o z x : Γ) : ℝ :=
  walkGreen s μ x z / walkGreen s μ x o

variable [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]
variable (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)

end Singularity
