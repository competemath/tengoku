import Tengoku.SingularityCompleteLean.Singularity.FiniteEntranceDecomposition
import Tengoku.SingularityCompleteLean.Singularity.GreenFirstHit

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Green comparison through a finite entrance set

The lower product inequality follows by stopping at one vertex. For an upper
comparison, stop on a finite set where Green rows are uniformly comparable to
the row at its center. The exact remainder is the killed Green kernel.
-/

noncomputable section
open scoped Classical

namespace Singularity

variable {Γ : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableMul Γ]
  [MeasurableSingletonClass Γ] [Countable Γ]

/-- The Green kernel satisfies the lower multiplicative comparison through
any intermediate vertex, with the diagonal Green normalizer.
@isnad1 id=le.3h6v.s12.4bd93d1685a2 from=translated src=- shape=cbd05f53 vocab=c3972721
-/
theorem walkGreen_product_le (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (hgap : spectralRadius ℂ (rightMarkov s μ) < 1) (x u y : Γ) :
    walkGreen s μ x u * walkGreen s μ u y ≤ walkGreen s μ u u * walkGreen s μ x y := by
  apply walkGreen_superharmonic_bound s μ hμ hmass hgap (fun z => walkGreen s μ z y)
    (fun z => walkGreen_nonneg s μ hμ z y) _ x u
  intro z
  have h := walkGreen_first_step s μ hgap z y
  have hδ : 0 ≤ (if z = y then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  linarith

end Singularity
