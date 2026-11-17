import Tengoku.SingularityCompleteLean.Singularity.EntranceFinalJump

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Boundary flux after the last visit to an additional stopping set

Combining the final-jump formula with relative last entrance yields an exact
factorization of the first-entrance kernel. The inner infinite sums are proved
summable before they are interchanged with the finite jump sum.
-/

noncomputable section
open scoped Classical
namespace Singularity

variable {Γ : Type*} [Group Γ]

/-- The reflected entrance coefficient followed by the original final jump.-/
def boundaryExitFlux (s : Finset Γ) (μ : Γ → ℝ) (D : Set Γ) (a b : Γ) : ℝ :=
  ∑ g ∈ s, μ g * firstEntranceKernel (s.map ⟨Inv.inv, inv_injective⟩)
    (fun g => μ g⁻¹) D (a * g⁻¹) b

/--
@isnad1 id=le.1h6v.s6.b215314c18b5 from=translated src=- shape=d6392006 vocab=b31864d5
-/
theorem boundaryExitFlux_nonneg (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (D : Set Γ) (a b : Γ) :
    0 ≤ boundaryExitFlux s μ D a b := by
  apply Finset.sum_nonneg
  intro g hg
  exact mul_nonneg (hμ g hg)
    (firstEntranceKernel_nonneg _ _ (reflected_jump_nonneg s μ hμ) D _ b)

/--
@isnad1 id=eq.1h6v.s5.a1236dc3b70a from=translated src=- shape=8510d4f8 vocab=06d177e5
-/
theorem boundaryExitFlux_eq_zero_of_notMem (s : Finset Γ) (μ : Γ → ℝ)
    (D : Set Γ) (a b : Γ) (hb : b ∉ D) : boundaryExitFlux s μ D a b = 0 := by
  simp only [boundaryExitFlux, firstEntranceKernel_eq_zero_of_notMem _ _ D _ b hb,
    mul_zero, Finset.sum_const_zero]

variable [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ] [Countable Γ]
variable (s : Finset Γ) (μ : Γ → ℝ) (hμ : ∀ g ∈ s, 0 ≤ μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
  (A B : Set Γ)

end Singularity
