import Tengoku.SingularityCompleteLean.Singularity.RelativeLastEntrance

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# First- and last-entrance transfers inside a fixed killed domain

The additional finite stopping set changes one endpoint, while the original
killing set is retained in every entrance coefficient and Green value.
Reflection identifies both discarded parts with the same union-killed kernel.
-/

noncomputable section
open scoped Classical
namespace Singularity

variable {Γ : Type*} [Group Γ]

/-- Actual endpoint transfer before hitting the original killing set A.-/
def relativePairTransfer (s : Finset Γ) (μ : Γ → ℝ) (A : Set Γ) (B : Finset Γ) (last : Bool) :
    (Γ × Γ → ℝ) →ₗ[ℝ] (Γ × Γ → ℝ) where
  toFun f p := ∑ b : B,
    (if last then firstEntranceKernel (s.map ⟨Inv.inv, inv_injective⟩) (fun g => μ g⁻¹) (A ∪ (B : Set Γ)) p.2 b
      else firstEntranceKernel s μ (A ∪ (B : Set Γ)) p.1 b) *
      f (if last then (p.1, (b : Γ)) else ((b : Γ), p.2))
  map_add' f g := by ext p; simp [mul_add, Finset.sum_add_distrib]
  map_smul' c f := by ext p; simp [Finset.mul_sum, mul_left_comm]

/-- Positivity preserves comparisons on the admissible successor pairs.-/
theorem relativePairTransfer_monoOn (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (A : Set Γ) (B : Finset Γ) (last : Bool) (S S' : Set (Γ × Γ))
    (hmove : ∀ p ∈ S, ∀ b : B, (if last then (p.1, (b : Γ)) else ((b : Γ), p.2)) ∈ S')
    (f g : Γ × Γ → ℝ) (hfg : ∀ p ∈ S', f p ≤ g p) :
    ∀ p ∈ S, relativePairTransfer s μ A B last f p ≤ relativePairTransfer s μ A B last g p := by
  intro p hp
  apply Finset.sum_le_sum
  intro b _
  apply mul_le_mul_of_nonneg_left (hfg _ (hmove p hp b))
  cases last
  · exact firstEntranceKernel_nonneg s μ hμ _ p.1 b
  · exact firstEntranceKernel_nonneg _ _ (reflected_jump_nonneg s μ hμ) _ p.2 b

variable [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ] [Countable Γ]

end Singularity
