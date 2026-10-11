import Tengoku.OpenaiMath.OAI.Combinatorics.ExpectationThreshold.SelectorGroupCost
import Tengoku.OpenaiMath.OAI.Combinatorics.ExpectationThreshold.SelectorGlobalCostProfiles
import Tengoku.OpenaiMath.OAI.Combinatorics.ExpectationThreshold.SelectorFeasibility
import Tengoku.OpenaiMath.OAI.Combinatorics.ExpectationThreshold.SelectorProfile

namespace OAI

/-!
# The global cost of actual selected moves

Partition selected pairs first by their final coloring and then by their
full profile. The profile estimate removes the profile-dependent heavy
sets before summation. Word-count normalization and the finite geometric
bound then give the strict budget under the actual coloring law.
-/

noncomputable section

open scoped BigOperators Classical

namespace TalagrandThreshold.Selector

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {F : Family α} {s : ℕ}

/-- Actual bad original colorings that select one fixed endpoint. -/
def selectedOriginals (mu : MassFamily F) (z : Coloring α s) :
    Finset (Coloring α s) := by
  classical
  exact Finset.univ.filter fun a => Bad mu a ∧ Selected mu a z

/-- Only the full profiles that occur for this endpoint. -/
def selectedProfiles (mu : MassFamily F) (z : Coloring α s) :
    Finset (Profile s) := by
  classical
  exact (selectedOriginals mu z).image fun a => profile a z

@[simp] theorem mem_selectedOriginals (mu : MassFamily F)
    (a z : Coloring α s) :
    a ∈ selectedOriginals mu z ↔ Bad mu a ∧ Selected mu a z := by
  classical
  simp only [selectedOriginals, Finset.mem_filter, Finset.mem_univ, true_and]

/-- A selected move from a bad coloring has a nonzero tuple of row sizes. -/
theorem selectedProfiles_rowCount_ne_zero (mu : MassFamily F)
    (z : Coloring α s) (n : Profile s) (hn : n ∈ selectedProfiles mu z) :
    rowCount n ≠ 0 := by
  classical
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨hbad, hselected⟩ := (mem_selectedOriginals mu a z).mp ha
  intro hz
  have hpos := Finset.card_pos.mpr (hselected.changes_nonempty hbad)
  rw [← profileSize_profile a z] at hpos
  simp only [profileSize, hz, Pi.zero_apply, Finset.sum_const_zero,
    lt_self_iff_false] at hpos

/-- Grouping by the actual full profile loses no original coloring. -/
theorem selected_endpoint_cost_grouped (mu : MassFamily F)
    (z : Coloring α s) (f : Coloring α s → ℝ) :
    (∑ a ∈ selectedOriginals mu z, f a) =
      ∑ n ∈ selectedProfiles mu z, ∑ a ∈ groupOriginals mu z n, f a := by
  classical
  have hgroup (n : Profile s) :
      (selectedOriginals mu z).filter (fun a => profile a z = n) =
        groupOriginals mu z n := by
    ext a
    simp [selectedOriginals, groupOriginals, and_assoc]
  symm
  calc
    (∑ n ∈ selectedProfiles mu z, ∑ a ∈ groupOriginals mu z n, f a) =
        ∑ n ∈ selectedProfiles mu z,
          ∑ a ∈ (selectedOriginals mu z).filter (fun a => profile a z = n), f a := by
      simp only [hgroup]
    _ = ∑ a ∈ selectedOriginals mu z, f a :=
      Finset.sum_fiberwise_of_maps_to
        (fun a ha => Finset.mem_image.mpr ⟨a, ha, rfl⟩) f

/-- Swapping the two finite sums groups all actual selected pairs by endpoint. -/
theorem selected_cost_group_by_endpoint (mu : MassFamily F)
    (f : Coloring α s → Coloring α s → ℝ) :
    (∑ a ∈ (Finset.univ : Finset (Coloring α s)).filter (Bad mu),
      ∑ z ∈ selectedMoves mu a, f a z) =
      ∑ z : Coloring α s, ∑ a ∈ selectedOriginals mu z, f a z := by
  classical
  calc
    (∑ a ∈ (Finset.univ : Finset (Coloring α s)).filter (Bad mu),
        ∑ z ∈ selectedMoves mu a, f a z) =
        ∑ a : Coloring α s, ∑ z : Coloring α s,
          if Bad mu a ∧ Selected mu a z then f a z else 0 := by
      simp only [selectedMoves, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : Bad mu a <;> simp [ha]
    _ = ∑ z : Coloring α s, ∑ a ∈ selectedOriginals mu z, f a z := by
      rw [Finset.sum_comm]
      simp only [selectedOriginals, Finset.sum_filter]

end TalagrandThreshold.Selector

end

end OAI
