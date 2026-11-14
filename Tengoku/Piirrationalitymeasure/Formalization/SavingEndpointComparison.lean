import Tengoku.Piirrationalitymeasure.Formalization.FloorThresholdComparison
import Tengoku.Piirrationalitymeasure.Formalization.SavingCircle

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Equal positions relative to the endpoint families give equal actual indicators. -/

namespace PiIrrationality

open Set

theorem savingEndpoint_le_iff_argument {a b c : ℝ} (z : ℝ × ℝ)
    (T : SavingEndpointType) (j : ℤ) (u : ℝ)
    (hm : 0 < savingEndpointSlope a b c T) :
    savingEndpoint a b c z T j ≤ u ↔ (j : ℝ) ≤ savingEndpointArgument a b c z T u := by
  rw [savingEndpoint, div_le_iff₀ hm]
  unfold savingEndpointArgument
  constructor <;> intro h <;> nlinarith only [h]

theorem savingEndpoint_candidate_argument_bounds (T : SavingEndpointType) {z : ℝ × ℝ}
    (hz : parameterNormOne z ≤ 1 / 100) {u : ℝ}
    (hu : u ∈ Ioo (candidateEndpointCut : ℝ) ((candidateEndpointCut : ℝ) + 1)) :
    (candidateEndpointStart T : ℝ) - 1 < savingEndpointArgument 1857 3714 5570 z T u ∧
      savingEndpointArgument 1857 3714 5570 z T u <
        ((candidateEndpointStart T + (candidateEndpointSize T : ℤ) : ℤ) : ℝ) := by
  have hm : 0 < savingEndpointSlope 1857 3714 5570 T := by
    cases T <;> norm_num [savingEndpointSlope]
  have hsize : savingEndpointSlope 1857 3714 5570 T = (candidateEndpointSize T : ℝ) := by
    cases T <;> norm_num [savingEndpointSlope, candidateEndpointSize]
  obtain ⟨hlo, hhi⟩ := savingEndpoint_candidate_cut_bounds T hz
  have hL := mul_lt_mul_of_pos_left hu.1 hm
  have hR := mul_lt_mul_of_pos_left hu.2 hm
  unfold savingEndpointArgument at hlo hhi ⊢
  push_cast
  rw [← hsize]
  constructor <;> nlinarith only [hlo, hhi, hL, hR]

theorem savingEndpoint_floor_eq_of_comparisons (T : SavingEndpointType)
    {z w : ℝ × ℝ} (hz : parameterNormOne z ≤ 1 / 100) (hw : parameterNormOne w ≤ 1 / 100)
    {u v : ℝ}
    (hu : u ∈ Ioo (candidateEndpointCut : ℝ) ((candidateEndpointCut : ℝ) + 1))
    (hv : v ∈ Ioo (candidateEndpointCut : ℝ) ((candidateEndpointCut : ℝ) + 1))
    (hcmp : ∀ j ∈ candidateEndpointIndices T,
      savingEndpoint 1857 3714 5570 z T j ≤ u ↔ savingEndpoint 1857 3714 5570 w T j ≤ v) :
    ⌊savingEndpointArgument 1857 3714 5570 z T u⌋ =
      ⌊savingEndpointArgument 1857 3714 5570 w T v⌋ := by
  obtain ⟨hxlo, hxhi⟩ := savingEndpoint_candidate_argument_bounds T hz hu
  obtain ⟨hylo, hyhi⟩ := savingEndpoint_candidate_argument_bounds T hw hv
  apply floor_eq_of_threshold_comparisons _ _ _ _ hxlo.le hxhi hylo.le hyhi
  intro j hjlo hjhi
  have hj := (mem_candidateEndpointIndices T j).mpr ⟨hjlo, hjhi⟩
  have hm : 0 < savingEndpointSlope 1857 3714 5570 T := by
    cases T <;> norm_num [savingEndpointSlope]
  simpa only [savingEndpoint_le_iff_argument _ _ _ _ hm] using hcmp j hj

theorem translatedSavingChi_eq_of_endpoint_comparisons
    {z w : ℝ × ℝ} (hz : parameterNormOne z ≤ 1 / 100) (hw : parameterNormOne w ≤ 1 / 100)
    {u v : ℝ}
    (hu : u ∈ Ioo (candidateEndpointCut : ℝ) ((candidateEndpointCut : ℝ) + 1))
    (hv : v ∈ Ioo (candidateEndpointCut : ℝ) ((candidateEndpointCut : ℝ) + 1))
    (hcmp : ∀ T : SavingEndpointType, ∀ j ∈ candidateEndpointIndices T,
      savingEndpoint 1857 3714 5570 z T j ≤ u ↔ savingEndpoint 1857 3714 5570 w T j ≤ v) :
    translatedSavingChi 1857 3714 5570 z u = translatedSavingChi 1857 3714 5570 w v := by
  have hf := fun T => savingEndpoint_floor_eq_of_comparisons T hz hw hu hv (hcmp T)
  rw [translatedSavingChi_floor_arguments, translatedSavingChi_floor_arguments]
  rw [hf .A, hf .B, hf .C, hf .Q]

end PiIrrationality
