import Tengoku.Piirrationalitymeasure.Formalization.AffineGap
import Tengoku.Piirrationalitymeasure.Formalization.SavingPartitionJumpSum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Actual two-sided endpoint samples equal the fixed adjacent partition values. -/

set_option maxRecDepth 100000

namespace PiIrrationality

open Filter Set
open scoped Topology

theorem candidateEndpointPartition_rank (e : CandidateEndpointEnumeration) (z : ℝ × ℝ)
    (p : CandidateEndpointLabel) :
    candidateEndpointPartition e z ((e.symm p).val + 1) = candidateEndpointPosition z p := by
  simpa only [candidateEndpointPartition, Equiv.apply_symm_apply] using
    finiteEndpointPartition_internal (candidateEndpointCut : ℝ) ((candidateEndpointCut : ℝ) + 1)
      (fun j => candidateEndpointPosition z (e j)) (e.symm p)

theorem candidatePartition_gap_eventually (e : CandidateEndpointEnumeration) (v : ℝ × ℝ)
    (horder : ∀ᶠ s : ℝ in 𝓝[>] 0, CandidateOrderedEndpoints e (s • v))
    {k : ℕ} (hk : k < Fintype.card CandidateEndpointLabel + 1) :
    ∀ᶠ s : ℝ in 𝓝[>] 0, s ^ 2 <
      candidateEndpointPartition e (s • v) (k + 1) - candidateEndpointPartition e (s • v) k := by
  have heq (s : ℝ) :
      candidateEndpointPartition e (s • v) (k + 1) - candidateEndpointPartition e (s • v) k =
      (candidateEndpointPartition e 0 (k + 1) - candidateEndpointPartition e 0 k) +
        s * (candidatePartitionVelocity e v (k + 1) - candidatePartitionVelocity e v k) := by
    rw [candidateEndpointPartition_smul e v s (k + 1), candidateEndpointPartition_smul e v s k]
    ring
  have hp : ∀ᶠ s : ℝ in 𝓝[>] 0,
      0 < (candidateEndpointPartition e 0 (k + 1) - candidateEndpointPartition e 0 k) +
        s * (candidatePartitionVelocity e v (k + 1) - candidatePartitionVelocity e v k) := by
    filter_upwards [horder] with s hs
    rw [← heq]
    exact sub_pos.mpr (candidateEndpointPartition_adjacent_lt hs hk)
  simpa only [heq] using affine_gt_sq_eventually_of_pos hp

theorem candidatePartitionJump_actual_eventually (e : CandidateEndpointEnumeration)
    (w v : ℝ × ℝ) (hw : CandidateOrderedEndpoints e w) (hwn : parameterNormOne w ≤ 1 / 100)
    (hscaled : ∀ᶠ s : ℝ in 𝓝[>] 0,
      CandidateOrderedEndpoints e (s • v) ∧ parameterNormOne (s • v) ≤ 1 / 100) :
    ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ p : CandidateEndpointLabel,
      translatedSavingChi 1857 3714 5570 (s • v) (candidateEndpointPosition (s • v) p - s ^ 2) -
        translatedSavingChi 1857 3714 5570 (s • v) (candidateEndpointPosition (s • v) p + s ^ 2) =
          candidatePartitionJump e (candidatePartitionIndicator e w) p := by
  apply eventually_all.mpr
  intro p
  have hr := (e.symm p).isLt
  have hL := candidatePartition_gap_eventually e v (hscaled.mono fun _ h => h.1)
    (k := (e.symm p).val) (by omega)
  have hR := candidatePartition_gap_eventually e v (hscaled.mono fun _ h => h.1)
    (k := (e.symm p).val + 1) (by omega)
  filter_upwards [hscaled, hL, hR, self_mem_nhdsWithin] with s hs hL hR hspos
  have hsq : 0 < s ^ 2 := sq_pos_of_pos hspos
  have hp := candidateEndpointPartition_rank e (s • v) p
  have hleft : candidateEndpointPosition (s • v) p - s ^ 2 ∈
      candidateEndpointCell e (s • v) (e.symm p).val := by
    constructor <;> linarith only [hL, hp, hsq]
  have hright : candidateEndpointPosition (s • v) p + s ^ 2 ∈
      candidateEndpointCell e (s • v) ((e.symm p).val + 1) := by
    constructor <;> linarith only [hR, hp, hsq]
  have hchiL := translatedSavingChi_eq_partitionIndicator hs.1 hw hs.2 hwn (by omega) hleft
  have hchiR := translatedSavingChi_eq_partitionIndicator hs.1 hw hs.2 hwn (by omega) hright
  rw [hchiL, hchiR]
  rfl

theorem candidatePartitionLinear_eq_actual_weighted_eventually (e : CandidateEndpointEnumeration)
    (w v : ℝ × ℝ) (hw : CandidateOrderedEndpoints e w) (hwn : parameterNormOne w ≤ 1 / 100)
    (hscaled : ∀ᶠ s : ℝ in 𝓝[>] 0,
      CandidateOrderedEndpoints e (s • v) ∧ parameterNormOne (s • v) ≤ 1 / 100) :
    ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ z : ℝ × ℝ,
      candidatePartitionLinear e (candidatePartitionIndicator e w) z =
        candidateActualJumpCount v .A s * savingEndpointVelocity 1857 3714 5570 z .A +
        candidateActualJumpCount v .B s * savingEndpointVelocity 1857 3714 5570 z .B +
        candidateActualJumpCount v .C s * savingEndpointVelocity 1857 3714 5570 z .C +
        candidateActualJumpCount v .Q s * savingEndpointVelocity 1857 3714 5570 z .Q := by
  filter_upwards [candidatePartitionJump_actual_eventually e w v hw hwn hscaled] with s hs
  intro z
  rw [candidatePartitionLinear_eq_label_sum]
  calc
    _ = ∑ p : CandidateEndpointLabel,
        (translatedSavingChi 1857 3714 5570 (s • v) (candidateEndpointPosition (s • v) p - s ^ 2) -
          translatedSavingChi 1857 3714 5570 (s • v) (candidateEndpointPosition (s • v) p + s ^ 2)) *
            savingEndpointVelocity 1857 3714 5570 z p.1 := by
      apply Finset.sum_congr rfl
      intro p _
      rw [hs p]
    _ = ∑ T : SavingEndpointType, ∑ j ∈ candidateEndpointIndices T,
        (translatedSavingChi 1857 3714 5570 (s • v) (savingEndpoint 1857 3714 5570 (s • v) T j - s ^ 2) -
          translatedSavingChi 1857 3714 5570 (s • v)
            (savingEndpoint 1857 3714 5570 (s • v) T j + s ^ 2)) *
              savingEndpointVelocity 1857 3714 5570 z T := by
      simpa only [candidateEndpointPosition] using candidateEndpointLabel_sum
        (fun T j =>
          (translatedSavingChi 1857 3714 5570 (s • v)
              (savingEndpoint 1857 3714 5570 (s • v) T j - s ^ 2) -
            translatedSavingChi 1857 3714 5570 (s • v)
              (savingEndpoint 1857 3714 5570 (s • v) T j + s ^ 2)) *
                savingEndpointVelocity 1857 3714 5570 z T)
    _ = ∑ T : SavingEndpointType,
        candidateActualJumpCount v T s * savingEndpointVelocity 1857 3714 5570 z T := by
      apply Finset.sum_congr rfl
      intro T _
      unfold candidateActualJumpCount
      rw [Finset.sum_mul]
    _ = _ := sum_savingEndpointType _

end PiIrrationality
