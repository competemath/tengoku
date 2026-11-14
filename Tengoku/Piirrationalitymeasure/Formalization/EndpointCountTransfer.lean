import Tengoku.Piirrationalitymeasure.Formalization.EndpointSectorOrder

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Transfer the computed endpoint counts to arbitrary real directions in open sectors. -/

namespace PiIrrationality

open Filter Set
open scoped Topology

theorem candidateActualJumpCount_eventually_germ (v : ℝ × ℝ) (T : SavingEndpointType) :
    ∀ᶠ s : ℝ in 𝓝[>] 0, candidateActualJumpCount v T s =
      ∑ j ∈ candidateEndpointIndices T,
        (savingEndpointChiGerm 1857 3714 5570 v T j (-1) -
          savingEndpointChiGerm 1857 3714 5570 v T j 1) := by
  have h : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ j ∈ candidateEndpointIndices T,
      translatedSavingChi 1857 3714 5570 (s • v)
        (savingEndpoint 1857 3714 5570 (s • v) T j - s ^ 2) =
          savingEndpointChiGerm 1857 3714 5570 v T j (-1) ∧
      translatedSavingChi 1857 3714 5570 (s • v)
        (savingEndpoint 1857 3714 5570 (s • v) T j + s ^ 2) =
          savingEndpointChiGerm 1857 3714 5570 v T j 1 := by
    apply (eventually_all_finset _).mpr
    intro j _
    filter_upwards [savingEndpoint_chi_eventually 1857 3714 5570 v T j (-1),
      savingEndpoint_chi_eventually 1857 3714 5570 v T j 1] with s hL hR
    exact ⟨by simpa only [neg_one_mul, sub_eq_add_neg] using hL,
      by simpa only [one_mul] using hR⟩
  filter_upwards [h] with s hs
  unfold candidateActualJumpCount
  apply Finset.sum_congr rfl
  intro j hj
  rw [(hs j hj).1, (hs j hj).2]

theorem candidateOpenSector_actualJumpCount {i : Fin 12} {v : ℝ × ℝ}
    (hv : CandidateOpenSector i v) (T : SavingEndpointType) :
    ∀ᶠ s : ℝ in 𝓝[>] 0, candidateActualJumpCount v T s =
      (candidateEndpointCount (candidateSectorDirection i) T : ℝ) := by
  filter_upwards [candidateActualJumpCount_eventually_germ v T] with s hs
  rw [hs]
  unfold candidateEndpointCount
  rw [Int.cast_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hL := candidateOpenSector_chiGerm hv T j (-1)
  have hR := candidateOpenSector_chiGerm hv T j 1
  norm_num only [Rat.cast_neg, Rat.cast_one] at hL hR
  rw [hL, hR, Int.cast_sub]

end PiIrrationality
