import Tengoku.Piirrationalitymeasure.Formalization.EndpointCountData

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The rational counts equal eventual sums of jumps of the actual indicator. -/

namespace PiIrrationality

open Filter Set
open scoped Topology

theorem candidateEndpointSlope_ratCast (T : SavingEndpointType) :
    (candidateEndpointSlopeRat T : ℝ) = savingEndpointSlope 1857 3714 5570 T := by
  cases T <;> norm_num [candidateEndpointSlopeRat, savingEndpointSlope]

theorem candidateEndpointShift_ratCast (T : SavingEndpointType) :
    (candidateEndpointShiftRat T : ℝ) = savingEndpointShift 0 T := by
  cases T <;> norm_num [candidateEndpointShiftRat, savingEndpointShift]

theorem candidateEndpointGradient_ratCast (v : ℚ × ℚ) (T : SavingEndpointType) :
    (candidateEndpointGradientRat v T : ℝ) = savingEndpointGradient (v.1, v.2) T := by
  cases T <;> simp [candidateEndpointGradientRat, savingEndpointGradient, savingEndpointShift] <;> ring

theorem candidateEndpointBase_ratCast (T : SavingEndpointType) (j : ℤ) :
    (candidateEndpointBaseRat T j : ℝ) = savingEndpoint 1857 3714 5570 0 T j := by
  simp only [candidateEndpointBaseRat, Rat.cast_div, Rat.cast_sub, Rat.cast_intCast,
    candidateEndpointShift_ratCast, candidateEndpointSlope_ratCast, savingEndpoint]

theorem candidateEndpointVelocity_ratCast (v : ℚ × ℚ) (T : SavingEndpointType) :
    (candidateEndpointVelocityRat v T : ℝ) = savingEndpointVelocity 1857 3714 5570 (v.1, v.2) T := by
  simp only [candidateEndpointVelocityRat, Rat.cast_div, Rat.cast_neg,
    candidateEndpointGradient_ratCast, candidateEndpointSlope_ratCast, savingEndpointVelocity]

theorem candidateEndpointFloorGerm_ratCast (v : ℚ × ℚ) (T S : SavingEndpointType)
    (j : ℤ) (side : ℚ) :
    savingEndpointFloorGerm 1857 3714 5570 (v.1, v.2) T j side S =
      candidateEndpointFloorGermRat v T j side S := by
  unfold savingEndpointFloorGerm candidateEndpointFloorGermRat
  rw [← quadraticFloorGerm_ratCast]
  simp only [Rat.cast_add, Rat.cast_mul, candidateEndpointSlope_ratCast,
    candidateEndpointBase_ratCast, candidateEndpointShift_ratCast,
    candidateEndpointVelocity_ratCast, candidateEndpointGradient_ratCast, savingEndpointArgument]

theorem candidateEndpointChiGerm_ratCast (v : ℚ × ℚ) (T : SavingEndpointType)
    (j : ℤ) (side : ℚ) :
    savingEndpointChiGerm 1857 3714 5570 (v.1, v.2) T j side =
      (candidateEndpointChiGermRat v T j side : ℝ) := by
  simp only [savingEndpointChiGerm, candidateEndpointChiGermRat, candidateEndpointFloorGerm_ratCast]
  split_ifs <;> norm_num

noncomputable def candidateActualJumpCount (v : ℝ × ℝ) (T : SavingEndpointType) (s : ℝ) : ℝ :=
  ∑ j ∈ candidateEndpointIndices T,
    (translatedSavingChi 1857 3714 5570 (s • v)
      (savingEndpoint 1857 3714 5570 (s • v) T j - s ^ 2) -
    translatedSavingChi 1857 3714 5570 (s • v)
      (savingEndpoint 1857 3714 5570 (s • v) T j + s ^ 2))

theorem candidateActualJumpCount_eventually (v : ℚ × ℚ) (T : SavingEndpointType) :
    ∀ᶠ s : ℝ in 𝓝[>] 0, candidateActualJumpCount (v.1, v.2) T s =
      (candidateEndpointCount v T : ℝ) := by
  have h : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ j ∈ candidateEndpointIndices T,
      translatedSavingChi 1857 3714 5570 (s • ((v.1 : ℝ), (v.2 : ℝ)))
        (savingEndpoint 1857 3714 5570 (s • ((v.1 : ℝ), (v.2 : ℝ))) T j - s ^ 2) =
          (candidateEndpointChiGermRat v T j (-1) : ℝ) ∧
      translatedSavingChi 1857 3714 5570 (s • ((v.1 : ℝ), (v.2 : ℝ)))
        (savingEndpoint 1857 3714 5570 (s • ((v.1 : ℝ), (v.2 : ℝ))) T j + s ^ 2) =
          (candidateEndpointChiGermRat v T j 1 : ℝ) := by
    apply (eventually_all_finset _).mpr
    intro j _
    have hL := savingEndpoint_chi_eventually 1857 3714 5570
      ((v.1 : ℝ), (v.2 : ℝ)) T j (-1)
    have hR := savingEndpoint_chi_eventually 1857 3714 5570
      ((v.1 : ℝ), (v.2 : ℝ)) T j 1
    filter_upwards [hL, hR] with s hL hR
    have hcastL := candidateEndpointChiGerm_ratCast v T j (-1)
    have hcastR := candidateEndpointChiGerm_ratCast v T j 1
    norm_num only [Rat.cast_neg, Rat.cast_one] at hcastL hcastR
    rw [hcastL] at hL
    rw [hcastR] at hR
    exact ⟨by simpa only [neg_one_mul, sub_eq_add_neg] using hL,
      by simpa only [one_mul] using hR⟩
  filter_upwards [h] with s hs
  unfold candidateActualJumpCount candidateEndpointCount
  rw [Int.cast_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [(hs j hj).1, (hs j hj).2, Int.cast_sub]

end PiIrrationality
