import Tengoku.Piirrationalitymeasure.Formalization.EndpointCountData

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The rational counts equal eventual sums of jumps of the actual indicator. -/

namespace PiIrrationality

open Filter Set
open scoped Topology

/--
@isnad1 id=eq.0h1v.s5.8fa09928c971 from=translated src=- shape=7dbd69f2 vocab=004e7bfb
-/
theorem candidateEndpointSlope_ratCast (T : SavingEndpointType) :
    (candidateEndpointSlopeRat T : ℝ) = savingEndpointSlope 1857 3714 5570 T := by
  cases T <;> norm_num [candidateEndpointSlopeRat, savingEndpointSlope]

/--
@isnad1 id=eq.0h1v.s4.cec9bf9dac2c from=translated src=- shape=2fe30d15 vocab=cb511db1
-/
theorem candidateEndpointShift_ratCast (T : SavingEndpointType) :
    (candidateEndpointShiftRat T : ℝ) = savingEndpointShift 0 T := by
  cases T <;> norm_num [candidateEndpointShiftRat, savingEndpointShift]

/--
@isnad1 id=eq.0h2v.s5.209d6460aa8a from=translated src=- shape=9a0fd012 vocab=2e8a2f1e
-/
theorem candidateEndpointGradient_ratCast (v : ℚ × ℚ) (T : SavingEndpointType) :
    (candidateEndpointGradientRat v T : ℝ) = savingEndpointGradient (v.1, v.2) T := by
  cases T <;> simp [candidateEndpointGradientRat, savingEndpointGradient, savingEndpointShift] <;> ring

/--
@isnad1 id=eq.0h2v.s5.d0793778999c from=translated src=- shape=0314840c vocab=93f4d616
-/
theorem candidateEndpointBase_ratCast (T : SavingEndpointType) (j : ℤ) :
    (candidateEndpointBaseRat T j : ℝ) = savingEndpoint 1857 3714 5570 0 T j := by
  simp only [candidateEndpointBaseRat, Rat.cast_div, Rat.cast_sub, Rat.cast_intCast,
    candidateEndpointShift_ratCast, candidateEndpointSlope_ratCast, savingEndpoint]

/--
@isnad1 id=eq.0h2v.s5.b09fac103915 from=translated src=- shape=a7c672a8 vocab=e7977a8c
-/
theorem candidateEndpointVelocity_ratCast (v : ℚ × ℚ) (T : SavingEndpointType) :
    (candidateEndpointVelocityRat v T : ℝ) = savingEndpointVelocity 1857 3714 5570 (v.1, v.2) T := by
  simp only [candidateEndpointVelocityRat, Rat.cast_div, Rat.cast_neg,
    candidateEndpointGradient_ratCast, candidateEndpointSlope_ratCast, savingEndpointVelocity]

/--
@isnad1 id=eq.0h5v.s6.1834f5d4884b from=translated src=- shape=30954f8d vocab=cb839df2
-/
theorem candidateEndpointFloorGerm_ratCast (v : ℚ × ℚ) (T S : SavingEndpointType)
    (j : ℤ) (side : ℚ) :
    savingEndpointFloorGerm 1857 3714 5570 (v.1, v.2) T j side S =
      candidateEndpointFloorGermRat v T j side S := by
  unfold savingEndpointFloorGerm candidateEndpointFloorGermRat
  rw [← quadraticFloorGerm_ratCast]
  simp only [Rat.cast_add, Rat.cast_mul, candidateEndpointSlope_ratCast,
    candidateEndpointBase_ratCast, candidateEndpointShift_ratCast,
    candidateEndpointVelocity_ratCast, candidateEndpointGradient_ratCast, savingEndpointArgument]

/--
@isnad1 id=eq.0h4v.s6.e88dcd5b0a47 from=translated src=- shape=1577bf5c vocab=84f9b4ce
-/
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

/--
@isnad1 id=eventual.0h2v.s5.7a4d0bf173bc from=translated src=- shape=f101a6dc vocab=0fc030f5
-/
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
