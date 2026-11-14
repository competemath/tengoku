import Tengoku.Piirrationalitymeasure.Formalization.EndpointCountRealization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The finite index sets enumerate exactly the base endpoints in one period. -/

namespace PiIrrationality

/--
@isnad1 id=iff.0h2v.s5.648879589225 from=translated src=- shape=6e6138e7 vocab=1a1cddc7
-/
theorem mem_candidateEndpointIndices (T : SavingEndpointType) (j : ℤ) :
    j ∈ candidateEndpointIndices T ↔
      candidateEndpointStart T ≤ j ∧
        j < candidateEndpointStart T + (candidateEndpointSize T : ℤ) := by
  simp only [candidateEndpointIndices, Finset.mem_map, Finset.mem_range]
  change (∃ n : ℕ, n < candidateEndpointSize T ∧
    (n : ℤ) + candidateEndpointStart T = j) ↔ _
  constructor
  · rintro ⟨n, hn, rfl⟩
    omega
  · rintro ⟨hlo, hhi⟩
    refine ⟨(j - candidateEndpointStart T).toNat, ?_, ?_⟩ <;> omega

/--
@isnad1 id=eq.0h1v.s3.78c0e8a953b2 from=translated src=- shape=981f0160 vocab=f7cdc4cb
-/
theorem candidateEndpointIndices_card (T : SavingEndpointType) :
    (candidateEndpointIndices T).card = candidateEndpointSize T := by
  simp only [candidateEndpointIndices, Finset.card_map, Finset.card_range]

/--
@isnad1 id=eq.0h0v.s5.c5b5b10b3eea from=translated src=- shape=b784143e vocab=ed5d4131
-/
theorem candidateEndpointIndices_total :
    (candidateEndpointIndices .A).card + (candidateEndpointIndices .B).card +
      (candidateEndpointIndices .C).card + (candidateEndpointIndices .Q).card = 14856 := by
  simp only [candidateEndpointIndices_card, candidateEndpointSize]

/--
@isnad1 id=iff.0h2v.s5.61e721b51677 from=translated src=- shape=774fec79 vocab=e7f33aff
-/
theorem candidateEndpointBase_mem_Ico (T : SavingEndpointType) (j : ℤ) :
    candidateEndpointBaseRat T j ∈ Set.Ico (0 : ℚ) 1 ↔ j ∈ candidateEndpointIndices T := by
  have hm : 0 < candidateEndpointSlopeRat T := by
    cases T <;> norm_num [candidateEndpointSlopeRat]
  have hc0 : ⌈candidateEndpointShiftRat T⌉ = candidateEndpointStart T := by
    cases T <;> norm_num [candidateEndpointShiftRat, candidateEndpointStart]
  have hc1 : ⌈candidateEndpointSlopeRat T + candidateEndpointShiftRat T⌉ =
      candidateEndpointStart T + (candidateEndpointSize T : ℤ) := by
    cases T <;> norm_num [candidateEndpointSlopeRat, candidateEndpointShiftRat,
      candidateEndpointStart, candidateEndpointSize]
  rw [Set.mem_Ico, candidateEndpointBaseRat, mem_candidateEndpointIndices]
  have h0 : 0 ≤ ((j : ℚ) - candidateEndpointShiftRat T) / candidateEndpointSlopeRat T ↔
      candidateEndpointShiftRat T ≤ (j : ℚ) := by
    rw [le_div_iff₀ hm, zero_mul, sub_nonneg]
  rw [h0, div_lt_iff₀ hm, one_mul, sub_lt_iff_lt_add, ← Int.ceil_le, ← Int.lt_ceil,
    hc0, hc1]

/--
@isnad1 id=iff.0h2v.s6.ec34b9331cb7 from=translated src=- shape=1bd8d8a7 vocab=d8a94a45
-/
theorem savingEndpoint_candidate_mem_Ico (T : SavingEndpointType) (j : ℤ) :
    savingEndpoint 1857 3714 5570 0 T j ∈ Set.Ico (0 : ℝ) 1 ↔
      j ∈ candidateEndpointIndices T := by
  rw [← candidateEndpointBase_ratCast, ← candidateEndpointBase_mem_Ico]
  simp only [Set.mem_Ico]
  norm_cast

/--
@isnad1 id=injectiv.0h1v.s2.cfc8fb0ddabf from=translated src=- shape=7000f90d vocab=08645b28
-/
theorem candidateEndpointBase_injective (T : SavingEndpointType) :
    Function.Injective (candidateEndpointBaseRat T) := by
  have hm : candidateEndpointSlopeRat T ≠ 0 := by
    cases T <;> norm_num [candidateEndpointSlopeRat]
  intro j k h
  unfold candidateEndpointBaseRat at h
  have heq := (div_left_inj' hm).mp h
  exact_mod_cast (sub_left_inj.mp heq)

end PiIrrationality
