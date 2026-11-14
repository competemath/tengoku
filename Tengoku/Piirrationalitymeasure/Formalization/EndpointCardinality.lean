import Tengoku.Piirrationalitymeasure.Formalization.EndpointCoincidences

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Exact distinct endpoint counts, using the coincidence catalogue (6.42). -/

namespace PiIrrationality

def candidateEndpointBases (T : SavingEndpointType) : Finset ℚ :=
  (candidateEndpointIndices T).image (candidateEndpointBaseRat T)

theorem candidateEndpointBases_card (T : SavingEndpointType) :
    (candidateEndpointBases T).card = candidateEndpointSize T := by
  rw [candidateEndpointBases,
    Finset.card_image_of_injective _ (candidateEndpointBase_injective T),
    candidateEndpointIndices_card]

theorem candidateEndpointBases_A_subset_B :
    candidateEndpointBases .A ⊆ candidateEndpointBases .B := by
  intro x hx
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
  refine Finset.mem_image.mpr ⟨2 * j - 1, ?_, ?_⟩
  · rw [mem_candidateEndpointIndices] at hj ⊢
    norm_num [candidateEndpointStart, candidateEndpointSize] at hj ⊢
    omega
  · exact ((candidateEndpoint_coincidence_AB j (2 * j - 1)).mpr rfl).symm

theorem candidateEndpointBases_B_inter_C :
    candidateEndpointBases .B ∩ candidateEndpointBases .C = {0, 1 / 2} := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxB, hxC⟩ := Finset.mem_inter.mp hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hxB
    obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp hxC
    rcases (candidateEndpoint_coincidence_BC hj hk).mp heq.symm with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      norm_num [candidateEndpointBaseRat, candidateEndpointShiftRat, candidateEndpointSlopeRat]
  · intro hx
    have hmem (j k : ℤ) (hj : j ∈ candidateEndpointIndices .B)
        (hk : k ∈ candidateEndpointIndices .C)
        (hB : candidateEndpointBaseRat .B j = x)
        (hC : candidateEndpointBaseRat .C k = x) :
        x ∈ candidateEndpointBases .B ∩ candidateEndpointBases .C :=
      Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨j, hj, hB⟩,
        Finset.mem_image.mpr ⟨k, hk, hC⟩⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · apply hmem 0 0 <;> norm_num [mem_candidateEndpointIndices,
        candidateEndpointStart, candidateEndpointSize, candidateEndpointBaseRat,
        candidateEndpointShiftRat, candidateEndpointSlopeRat]
    · apply hmem 1857 2785 <;> norm_num [mem_candidateEndpointIndices,
        candidateEndpointStart, candidateEndpointSize, candidateEndpointBaseRat,
        candidateEndpointShiftRat, candidateEndpointSlopeRat]

theorem candidateEndpointBases_B_inter_Q :
    candidateEndpointBases .B ∩ candidateEndpointBases .Q = {1 / 2} := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxB, hxQ⟩ := Finset.mem_inter.mp hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hxB
    obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp hxQ
    obtain ⟨rfl, rfl⟩ := (candidateEndpoint_coincidence_BQ hj hk).mp heq.symm
    norm_num [candidateEndpointBaseRat, candidateEndpointShiftRat, candidateEndpointSlopeRat]
  · intro hx
    have hx' : x = 1 / 2 := Finset.mem_singleton.mp hx
    subst x
    refine Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨1857, ?_, ?_⟩,
      Finset.mem_image.mpr ⟨1858, ?_, ?_⟩⟩ <;>
      norm_num [mem_candidateEndpointIndices, candidateEndpointStart, candidateEndpointSize,
        candidateEndpointBaseRat, candidateEndpointShiftRat, candidateEndpointSlopeRat]

theorem candidateEndpointBases_C_inter_Q :
    candidateEndpointBases .C ∩ candidateEndpointBases .Q =
      {1 / 10, 3 / 10, 1 / 2, 7 / 10, 9 / 10} := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxC, hxQ⟩ := Finset.mem_inter.mp hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hxC
    obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp hxQ
    rcases (candidateEndpoint_coincidence_CQ hj hk).mp heq.symm with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      norm_num [candidateEndpointBaseRat, candidateEndpointShiftRat, candidateEndpointSlopeRat]
  · intro hx
    have hmem (j k : ℤ) (hj : j ∈ candidateEndpointIndices .C)
        (hk : k ∈ candidateEndpointIndices .Q)
        (hC : candidateEndpointBaseRat .C j = x)
        (hQ : candidateEndpointBaseRat .Q k = x) :
        x ∈ candidateEndpointBases .C ∩ candidateEndpointBases .Q :=
      Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨j, hj, hC⟩,
        Finset.mem_image.mpr ⟨k, hk, hQ⟩⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · apply hmem 557 372 <;> norm_num [mem_candidateEndpointIndices,
        candidateEndpointStart, candidateEndpointSize, candidateEndpointBaseRat,
        candidateEndpointShiftRat, candidateEndpointSlopeRat]
    · apply hmem 1671 1115 <;> norm_num [mem_candidateEndpointIndices,
        candidateEndpointStart, candidateEndpointSize, candidateEndpointBaseRat,
        candidateEndpointShiftRat, candidateEndpointSlopeRat]
    · apply hmem 2785 1858 <;> norm_num [mem_candidateEndpointIndices,
        candidateEndpointStart, candidateEndpointSize, candidateEndpointBaseRat,
        candidateEndpointShiftRat, candidateEndpointSlopeRat]
    · apply hmem 3899 2601 <;> norm_num [mem_candidateEndpointIndices,
        candidateEndpointStart, candidateEndpointSize, candidateEndpointBaseRat,
        candidateEndpointShiftRat, candidateEndpointSlopeRat]
    · apply hmem 5013 3344 <;> norm_num [mem_candidateEndpointIndices,
        candidateEndpointStart, candidateEndpointSize, candidateEndpointBaseRat,
        candidateEndpointShiftRat, candidateEndpointSlopeRat]

def candidateDistinctEndpointBases : Finset ℚ :=
  candidateEndpointBases .A ∪ candidateEndpointBases .B ∪
    candidateEndpointBases .C ∪ candidateEndpointBases .Q

theorem candidateDistinctEndpointBases_card : candidateDistinctEndpointBases.card = 12992 := by
  unfold candidateDistinctEndpointBases
  rw [Finset.union_eq_right.mpr candidateEndpointBases_A_subset_B, Finset.card_union,
    Finset.union_inter_distrib_right, candidateEndpointBases_B_inter_Q,
    candidateEndpointBases_C_inter_Q, Finset.card_union, candidateEndpointBases_B_inter_C]
  norm_num [candidateEndpointBases_card, candidateEndpointSize]

theorem mem_candidateDistinctEndpointBases (x : ℚ) :
    x ∈ candidateDistinctEndpointBases ↔
      ∃ T : SavingEndpointType, ∃ j ∈ candidateEndpointIndices T,
        candidateEndpointBaseRat T j = x := by
  simp only [candidateDistinctEndpointBases, Finset.mem_union,
    candidateEndpointBases, Finset.mem_image]
  constructor
  · rintro (((h | h) | h) | h)
    · exact ⟨.A, h⟩
    · exact ⟨.B, h⟩
    · exact ⟨.C, h⟩
    · exact ⟨.Q, h⟩
  · rintro ⟨T, h⟩
    cases T
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inl (Or.inr h)
    · exact Or.inr h

end PiIrrationality
