import Tengoku.Piirrationalitymeasure.Formalization.EndpointIndexGeometry

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The exact pairwise coincidence catalogue of candidate endpoints in (6.42). -/

namespace PiIrrationality

theorem candidateEndpoint_coincidence_AB (j k : ℤ) :
    candidateEndpointBaseRat .A j = candidateEndpointBaseRat .B k ↔ k = 2 * j - 1 := by
  unfold candidateEndpointBaseRat candidateEndpointShiftRat candidateEndpointSlopeRat
  constructor
  · intro h
    have hq : (k : ℚ) = 2 * j - 1 := by linarith
    exact_mod_cast hq
  · intro h
    rw [h]
    push_cast
    ring

theorem candidateEndpoint_coincidence_AC {j k : ℤ}
    (hj : j ∈ candidateEndpointIndices .A) (hk : k ∈ candidateEndpointIndices .C) :
    candidateEndpointBaseRat .A j = candidateEndpointBaseRat .C k ↔
      j = 929 ∧ k = 2785 := by
  rw [mem_candidateEndpointIndices] at hj hk
  norm_num [candidateEndpointStart, candidateEndpointSize] at hj hk
  constructor
  · intro h
    dsimp [candidateEndpointBaseRat, candidateEndpointShiftRat, candidateEndpointSlopeRat] at h
    have hq : (2785 : ℚ) * (2 * j - 1) = 1857 * k := by linarith
    have hz : (2785 : ℤ) * (2 * j - 1) = 1857 * k := by exact_mod_cast hq
    omega
  · rintro ⟨rfl, rfl⟩
    norm_num [candidateEndpointBaseRat, candidateEndpointShiftRat, candidateEndpointSlopeRat]

theorem candidateEndpoint_coincidence_AQ {j k : ℤ}
    (hj : j ∈ candidateEndpointIndices .A) (hk : k ∈ candidateEndpointIndices .Q) :
    candidateEndpointBaseRat .A j = candidateEndpointBaseRat .Q k ↔
      j = 929 ∧ k = 1858 := by
  rw [mem_candidateEndpointIndices] at hj hk
  norm_num [candidateEndpointStart, candidateEndpointSize] at hj hk
  constructor
  · intro h
    dsimp [candidateEndpointBaseRat, candidateEndpointShiftRat, candidateEndpointSlopeRat] at h
    have hq : (3715 : ℚ) * (2 * j - 1) = 1857 * (2 * k - 1) := by linarith
    have hz : (3715 : ℤ) * (2 * j - 1) = 1857 * (2 * k - 1) := by exact_mod_cast hq
    omega
  · rintro ⟨rfl, rfl⟩
    norm_num [candidateEndpointBaseRat, candidateEndpointShiftRat, candidateEndpointSlopeRat]

theorem candidateEndpoint_coincidence_BC {j k : ℤ}
    (hj : j ∈ candidateEndpointIndices .B) (hk : k ∈ candidateEndpointIndices .C) :
    candidateEndpointBaseRat .B j = candidateEndpointBaseRat .C k ↔
      (j = 0 ∧ k = 0) ∨ (j = 1857 ∧ k = 2785) := by
  rw [mem_candidateEndpointIndices] at hj hk
  norm_num [candidateEndpointStart, candidateEndpointSize] at hj hk
  constructor
  · intro h
    dsimp [candidateEndpointBaseRat, candidateEndpointShiftRat, candidateEndpointSlopeRat] at h
    have hq : (2785 : ℚ) * j = 1857 * k := by linarith
    have hz : (2785 : ℤ) * j = 1857 * k := by exact_mod_cast hq
    omega
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
      norm_num [candidateEndpointBaseRat, candidateEndpointShiftRat, candidateEndpointSlopeRat]

theorem candidateEndpoint_coincidence_BQ {j k : ℤ}
    (hj : j ∈ candidateEndpointIndices .B) (hk : k ∈ candidateEndpointIndices .Q) :
    candidateEndpointBaseRat .B j = candidateEndpointBaseRat .Q k ↔
      j = 1857 ∧ k = 1858 := by
  rw [mem_candidateEndpointIndices] at hj hk
  norm_num [candidateEndpointStart, candidateEndpointSize] at hj hk
  constructor
  · intro h
    dsimp [candidateEndpointBaseRat, candidateEndpointShiftRat, candidateEndpointSlopeRat] at h
    have hq : (3715 : ℚ) * j = 1857 * (2 * k - 1) := by linarith
    have hz : (3715 : ℤ) * j = 1857 * (2 * k - 1) := by exact_mod_cast hq
    omega
  · rintro ⟨rfl, rfl⟩
    norm_num [candidateEndpointBaseRat, candidateEndpointShiftRat, candidateEndpointSlopeRat]

theorem candidateEndpoint_coincidence_CQ {j k : ℤ}
    (hj : j ∈ candidateEndpointIndices .C) (hk : k ∈ candidateEndpointIndices .Q) :
    candidateEndpointBaseRat .C j = candidateEndpointBaseRat .Q k ↔
      (j = 557 ∧ k = 372) ∨ (j = 1671 ∧ k = 1115) ∨ (j = 2785 ∧ k = 1858) ∨
      (j = 3899 ∧ k = 2601) ∨ (j = 5013 ∧ k = 3344) := by
  rw [mem_candidateEndpointIndices] at hj hk
  norm_num [candidateEndpointStart, candidateEndpointSize] at hj hk
  constructor
  · intro h
    dsimp [candidateEndpointBaseRat, candidateEndpointShiftRat, candidateEndpointSlopeRat] at h
    have hq : (743 : ℚ) * j = 557 * (2 * k - 1) := by linarith
    have hz : (743 : ℤ) * j = 557 * (2 * k - 1) := by exact_mod_cast hq
    omega
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
      norm_num [candidateEndpointBaseRat, candidateEndpointShiftRat, candidateEndpointSlopeRat]

end PiIrrationality
