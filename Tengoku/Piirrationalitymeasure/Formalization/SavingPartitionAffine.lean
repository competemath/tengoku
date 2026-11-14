import Tengoku.Piirrationalitymeasure.Formalization.EndpointUniformEnumeration

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Affine dependence of the exact finite partition integral on the translation. -/

set_option maxRecDepth 100000

namespace PiIrrationality

noncomputable def candidatePartitionVelocity (e : CandidateEndpointEnumeration)
    (z : ℝ × ℝ) (k : ℕ) : ℝ :=
  finiteEndpointPartition 0 0
    (fun j => savingEndpointVelocity 1857 3714 5570 z (e j).1) k

noncomputable def candidatePartitionConstant (e : CandidateEndpointEnumeration)
    (eps : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.range (Fintype.card CandidateEndpointLabel + 1),
    eps k * (candidateEndpointPartition e 0 (k + 1) - candidateEndpointPartition e 0 k)

noncomputable def candidatePartitionLinear (e : CandidateEndpointEnumeration)
    (eps : ℕ → ℝ) (z : ℝ × ℝ) : ℝ :=
  ∑ k ∈ Finset.range (Fintype.card CandidateEndpointLabel + 1),
    eps k * (candidatePartitionVelocity e z (k + 1) - candidatePartitionVelocity e z k)

/--
@isnad1 id=eq.0h3v.s5.655055cdbc6f from=translated src=- shape=dfd38d37 vocab=b67bc738
-/
theorem candidateEndpointPartition_affine (e : CandidateEndpointEnumeration) (z : ℝ × ℝ) (k : ℕ) :
    candidateEndpointPartition e z k =
      candidateEndpointPartition e 0 k + candidatePartitionVelocity e z k := by
  unfold candidateEndpointPartition candidatePartitionVelocity finiteEndpointPartition
  by_cases hk : k = 0
  · simp only [ite_eq_left hk, add_zero]
  · simp only [ite_eq_right hk]
    split_ifs with hn
    · exact candidateEndpointPosition_eq_base_add z (e ⟨k - 1, hn⟩)
    · simp only [add_zero]

/--
@isnad1 id=eq.0h6v.s6.88f2f79b9f46 from=translated src=- shape=df9a2ada vocab=444b99c4
-/
theorem candidatePartitionVelocity_add_smul (e : CandidateEndpointEnumeration)
    (v w : ℝ × ℝ) (s t : ℝ) (k : ℕ) :
    candidatePartitionVelocity e (s • v + t • w) k =
      s * candidatePartitionVelocity e v k + t * candidatePartitionVelocity e w k := by
  unfold candidatePartitionVelocity finiteEndpointPartition
  by_cases hk : k = 0
  · simp only [ite_eq_left hk, mul_zero, add_zero]
  · simp only [ite_eq_right hk]
    split_ifs with hn
    · exact savingEndpointVelocity_add_smul 1857 3714 5570 v w s t (e ⟨k - 1, hn⟩).1
    · simp only [mul_zero, add_zero]

/--
@isnad1 id=eq.0h6v.s6.ea708e4aade8 from=translated src=- shape=dbccf980 vocab=1a2ac8f6
-/
theorem candidatePartitionLinear_add_smul (e : CandidateEndpointEnumeration) (eps : ℕ → ℝ)
    (v w : ℝ × ℝ) (s t : ℝ) :
    candidatePartitionLinear e eps (s • v + t • w) =
      s * candidatePartitionLinear e eps v + t * candidatePartitionLinear e eps w := by
  unfold candidatePartitionLinear
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [candidatePartitionVelocity_add_smul, candidatePartitionVelocity_add_smul]
  ring

/--
@isnad1 id=eq.0h4v.s5.bf8d0e4e94d5 from=translated src=- shape=058d3f73 vocab=6a0bd2af
-/
theorem candidatePartitionLinear_smul (e : CandidateEndpointEnumeration) (eps : ℕ → ℝ)
    (v : ℝ × ℝ) (s : ℝ) :
    candidatePartitionLinear e eps (s • v) = s * candidatePartitionLinear e eps v := by
  simpa only [zero_smul, add_zero, zero_mul] using
    candidatePartitionLinear_add_smul e eps v 0 s 0

/--
@isnad1 id=eq.4h3v.s6.dc9d219a3456 from=translated src=- shape=1c59c797 vocab=ffa7afd3
-/
theorem translatedSavingMeasure_eq_partition_affine
    {e : CandidateEndpointEnumeration} {z w : ℝ × ℝ}
    (hz : CandidateOrderedEndpoints e z) (hw : CandidateOrderedEndpoints e w)
    (hzn : parameterNormOne z ≤ 1 / 100) (hwn : parameterNormOne w ≤ 1 / 100) :
    translatedSavingMeasure 1857 3714 5570 z =
      candidatePartitionConstant e (candidatePartitionIndicator e w) +
        candidatePartitionLinear e (candidatePartitionIndicator e w) z := by
  rw [translatedSavingMeasure_eq_partition_sum hz hw hzn hwn]
  unfold candidatePartitionConstant candidatePartitionLinear
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [candidateEndpointPartition_affine e z (k + 1), candidateEndpointPartition_affine e z k]
  ring

end PiIrrationality
