import Tengoku.Piirrationalitymeasure.Formalization.SavingPartitionAffine

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The partition's linear term as a sum of signed jumps over the original endpoint labels. -/

set_option maxRecDepth 100000

namespace PiIrrationality

noncomputable def candidatePartitionJump (e : CandidateEndpointEnumeration)
    (eps : ℕ → ℝ) (p : CandidateEndpointLabel) : ℝ :=
  eps (e.symm p).val - eps ((e.symm p).val + 1)

theorem candidatePartitionVelocity_zero (e : CandidateEndpointEnumeration) (z : ℝ × ℝ) :
    candidatePartitionVelocity e z 0 = 0 := finiteEndpointPartition_zero _ _ _

theorem candidatePartitionVelocity_last (e : CandidateEndpointEnumeration) (z : ℝ × ℝ) :
    candidatePartitionVelocity e z (Fintype.card CandidateEndpointLabel + 1) = 0 :=
  finiteEndpointPartition_last _ _ _

theorem candidatePartitionVelocity_internal (e : CandidateEndpointEnumeration) (z : ℝ × ℝ)
    (k : Fin (Fintype.card CandidateEndpointLabel)) :
    candidatePartitionVelocity e z (k.val + 1) =
      savingEndpointVelocity 1857 3714 5570 z (e k).1 :=
  finiteEndpointPartition_internal _ _ _ k

theorem candidatePartitionVelocity_smul (e : CandidateEndpointEnumeration) (z : ℝ × ℝ)
    (s : ℝ) (k : ℕ) :
    candidatePartitionVelocity e (s • z) k = s * candidatePartitionVelocity e z k := by
  simpa only [zero_smul, add_zero, zero_mul] using
    candidatePartitionVelocity_add_smul e z 0 s 0 k

theorem candidateEndpointPartition_smul (e : CandidateEndpointEnumeration) (z : ℝ × ℝ)
    (s : ℝ) (k : ℕ) :
    candidateEndpointPartition e (s • z) k =
      candidateEndpointPartition e 0 k + s * candidatePartitionVelocity e z k := by
  rw [candidateEndpointPartition_affine, candidatePartitionVelocity_smul]

theorem candidatePartitionLinear_eq_label_sum (e : CandidateEndpointEnumeration) (eps : ℕ → ℝ)
    (z : ℝ × ℝ) :
    candidatePartitionLinear e eps z =
      ∑ p : CandidateEndpointLabel,
        candidatePartitionJump e eps p * savingEndpointVelocity 1857 3714 5570 z p.1 := by
  unfold candidatePartitionLinear
  rw [finite_step_jump_sum_fixed_boundary eps (candidatePartitionVelocity e z)
    (Fintype.card CandidateEndpointLabel) (candidatePartitionVelocity_zero e z)
      (candidatePartitionVelocity_last e z), Finset.sum_range]
  apply Fintype.sum_equiv e
  intro k
  rw [candidatePartitionVelocity_internal]
  simp only [candidatePartitionJump, Equiv.symm_apply_apply]

theorem candidateEndpointLabel_sum (f : SavingEndpointType → ℤ → ℝ) :
    (∑ p : CandidateEndpointLabel, f p.1 (candidateEndpointLabelIndex p)) =
      ∑ T : SavingEndpointType, ∑ j ∈ candidateEndpointIndices T, f T j := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro T _
  simp only [candidateEndpointIndices, Finset.sum_map, Finset.sum_range]
  rfl

theorem sum_savingEndpointType (f : SavingEndpointType → ℝ) :
    (∑ T : SavingEndpointType, f T) = f .A + f .B + f .C + f .Q := by
  change (∑ T ∈ ({.A, .B, .C, .Q} : Finset SavingEndpointType), f T) = _
  simp [add_assoc]

end PiIrrationality
