import Tengoku.Piirrationalitymeasure.Formalization.SavingPartitionAffine

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The partition's linear term as a sum of signed jumps over the original endpoint labels. -/

set_option maxRecDepth 100000

namespace PiIrrationality

noncomputable def candidatePartitionJump (e : CandidateEndpointEnumeration)
    (eps : ℕ → ℝ) (p : CandidateEndpointLabel) : ℝ :=
  eps (e.symm p).val - eps ((e.symm p).val + 1)

/--
@isnad1 id=eq.0h2v.s4.0ed3044c8282 from=translated src=- shape=06cc5369 vocab=9b97273c
-/
theorem candidatePartitionVelocity_zero (e : CandidateEndpointEnumeration) (z : ℝ × ℝ) :
    candidatePartitionVelocity e z 0 = 0 := finiteEndpointPartition_zero _ _ _

/--
@isnad1 id=eq.0h2v.s5.bcd61ff65e8d from=translated src=- shape=69fd94ce vocab=526714bc
-/
theorem candidatePartitionVelocity_last (e : CandidateEndpointEnumeration) (z : ℝ × ℝ) :
    candidatePartitionVelocity e z (Fintype.card CandidateEndpointLabel + 1) = 0 :=
  finiteEndpointPartition_last _ _ _

/--
@isnad1 id=eq.0h3v.s7.fc7350ecc828 from=translated src=- shape=81f74340 vocab=e2cf004a
-/
theorem candidatePartitionVelocity_internal (e : CandidateEndpointEnumeration) (z : ℝ × ℝ)
    (k : Fin (Fintype.card CandidateEndpointLabel)) :
    candidatePartitionVelocity e z (k.val + 1) =
      savingEndpointVelocity 1857 3714 5570 z (e k).1 :=
  finiteEndpointPartition_internal _ _ _ k

/--
@isnad1 id=eq.0h4v.s5.0ef7a4caf426 from=translated src=- shape=ba790fa3 vocab=8a909870
-/
theorem candidatePartitionVelocity_smul (e : CandidateEndpointEnumeration) (z : ℝ × ℝ)
    (s : ℝ) (k : ℕ) :
    candidatePartitionVelocity e (s • z) k = s * candidatePartitionVelocity e z k := by
  simpa only [zero_smul, add_zero, zero_mul] using
    candidatePartitionVelocity_add_smul e z 0 s 0 k

/--
@isnad1 id=eq.0h4v.s6.33ca98d4df43 from=translated src=- shape=af70e54c vocab=c5503ea2
-/
theorem candidateEndpointPartition_smul (e : CandidateEndpointEnumeration) (z : ℝ × ℝ)
    (s : ℝ) (k : ℕ) :
    candidateEndpointPartition e (s • z) k =
      candidateEndpointPartition e 0 k + s * candidatePartitionVelocity e z k := by
  rw [candidateEndpointPartition_affine, candidatePartitionVelocity_smul]

/--
@isnad1 id=eq.0h3v.s6.2e2115f7c967 from=translated src=- shape=acf1dc5c vocab=acfa2006
-/
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

/--
@isnad1 id=eq.0h1v.s5.43030d0e0ab9 from=translated src=- shape=cb31552f vocab=73745678
-/
theorem candidateEndpointLabel_sum (f : SavingEndpointType → ℤ → ℝ) :
    (∑ p : CandidateEndpointLabel, f p.1 (candidateEndpointLabelIndex p)) =
      ∑ T : SavingEndpointType, ∑ j ∈ candidateEndpointIndices T, f T j := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro T _
  simp only [candidateEndpointIndices, Finset.sum_map, Finset.sum_range]
  rfl

/--
@isnad1 id=eq.0h1v.s5.281fa9ccab7a from=translated src=- shape=66362361 vocab=e5431e58
-/
theorem sum_savingEndpointType (f : SavingEndpointType → ℝ) :
    (∑ T : SavingEndpointType, f T) = f .A + f .B + f .C + f .Q := by
  change (∑ T ∈ ({.A, .B, .C, .Q} : Finset SavingEndpointType), f T) = _
  simp [add_assoc]

end PiIrrationality
