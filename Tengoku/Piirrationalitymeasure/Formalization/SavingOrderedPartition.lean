import Tengoku.Piirrationalitymeasure.Formalization.EndpointUniformOrder
import Tengoku.Piirrationalitymeasure.Formalization.FiniteEndpointPartition
import Tengoku.Piirrationalitymeasure.Formalization.SavingEndpointComparison

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! A fixed ordered endpoint enumeration gives an exact partition of the actual measure. -/

set_option maxRecDepth 100000

namespace PiIrrationality

open MeasureTheory Set

abbrev CandidateEndpointEnumeration :=
  Fin (Fintype.card CandidateEndpointLabel) ≃ CandidateEndpointLabel

def CandidateOrderedEndpoints (e : CandidateEndpointEnumeration) (z : ℝ × ℝ) : Prop :=
  StrictMono (fun k => candidateEndpointPosition z (e k)) ∧
    ∀ k, candidateEndpointPosition z (e k) ∈
      Ioo (candidateEndpointCut : ℝ) ((candidateEndpointCut : ℝ) + 1)

noncomputable def candidateEndpointPartition (e : CandidateEndpointEnumeration)
    (z : ℝ × ℝ) (k : ℕ) : ℝ :=
  finiteEndpointPartition candidateEndpointCut ((candidateEndpointCut : ℝ) + 1)
    (fun j => candidateEndpointPosition z (e j)) k

def candidateEndpointCell (e : CandidateEndpointEnumeration) (z : ℝ × ℝ) (k : ℕ) : Set ℝ :=
  Ioo (candidateEndpointPartition e z k) (candidateEndpointPartition e z (k + 1))

noncomputable def candidatePartitionIndicator (e : CandidateEndpointEnumeration)
    (z : ℝ × ℝ) (k : ℕ) : ℝ :=
  translatedSavingChi 1857 3714 5570 z
    ((candidateEndpointPartition e z k + candidateEndpointPartition e z (k + 1)) / 2)

/--
@isnad1 id=ex.1h2v.s5.8d0e8ff26491 from=translated src=- shape=d4dee35f vocab=35f32eeb
-/
theorem candidateEndpointLabel_exists (T : SavingEndpointType) (j : ℤ)
    (hj : j ∈ candidateEndpointIndices T) :
    ∃ p : CandidateEndpointLabel, p.1 = T ∧ candidateEndpointLabelIndex p = j := by
  obtain ⟨hlo, hhi⟩ := (mem_candidateEndpointIndices T j).mp hj
  refine ⟨⟨T, ⟨(j - candidateEndpointStart T).toNat, by omega⟩⟩, rfl, ?_⟩
  dsimp [candidateEndpointLabelIndex]
  omega

/--
@isnad1 id=eq.0h2v.s4.359acf39e01b from=translated src=- shape=37c2d80e vocab=d1f32187
-/
theorem candidateEndpointPartition_zero (e : CandidateEndpointEnumeration) (z : ℝ × ℝ) :
    candidateEndpointPartition e z 0 = (candidateEndpointCut : ℝ) :=
  finiteEndpointPartition_zero _ _ _

/--
@isnad1 id=eq.0h2v.s5.075ff280d2ba from=translated src=- shape=bb4ca15e vocab=35fae93d
-/
theorem candidateEndpointPartition_last (e : CandidateEndpointEnumeration) (z : ℝ × ℝ) :
    candidateEndpointPartition e z (Fintype.card CandidateEndpointLabel + 1) =
      (candidateEndpointCut : ℝ) + 1 :=
  finiteEndpointPartition_last _ _ _

/--
@isnad1 id=monotone.1h2v.s4.af8df23d6bfe from=translated src=- shape=84c6d184 vocab=d6b1bcc0
-/
theorem candidateEndpointPartition_monotone {e : CandidateEndpointEnumeration} {z : ℝ × ℝ}
    (hz : CandidateOrderedEndpoints e z) : Monotone (candidateEndpointPartition e z) :=
  finiteEndpointPartition_monotone (by linarith) hz.1.monotone
    (fun k => ⟨(hz.2 k).1.le, (hz.2 k).2.le⟩)

/--
@isnad1 id=lt.2h3v.s6.1d839b06a8c4 from=translated src=- shape=4f3a0496 vocab=fe0fbcfa
-/
theorem candidateEndpointPartition_adjacent_lt {e : CandidateEndpointEnumeration} {z : ℝ × ℝ}
    (hz : CandidateOrderedEndpoints e z) {k : ℕ} (hk : k < Fintype.card CandidateEndpointLabel + 1) :
    candidateEndpointPartition e z k < candidateEndpointPartition e z (k + 1) :=
  finiteEndpointPartition_adjacent_lt (by linarith) hz.1 hz.2 k hk

/--
@isnad1 id=le.2h3v.s6.b3ee5f772ef5 from=translated src=- shape=37122e94 vocab=bfeaa58a
-/
theorem candidateEndpointCell_subset {e : CandidateEndpointEnumeration} {z : ℝ × ℝ}
    (hz : CandidateOrderedEndpoints e z) {k : ℕ} (hk : k < Fintype.card CandidateEndpointLabel + 1) :
    candidateEndpointCell e z k ⊆
      Ioo (candidateEndpointCut : ℝ) ((candidateEndpointCut : ℝ) + 1) :=
  finiteEndpointPartition_cell_subset (by linarith) hz.1.monotone
    (fun k => ⟨(hz.2 k).1.le, (hz.2 k).2.le⟩) hk

/--
@isnad1 id=mem.2h3v.s6.6461f5e3ef2d from=translated src=- shape=8d084287 vocab=91542b00
-/
theorem candidateEndpointCell_midpoint {e : CandidateEndpointEnumeration} {z : ℝ × ℝ}
    (hz : CandidateOrderedEndpoints e z) {k : ℕ} (hk : k < Fintype.card CandidateEndpointLabel + 1) :
    (candidateEndpointPartition e z k + candidateEndpointPartition e z (k + 1)) / 2 ∈
      candidateEndpointCell e z k := by
  have h := candidateEndpointPartition_adjacent_lt hz hk
  constructor <;> linarith

/--
@isnad1 id=iff.5h8v.s7.e789617c72cc from=translated src=- shape=be898753 vocab=db1224a3
-/
theorem candidateEndpointCell_comparisons {e : CandidateEndpointEnumeration} {z w : ℝ × ℝ}
    (hz : CandidateOrderedEndpoints e z) (hw : CandidateOrderedEndpoints e w)
    {k : ℕ} {u v : ℝ} (hu : u ∈ candidateEndpointCell e z k)
    (hv : v ∈ candidateEndpointCell e w k) :
    ∀ T : SavingEndpointType, ∀ j ∈ candidateEndpointIndices T,
      savingEndpoint 1857 3714 5570 z T j ≤ u ↔ savingEndpoint 1857 3714 5570 w T j ≤ v := by
  intro T j hj
  obtain ⟨p, hT, hjp⟩ := candidateEndpointLabel_exists T j hj
  have hzu := finiteEndpointPartition_prefix (by linarith) hz.1.monotone
    (fun k => ⟨(hz.2 k).1.le, (hz.2 k).2.le⟩) hu (e.symm p)
  have hwv := finiteEndpointPartition_prefix (by linarith) hw.1.monotone
    (fun k => ⟨(hw.2 k).1.le, (hw.2 k).2.le⟩) hv (e.symm p)
  simpa only [Equiv.apply_symm_apply, candidateEndpointPosition, hT, hjp] using hzu.trans hwv.symm

/--
@isnad1 id=eq.6h5v.s7.1e4c7d34bbcd from=translated src=- shape=bb571bc8 vocab=2ea0a06c
-/
theorem translatedSavingChi_eq_partitionIndicator
    {e : CandidateEndpointEnumeration} {z w : ℝ × ℝ}
    (hz : CandidateOrderedEndpoints e z) (hw : CandidateOrderedEndpoints e w)
    (hzn : parameterNormOne z ≤ 1 / 100) (hwn : parameterNormOne w ≤ 1 / 100)
    {k : ℕ} (hk : k < Fintype.card CandidateEndpointLabel + 1)
    {u : ℝ} (hu : u ∈ candidateEndpointCell e z k) :
    translatedSavingChi 1857 3714 5570 z u = candidatePartitionIndicator e w k := by
  have hmid := candidateEndpointCell_midpoint hw hk
  exact translatedSavingChi_eq_of_endpoint_comparisons hzn hwn
    (candidateEndpointCell_subset hz hk hu) (candidateEndpointCell_subset hw hk hmid)
    (candidateEndpointCell_comparisons hz hw hu hmid)

/--
@isnad1 id=eq.4h3v.s7.f40ae905213d from=translated src=- shape=de727bd7 vocab=f7de607d
-/
theorem translatedSavingMeasure_eq_partition_sum
    {e : CandidateEndpointEnumeration} {z w : ℝ × ℝ}
    (hz : CandidateOrderedEndpoints e z) (hw : CandidateOrderedEndpoints e w)
    (hzn : parameterNormOne z ≤ 1 / 100) (hwn : parameterNormOne w ≤ 1 / 100) :
    translatedSavingMeasure 1857 3714 5570 z =
      ∑ k ∈ Finset.range (Fintype.card CandidateEndpointLabel + 1),
        candidatePartitionIndicator e w k *
          (candidateEndpointPartition e z (k + 1) - candidateEndpointPartition e z k) := by
  have hi := finite_step_integral (candidateEndpointPartition e z) (candidatePartitionIndicator e w)
    (translatedSavingChi 1857 3714 5570 z) (Fintype.card CandidateEndpointLabel + 1)
    (fun k hk => (candidateEndpointPartition_adjacent_lt hz hk).le)
    (fun _ hk _ hu => translatedSavingChi_eq_partitionIndicator hz hw hzn hwn hk hu)
  rw [candidateEndpointPartition_zero, candidateEndpointPartition_last] at hi
  have hp := translatedSavingMeasure_eq_period (1857 : ℤ) 3714 5570 z candidateEndpointCut
  norm_num only [Int.cast_ofNat] at hp
  exact hp.trans hi

end PiIrrationality
