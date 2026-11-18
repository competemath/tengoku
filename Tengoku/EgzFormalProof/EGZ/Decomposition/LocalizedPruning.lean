import Tengoku.EgzFormalProof.EGZ.Decomposition.GapCleanup
import Tengoku.EgzFormalProof.EGZ.Decomposition.Pullback
import Tengoku.EgzFormalProof.EGZ.Decomposition.SlabPruning

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Pruning only below one node

Restrict the local weights below an anchor to a fixed set of ambient points.
The lost total mass is exactly the lost cumulative mass at the anchor. The
surviving weights can be rebuilt using the geometric pruning construction.
-/

open scoped BigOperators
open Classical

namespace EGZ.FlagDecomposition.LocalizedPruning

variable {p d : ℕ} [NeZero p] {f : FpCoord p d → ℕ}
    (Φ : FlagDecomposition p d f) (anchor : Φ.flag.Node) (S : Set (FpCoord p d))

noncomputable def weight (y : Φ.flag.Node) (v : FpCoord p d) : ℕ :=
  if y ≤ anchor then restrictWeight (Φ.localWeight y) S v else Φ.localWeight y v

/--
@isnad1 id=le.0h8v.s6.3c123741b510 from=translated src=- shape=877d0b5a vocab=aeef54bd
-/
theorem weight_le (y : Φ.flag.Node) (v : FpCoord p d) :
    weight Φ anchor S y v ≤ Φ.localWeight y v := by
  unfold weight
  split_ifs
  · exact restrictWeight_le _ _ v
  · exact le_rfl

/--
@isnad1 id=eq.1h8v.s6.d115585f2d1e from=translated src=- shape=42e36713 vocab=ea316677
-/
theorem cumulative_below (y : Φ.flag.Node) (hy : y ≤ anchor) (v : FpCoord p d) :
    FlagDecompositionRaw.cumulativeWeight (weight Φ anchor S) y v =
      restrictWeight (Φ.cumulativeWeight y) S v := by
  unfold FlagDecompositionRaw.cumulativeWeight restrictWeight
  by_cases hv : v ∈ S
  · rw [ite_eq_left hv]
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz : z ≤ y
    · simp only [weight, hz, ite_eq_left, hz.trans hy, restrictWeight, hv]
    · simp only [ite_eq_right hz]
  · rw [ite_eq_right hv]
    apply Finset.sum_eq_zero
    intro z _
    by_cases hz : z ≤ y
    · simp only [weight, hz, ite_eq_left, hz.trans hy, restrictWeight, ite_eq_right hv]
    · simp only [ite_eq_right hz]

/--
@isnad1 id=le.0h7v.s6.9c2bf1a5c7ca from=translated src=- shape=63307a27 vocab=1552ef36
-/
theorem retainedWeight_le (v : FpCoord p d) :
    FlagDecompositionRaw.retainedWeight (weight Φ anchor S) v ≤ Φ.retainedWeight v :=
  Finset.sum_le_sum fun y _ ↦ weight_le Φ anchor S y v

/-- At every ambient point, all loss occurs in the cumulative summand at the
anchor and is exactly its excluded part.
@isnad1 id=eq.0h7v.s6.ece6dfa87450 from=translated src=- shape=925c489a vocab=4a6bbef2
-/
theorem retainedWeight_loss (v : FpCoord p d) :
    Φ.retainedWeight v - FlagDecompositionRaw.retainedWeight (weight Φ anchor S) v =
      Φ.cumulativeWeight anchor v - restrictWeight (Φ.cumulativeWeight anchor) S v := by
  change (∑ y, Φ.localWeight y v) - ∑ y, weight Φ anchor S y v = _
  rw [← Finset.sum_tsub_distrib _ (fun y _ ↦ weight_le Φ anchor S y v)]
  by_cases hv : v ∈ S
  · simp only [restrictWeight, ite_eq_left hv, Nat.sub_self]
    apply Finset.sum_eq_zero
    intro y _
    simp [weight, restrictWeight, hv]
  · simp only [restrictWeight, ite_eq_right hv, Nat.sub_zero]
    change (∑ y, (Φ.localWeight y v - weight Φ anchor S y v)) =
      ∑ y, if y ≤ anchor then Φ.localWeight y v else 0
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : y ≤ anchor <;> simp [weight, hy, restrictWeight, hv]

/--
@isnad1 id=eq.0h6v.s7.3ebfad12f817 from=translated src=- shape=94449877 vocab=1769bc65
-/
theorem retainedMass_loss :
    Φ.retainedMass - natMass (FlagDecompositionRaw.retainedWeight (weight Φ anchor S)) =
      natMass (Φ.cumulativeWeight anchor) - natMass (restrictWeight (Φ.cumulativeWeight anchor) S) := by
  unfold FlagDecomposition.retainedMass
  rw [← natMass_sub (retainedWeight_le Φ anchor S)]
  simp_rw [retainedWeight_loss Φ anchor S]
  exact natMass_sub (restrictWeight_le _ _)

variable (hne : ∃ v, restrictWeight (Φ.cumulativeWeight anchor) S v ≠ 0)

include hne

/--
@isnad1 id=ex.1h6v.s6.a7c953dbbb74 from=translated src=- shape=de245a89 vocab=a19a3df8
-/
theorem nonzero : ∃ y v, weight Φ anchor S y v ≠ 0 := by
  obtain ⟨v, hv⟩ := hne
  have hc : FlagDecompositionRaw.cumulativeWeight (weight Φ anchor S) anchor v ≠ 0 := by
    rwa [cumulative_below Φ anchor S anchor le_rfl v]
  obtain ⟨y, _, hy⟩ := (FlagDecompositionRaw.cumulative_ne_zero_iff
    (F := Φ.flag) (weight Φ anchor S) anchor v).mp hc
  exact ⟨y, v, hy⟩

/-- The surviving local weights, ready for geometric rebuilding.-/
noncomputable abbrev prunedWeights : Φ.PrunedWeights where
  weight := weight Φ anchor S
  weight_le := weight_le Φ anchor S
  nonzero := nonzero Φ anchor S hne

variable (hp : Odd p)

noncomputable abbrev decomposition : FlagDecomposition p d f :=
  (prunedWeights Φ anchor S hne).rebuilt hp

/--
@isnad1 id=active.2h6v.s6.acad8628e9d9 from=translated src=- shape=9bb09019 vocab=34024fdd
-/
theorem active_anchor :
    ((prunedWeights Φ anchor S hne).rebuildData hp).Active anchor := by
  obtain ⟨v, hv⟩ := hne
  have hc : FlagDecompositionRaw.cumulativeWeight (weight Φ anchor S) anchor v ≠ 0 := by
    rwa [cumulative_below Φ anchor S anchor le_rfl v]
  obtain ⟨y, hy, hw⟩ := (FlagDecompositionRaw.cumulative_ne_zero_iff
    (F := Φ.flag) (weight Φ anchor S) anchor v).mp hc
  exact ⟨y, hy, v, hw⟩

def anchorNode : (decomposition Φ anchor S hne hp).flag.Node :=
  ⟨anchor, active_anchor Φ anchor S hne hp⟩

/--
@isnad1 id=eq.2h6v.s6.96dfface4df2 from=translated src=- shape=599aabc9 vocab=51534bab
-/
@[simp]
theorem cumulativeWeight_anchorNode :
    (decomposition Φ anchor S hne hp).cumulativeWeight (anchorNode Φ anchor S hne hp) =
      restrictWeight (Φ.cumulativeWeight anchor) S := by
  rw [(prunedWeights Φ anchor S hne).rebuildData hp |>.decomposition_cumulativeWeight]
  exact funext (cumulative_below Φ anchor S anchor le_rfl)

/--
@isnad1 id=eq.3h7v.s8.b35bdf621f66 from=translated src=- shape=66e54385 vocab=300b1201
-/
theorem cumulativeWeight_below (x : (decomposition Φ anchor S hne hp).flag.Node)
    (hx : x ≤ anchorNode Φ anchor S hne hp) :
    (decomposition Φ anchor S hne hp).cumulativeWeight x =
      restrictWeight (Φ.cumulativeWeight x.1) S := by
  rw [((prunedWeights Φ anchor S hne).rebuildData hp).decomposition_cumulativeWeight x]
  exact funext (cumulative_below Φ anchor S x.1 hx)

/--
@isnad1 id=eq.2h6v.s7.b4d441ff10b9 from=translated src=- shape=d634e3f7 vocab=6f76009a
-/
theorem decomposition_retainedMass_loss :
    (Φ.retainedMass : ℝ) - (decomposition Φ anchor S hne hp).retainedMass =
      (natMass (Φ.cumulativeWeight anchor) : ℝ) -
        natMass (restrictWeight (Φ.cumulativeWeight anchor) S) := by
  have hmass := retainedMass_loss Φ anchor S
  have htotal : natMass (FlagDecompositionRaw.retainedWeight (weight Φ anchor S)) ≤ Φ.retainedMass :=
    natMass_mono (retainedWeight_le Φ anchor S)
  have hselected := natMass_mono (restrictWeight_le (Φ.cumulativeWeight anchor) S)
  have hreal := congrArg (fun n : ℕ ↦ (n : ℝ)) hmass
  rw [Nat.cast_sub htotal, Nat.cast_sub hselected] at hreal
  have hret : (decomposition Φ anchor S hne hp).retainedWeight =
      FlagDecompositionRaw.retainedWeight (weight Φ anchor S) :=
    ((prunedWeights Φ anchor S hne).rebuildData hp).decomposition_retainedWeight
  simpa only [FlagDecomposition.retainedMass, hret] using hreal

end EGZ.FlagDecomposition.LocalizedPruning
