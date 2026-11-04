import Tengoku.EntropyConstrainedMissingMass.EntropyConstrainedMissingMass.Probability
import Tengoku.EntropyConstrainedMissingMass.EntropyConstrainedMissingMass.BranchEntropy
import Tengoku.EntropyConstrainedMissingMass.EntropyConstrainedMissingMass.CertificateBounds
import Tengoku.EntropyConstrainedMissingMass.EntropyConstrainedMissingMass.Reindex
import Tengoku.Seed.Data.Fin.Tuple.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Genuine probability vectors realizing the manuscript's one-exceptional-atom branches. -/

namespace EntropyConstrainedMissingMass

noncomputable section

open scoped ENNReal
open Set

/-- The distinguished coordinate is zero; all other coordinates have equal mass.-/
def candidateCoord (m : ℕ) (z : ℝ) : Fin (m + 1) → ℝ :=
  Fin.cases z (fun _ => (1 - z) / (m : ℝ))

/--
@isnad1 id=eq.0h2v.s5.73ca83c982a6 from=translated src=- shape=8f8700b0 vocab=fb762cf4
-/
@[simp] theorem candidateCoord_zero (m : ℕ) (z : ℝ) : candidateCoord m z 0 = z := rfl

/--
@isnad1 id=eq.0h3v.s5.c2e86d8fc7fd from=translated src=- shape=564923c1 vocab=b514fab0
-/
@[simp] theorem candidateCoord_succ (m : ℕ) (z : ℝ) (i : Fin m) :
    candidateCoord m z i.succ = (1 - z) / (m : ℝ) := rfl

/--
@isnad1 id=eq.1h2v.s6.5a0d09b0896d from=translated src=- shape=3e815552 vocab=ebaae53c
-/
theorem sum_candidateCoord {m : ℕ} (hm : 0 < m) (z : ℝ) :
    ∑ i, candidateCoord m z i = 1 := by
  rw [Fin.sum_univ_succ]
  simp only [candidateCoord_zero, candidateCoord_succ, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  field_simp
  ring

/--
@isnad1 id=le.1h3v.s5.6fa20dc9df33 from=translated src=- shape=4d3cb4c6 vocab=f6ad3df5
-/
theorem candidateCoord_nonneg {m : ℕ} {z : ℝ} (hz : z ∈ Icc 0 1)
    (i : Fin (m + 1)) : 0 ≤ candidateCoord m z i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hz.1
  · exact div_nonneg (sub_nonneg.mpr hz.2) (Nat.cast_nonneg _)

/--
@isnad1 id=hassum.1h2v.s5.a08e4dccb6d1 from=translated src=- shape=14489330 vocab=05ae8afc
-/
theorem hasSum_candidateCoord {m : ℕ} (hm : 0 < m) (z : ℝ) :
    HasSum (candidateCoord m z) 1 := by
  simpa only [sum_candidateCoord hm] using hasSum_fintype (candidateCoord m z)

/-- The finite candidate law with one exceptional mass and `m` repeated masses.-/
def candidateVector (m : ℕ) (z : ℝ) (hm : 0 < m) (hz : z ∈ Icc 0 1) :
    ProbabilityVector (Fin (m + 1)) :=
  ProbabilityVector.ofHasSum (candidateCoord m z) (candidateCoord_nonneg hz)
    (hasSum_candidateCoord hm z)

/--
@isnad1 id=eq.2h2v.s6.5724ec6ed394 from=translated src=- shape=c7f1ba90 vocab=e6adce28
-/
@[simp] theorem coord_candidateVector (m : ℕ) (z : ℝ) (hm : 0 < m)
    (hz : z ∈ Icc 0 1) : (candidateVector m z hm hz).coord = candidateCoord m z := rfl

/--
@isnad1 id=eq.1h2v.s6.dcae62722f06 from=translated src=- shape=dffc0545 vocab=e9984d11
-/
theorem sum_negMulLog_candidateCoord {m : ℕ} (hm : 0 < m) (z : ℝ) :
    (∑ i, Real.negMulLog (candidateCoord m z i)) = branchEntropy m z := by
  rw [Fin.sum_univ_succ]
  simp only [candidateCoord_zero, candidateCoord_succ, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Real.negMulLog, branchEntropy]
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  field_simp
  ring

/--
@isnad1 id=eq.2h2v.s6.2febd5206fc8 from=translated src=- shape=3bb58ded vocab=add24f42
-/
theorem entropy_candidateVector (m : ℕ) (z : ℝ) (hm : 0 < m)
    (hz : z ∈ Icc 0 1) :
    (candidateVector m z hm hz).entropy = ENNReal.ofReal (branchEntropy m z) := by
  have hp : (candidateVector m z hm hz).entropy ≠ ⊤ :=
    (ProbabilityVector.entropy_ne_top_iff _).2 (hasSum_fintype _).summable
  rw [ProbabilityVector.entropy_eq_ofReal_tsum _ hp, coord_candidateVector,
    tsum_fintype, sum_negMulLog_candidateCoord hm]

/--
@isnad1 id=eq.2h3v.s6.b709b33422b9 from=translated src=- shape=524f8b61 vocab=19a8ee77
-/
theorem objective_candidateVector (m t : ℕ) (z : ℝ) (hm : 0 < m)
    (hz : z ∈ Icc 0 1) :
    (candidateVector m z hm hz).objective t = branchObjective m t z := by
  rw [ProbabilityVector.objective, coord_candidateVector, tsum_fintype, Fin.sum_univ_succ]
  simp only [candidateCoord_zero, candidateCoord_succ, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, missingMassTerm, branchObjective]
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  field_simp

/-- The uniform meeting point has `m+1` identical coordinates.
@isnad1 id=eq.1h2v.s6.a847e5d8478e from=translated src=- shape=378c2852 vocab=1f62364e
-/
theorem candidateCoord_uniform {m : ℕ} (hm : 0 < m) (i : Fin (m + 1)) :
    candidateCoord m (1 / ((m : ℝ) + 1)) i = 1 / ((m : ℝ) + 1) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp only [candidateCoord_succ]
    have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
    have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring

/--
@isnad1 id=lt.2h3v.s6.ec9b323bfff1 from=translated src=- shape=4d3fa50c vocab=c219c67b
-/
theorem candidateCoord_pos {m : ℕ} (hm : 0 < m) {z : ℝ} (hz : z ∈ Ioo 0 1)
    (i : Fin (m + 1)) : 0 < candidateCoord m z i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hz.1
  · exact div_pos (sub_pos.mpr hz.2) (Nat.cast_pos.mpr hm)

/-- Matching the real branch entropy really does satisfy the extended entropy constraint.
@isnad1 id=mem.3h3v.s6.2209da92ea5c from=translated src=- shape=b1457a91 vocab=56ee1b1a
-/
theorem candidateVector_feasible {m : ℕ} {z h : ℝ} (hm : 0 < m)
    (hz : z ∈ Icc 0 1) (he : branchEntropy m z ≤ h) :
    candidateVector m z hm hz ∈ ProbabilityVector.Feasible h := by
  change (candidateVector m z hm hz).entropy ≤ ENNReal.ofReal h
  rw [entropy_candidateVector]
  exact ENNReal.ofReal_le_ofReal he

/-- The finite candidate's index set is the initial segment of the countable alphabet.-/
def candidateIndexEmbedding (m : ℕ) : Fin (m + 1) ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩

/-- The same candidate as a genuine countably indexed probability vector.-/
def natCandidateVector (m : ℕ) (z : ℝ) (hm : 0 < m) (hz : z ∈ Icc 0 1) :
    ProbabilityVector ℕ :=
  ProbabilityVector.zeroExtend (candidateIndexEmbedding m) (candidateVector m z hm hz)

/--
@isnad1 id=eq.2h3v.s6.c6537a377b4f from=translated src=- shape=ca1ed0f9 vocab=9585f394
-/
@[simp] theorem coord_natCandidateVector (m : ℕ) (z : ℝ) (hm : 0 < m)
    (hz : z ∈ Icc 0 1) (i : Fin (m + 1)) :
    (natCandidateVector m z hm hz).coord i.val = candidateCoord m z i :=
  ProbabilityVector.coord_zeroExtend_apply _ _ i

/--
@isnad1 id=eq.3h3v.s6.0354411ef2cc from=translated src=- shape=7dd47c67 vocab=59f2f584
-/
theorem coord_natCandidateVector_eq_zero (m : ℕ) (z : ℝ) (hm : 0 < m)
    (hz : z ∈ Icc 0 1) (n : ℕ) (hn : m + 1 ≤ n) :
    (natCandidateVector m z hm hz).coord n = 0 := by
  apply ProbabilityVector.coord_zeroExtend_of_not_mem_range
  rintro ⟨i, hi⟩
  have hi' : i.val = n := hi
  exact Nat.not_lt_of_ge hn (hi' ▸ i.isLt)

/--
@isnad1 id=eq.2h2v.s5.f090eac966c9 from=translated src=- shape=ea4375e5 vocab=68ff46fb
-/
@[simp] theorem entropy_natCandidateVector (m : ℕ) (z : ℝ) (hm : 0 < m)
    (hz : z ∈ Icc 0 1) :
    (natCandidateVector m z hm hz).entropy = ENNReal.ofReal (branchEntropy m z) := by
  rw [natCandidateVector, ProbabilityVector.entropy_zeroExtend, entropy_candidateVector]

/--
@isnad1 id=eq.2h3v.s5.db841e3c2b75 from=translated src=- shape=28095880 vocab=89c182ac
-/
@[simp] theorem objective_natCandidateVector (m t : ℕ) (z : ℝ) (hm : 0 < m)
    (hz : z ∈ Icc 0 1) :
    (natCandidateVector m z hm hz).objective t = branchObjective m t z := by
  rw [natCandidateVector, ProbabilityVector.objective_zeroExtend, objective_candidateVector]

/--
@isnad1 id=finite.2h2v.s5.3918db3a829c from=translated src=- shape=c55c9195 vocab=ee29c478
-/
theorem natCandidateVector_finite_support (m : ℕ) (z : ℝ) (hm : 0 < m)
    (hz : z ∈ Icc 0 1) : (Function.support (natCandidateVector m z hm hz).coord).Finite := by
  apply (Set.finite_range (candidateIndexEmbedding m)).subset
  intro n hn
  by_contra hnot
  exact hn (ProbabilityVector.coord_zeroExtend_of_not_mem_range _ _ n hnot)

/--
@isnad1 id=mem.3h3v.s6.44120254b315 from=translated src=- shape=6b479bd7 vocab=6c8cb73f
-/
theorem natCandidateVector_feasible {m : ℕ} {z h : ℝ} (hm : 0 < m)
    (hz : z ∈ Icc 0 1) (he : branchEntropy m z ≤ h) :
    natCandidateVector m z hm hz ∈ ProbabilityVector.Feasible h := by
  change (natCandidateVector m z hm hz).entropy ≤ ENNReal.ofReal h
  rw [entropy_natCandidateVector]
  exact ENNReal.ofReal_le_ofReal he

end

end EntropyConstrainedMissingMass
