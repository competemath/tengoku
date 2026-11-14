import Tengoku.Piirrationalitymeasure.Formalization.ParameterSaving
import Tengoku.Piirrationalitymeasure.Formalization.PeriodicSavingIntegral
import Tengoku.Piirrationalitymeasure.Formalization.PrimeSavingSelection
import Tengoku.Piirrationalitymeasure.Formalization.Normalization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Identification of the continuous saving and the arithmetic saving in (6.5). -/

namespace PiIrrationality

open MeasureTheory Set

/--
@isnad1 id=eq.0h6v.s5.65045818ce7d from=translated src=- shape=b624b0f9 vocab=d1f1237f
-/
theorem savingChi_add_int (X Y Z : ℝ) (m n p : ℤ) :
    savingChi (X + m) (Y + n) (Z + p) = savingChi X Y Z := by
  unfold savingChi
  rw [show X + m + 1 / 2 = (X + 1 / 2) + m by ring]
  simp only [Int.fract_add_intCast]

/--
@isnad1 id=eq.0h5v.s6.20a791fb6137 from=translated src=- shape=82f738f1 vocab=7fd4569e
-/
theorem savingChi_integer_periodic (a b c : ℤ) (k : ℕ) (u : ℝ) :
    savingChi ((a : ℝ) * (k + u)) ((b : ℝ) * (k + u)) ((c : ℝ) * (k + u)) =
      savingChi ((a : ℝ) * u) ((b : ℝ) * u) ((c : ℝ) * u) := by
  have hmul (m : ℤ) : (m : ℝ) * (k + u) =
      (m : ℝ) * u + ((m * (k : ℤ) : ℤ) : ℝ) := by push_cast; ring
  rw [hmul a, hmul b, hmul c, savingChi_add_int]

/--
@isnad1 id=eq.1h1v.s6.f7df4812e6cd from=translated src=- shape=dc46d596 vocab=a06a2b24
-/
theorem savingChi_candidate_indicator {u : ℝ} (hu : u ∈ Ico (0 : ℝ) 1) :
    savingChi (1857 * u) (3714 * u) (5570 * u) =
      primeSavingSet.indicator (fun _ => (1 : ℝ)) u := by
  classical
  have hm : u ∈ primeSavingSet ↔ primeSavingCondition u := by
    simp only [primeSavingSet, mem_ofPred_eq, hu.1, hu.2, true_and]
  simp only [savingChi, Set.indicator, hm, primeSavingCondition]

/--
@isnad1 id=eq.0h0v.s4.cf472ead1cef from=translated src=- shape=d4df52f5 vocab=7c76597a
-/
theorem savingOmega_candidate_eq_series :
    savingOmega 1857 3714 5570 = primeSavingSeries := by
  apply periodic_saving_integral_eq_series
    (fun u => savingChi (1857 * u) (3714 * u) (5570 * u))
    activeSavingCells savingLeft savingRight
  · intro k u
    simpa only [Int.cast_ofNat] using savingChi_integer_periodic 1857 3714 5570 k u
  · exact savingDensity_integrableOn (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · intro j hj
    have he := savingInterval_endpoints hj
    exact ⟨he.1, he.2.1, he.2.2.2.le⟩
  · exact savingIntervals_pairwiseDisjoint
  · intro u hu
    rw [savingChi_candidate_indicator hu, primeSavingSet_eq_intervals]
    rfl

/--
@isnad1 id=eq.0h0v.s4.1963960a51e9 from=translated src=- shape=3c781761 vocab=bcd9e6b7
-/
theorem savingPhi_candidate_eq_series :
    savingPhi candidate = primeSavingSeries / 5570 := by
  have h := savingOmega_eq_scaled_phi (1857 / 5570) (3714 / 5570)
    (by norm_num : (0 : ℝ) < 5570)
  norm_num only at h
  rw [savingOmega_candidate_eq_series] at h
  change primeSavingSeries = 5570 * savingPhi candidate at h
  linarith

/--
@isnad1 id=lt.0h0v.s3.60fe479ec3ad from=translated src=- shape=a1bca669 vocab=21f6b6a9
-/
theorem savingPhi_candidate_pos : 0 < savingPhi candidate := by
  have hn : ∀ j ∈ activeSavingCells, ∀ k,
      0 ≤ periodicSummandReal (savingLeft j) (savingRight j) k := by
    intro j hj
    have he := savingInterval_endpoints hj
    exact periodicSummandReal_nonneg he.1 he.2.1
  have hj : 1 ∈ activeSavingCells := by norm_num [mem_activeSavingCells]
  have hs : 0 < primeSavingSeries := by
    apply Finset.sum_pos' (fun j hj => tsum_nonneg (hn j hj))
    refine ⟨1, hj, (savingInterval_series_summable hj).tsum_pos (hn 1 hj) 0 ?_⟩
    norm_num [periodicSummandReal, savingLeft, savingRight]
  rw [savingPhi_candidate_eq_series]
  exact div_pos hs (by norm_num)

noncomputable def parameterSmoothCost (p : ℝ × ℝ) : ℝ :=
  2 * p.1 + 4 * p.2 - 2 - (5 * p.2 - 5 / 2) * Real.log 2

noncomputable def parameterCost (p : ℝ × ℝ) : ℝ :=
  parameterSmoothCost p - savingPhi p

/--
@isnad1 id=eq.0h0v.s2.46bf120fcd1f from=translated src=- shape=1b5bb463 vocab=a6948bcb
-/
theorem parameterCost_candidate :
    parameterCost candidate = normalizationCost primeSavingSeries := by
  rw [parameterCost, savingPhi_candidate_eq_series, normalizationCost_explicit]
  norm_num [parameterSmoothCost, candidate]
  ring

end PiIrrationality
