/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import Tengoku.LeanPool.LeanPool.ChannelCapacity.Discharged
public import Tengoku.LeanPool.LeanPool.ChannelCapacity.Finite

public import Tengoku

/-!
# ChannelCapacity.DischargedExample

Worked example for the discharged capacity theorem.

This file builds a concrete positive full-rank `Fin 2 → Fin 2` channel with counting-measure
reference, instantiates `Kernel.ContinuousPositiveDensity`, and applies
`exists_unique_capacity_achieving_prior_discharged`.
-/

@[expose] public section

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal NNReal

namespace ChannelCapacity.DischargedExample

private lemma threeQuarter_add_oneQuarter :
    (3 / 4 : ℝ≥0∞) + 1 / 4 = 1 := by
  have h : ((3 / 4 : ℝ≥0) + 1 / 4 : ℝ≥0) = 1 := by
    norm_num
  exact (by simpa using congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) h)

private lemma oneQuarter_add_threeQuarter :
    (1 / 4 : ℝ≥0∞) + 3 / 4 = 1 := by
  simpa [add_comm] using threeQuarter_add_oneQuarter

/-- The two rows of the `2 × 2` channel as probability mass functions on `Fin 2`
(mass `3/4` on the matching output, `1/4` on the other). -/
noncomputable def twoByTwoRowPMF : Fin 2 → PMF (Fin 2)
  | 0 => PMF.ofFintype (fun
      | 0 => (3 / 4 : ℝ≥0∞)
      | _ => (1 / 4 : ℝ≥0∞)) (by
        simpa [Fin.sum_univ_two] using threeQuarter_add_oneQuarter)
  | _ => PMF.ofFintype (fun
      | 0 => (1 / 4 : ℝ≥0∞)
      | _ => (3 / 4 : ℝ≥0∞)) (by
        simpa [Fin.sum_univ_two] using oneQuarter_add_threeQuarter)

/-- The two channel rows as probability measures on `Fin 2`. -/
noncomputable def twoByTwoRows (i : Fin 2) : ProbabilityMeasure (Fin 2) :=
  ⟨(twoByTwoRowPMF i).toMeasure, by infer_instance⟩

/--
@isnad1 id=eq.0h2v.s7.6b29eec5a738 from=translated src=- shape=000de0ee vocab=33caf209
-/
@[simp]
lemma twoByTwoRows_apply_singleton (i j : Fin 2) :
    (twoByTwoRows i).toMeasure {j} = twoByTwoRowPMF i j := by
  simp [twoByTwoRows]

/-- The `2 × 2` Markov kernel whose rows are `twoByTwoRows`. -/
noncomputable def twoByTwoKernel : Kernel (Fin 2) (Fin 2) :=
  Kernel.ofFunOfCountable fun i => (twoByTwoRows i).toMeasure

/--
@isnad1 id=eq.0h1v.s6.e33ff5dc338b from=translated src=- shape=11e298fe vocab=05144aab
-/
@[simp]
lemma twoByTwoKernel_apply (i : Fin 2) :
    twoByTwoKernel i = (twoByTwoRows i).toMeasure := by
  rfl

/--
@isnad1 id=eq.0h2v.s7.966e4dd747b7 from=translated src=- shape=f6b3a7b3 vocab=53df51a9
-/
lemma twoByTwoKernel_apply_singleton (i j : Fin 2) :
    twoByTwoKernel i {j} = twoByTwoRowPMF i j := by
  simp [twoByTwoKernel_apply, twoByTwoRows]

/--
@isnad1 id=ismarkov.0h0v.s4.430403da4511 from=translated src=- shape=8bd98729 vocab=477c4cf6
-/
noncomputable instance twoByTwoKernel_isMarkov : IsMarkovKernel twoByTwoKernel := by
  constructor
  intro i
  change IsProbabilityMeasure ((twoByTwoRowPMF i).toMeasure)
  infer_instance

/-- The density of `twoByTwoKernel` with respect to the counting measure:
`3/4` on the diagonal and `1/4` off it. -/
noncomputable def twoByTwoDensity (i j : Fin 2) : NNReal :=
  if i = j then 3 / 4 else 1 / 4

/--
@isnad1 id=eq.0h2v.s5.560c41c4a90b from=translated src=- shape=a7f6acc8 vocab=43dc9c26
-/
@[simp]
lemma twoByTwoDensity_apply (i j : Fin 2) :
    (twoByTwoDensity i j : ℝ≥0∞) = twoByTwoRowPMF i j := by
  fin_cases i <;> fin_cases j <;> simp [twoByTwoDensity, twoByTwoRowPMF]

/--
@isnad1 id=rowmatri.0h0v.s5.9f49c4812e69 from=translated src=- shape=44762807 vocab=76c9b269
-/
theorem twoByTwo_rowMatrixFullRank : Kernel.RowMatrixFullRank twoByTwoKernel := by
  intro w v hEq
  funext a
  fin_cases a
  · have h0 := congrFun hEq 0
    have h1 := congrFun hEq 1
    norm_num [Fin.sum_univ_two, twoByTwoKernel_apply_singleton, twoByTwoRowPMF] at h0 h1 ⊢
    nlinarith
  · have h0 := congrFun hEq 0
    have h1 := congrFun hEq 1
    norm_num [Fin.sum_univ_two, twoByTwoKernel_apply_singleton, twoByTwoRowPMF] at h0 h1 ⊢
    nlinarith

/--
@isnad1 id=injectiv.0h0v.s4.c93756abc647 from=translated src=- shape=44762807 vocab=e45228d5
-/
theorem twoByTwo_injectivePriorPushforward :
    Kernel.InjectivePriorPushforward twoByTwoKernel :=
  Kernel.injectivePriorPushforward_of_rowMatrixFullRank twoByTwoKernel twoByTwo_rowMatrixFullRank

/-- The `ContinuousPositiveDensity` witness for `twoByTwoKernel` over the counting measure. -/
noncomputable def twoByTwoContinuousPositiveDensity :
    Kernel.ContinuousPositiveDensity twoByTwoKernel Measure.count := by
  refine
    { density := twoByTwoDensity
      continuous_density := by
        fun_prop
      eq_withDensity := ?_
      density_pos := ?_
      mutualInformation_usc := ?_ }
  · intro i
    have hcount := ChannelCapacity.toMeasure_eq_count_withDensity (μ := twoByTwoRows i)
    simpa [twoByTwoRows, twoByTwoDensity_apply] using hcount
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [twoByTwoDensity]
  · exact (continuous_mutualInformation_of_finite (k := twoByTwoKernel)).upperSemicontinuous

end ChannelCapacity.DischargedExample
