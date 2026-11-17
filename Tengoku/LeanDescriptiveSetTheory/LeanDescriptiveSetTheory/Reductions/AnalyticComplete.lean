/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Reductions.Continuous
import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Universal.AnalyticStrictness
import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Universal.Coanalytic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Complete analytic and coanalytic subsets of Baire space

The universal analytic and coanalytic relations live on a product of two Baire spaces. Pulling them
back along the fixed Baire-pair homeomorphism gives subsets of one Baire space. Exact section
universality, fixed-parameter reduction, and pair packing show that every analytic or coanalytic
Baire subset continuously reduces to the corresponding packed relation.

Completeness in this module is deliberately Baire-domain completeness. It asserts neither
uniqueness nor a preferred canonical encoding, and it introduces no higher projective levels.
-/

open Set

namespace DescriptiveSetTheory

/-- A Baire set is analytic-complete here when it is analytic and every analytic Baire set
continuously reduces to it.-/
def IsAnalyticComplete (t : Set (ℕ → ℕ)) : Prop :=
  MeasureTheory.AnalyticSet t ∧
    ∀ s : Set (ℕ → ℕ), MeasureTheory.AnalyticSet s → ContinuouslyReduces s t

/-- A Baire set is coanalytic-complete here when it is coanalytic and every coanalytic Baire set
continuously reduces to it.-/
def IsCoanalyticComplete (t : Set (ℕ → ℕ)) : Prop :=
  IsCoanalytic t ∧
    ∀ s : Set (ℕ → ℕ), IsCoanalytic s → ContinuouslyReduces s t

/-- Apply analytic completeness without unfolding its conjunction.
@isnad1 id=continuo.2h2v.s5.e4d4e115a06a from=translated src=- shape=477b97d6 vocab=e95cbbe1
-/
theorem IsAnalyticComplete.continuouslyReduces {t s : Set (ℕ → ℕ)}
    (ht : IsAnalyticComplete t) (hs : MeasureTheory.AnalyticSet s) :
    ContinuouslyReduces s t :=
  ht.2 s hs

/-- Apply coanalytic completeness without unfolding its conjunction.
@isnad1 id=continuo.2h2v.s5.0a3e28f6cc57 from=translated src=- shape=477b97d6 vocab=2123d27a
-/
theorem IsCoanalyticComplete.continuouslyReduces {t s : Set (ℕ → ℕ)}
    (ht : IsCoanalyticComplete t) (hs : IsCoanalytic s) :
    ContinuouslyReduces s t :=
  ht.2 s hs

/-- The universal analytic relation packed into one Baire coordinate.-/
def analyticCompleteSet : Set (ℕ → ℕ) :=
  unpackBairePair ⁻¹' baireUniversalAnalytic

/-- The universal coanalytic relation packed into one Baire coordinate.-/
def coanalyticCompleteSet : Set (ℕ → ℕ) :=
  unpackBairePair ⁻¹' baireUniversalCoanalytic

/-- The packed analytic relation is analytic.
@isnad1 id=analytic.0h0v.s3.6861afb1e018 from=translated src=- shape=c69f195a vocab=4c7535dd
-/
theorem analyticSet_analyticCompleteSet :
    MeasureTheory.AnalyticSet analyticCompleteSet :=
  analyticSet_baireUniversalAnalytic.preimage continuous_unpackBairePair

/-- The packed coanalytic relation is coanalytic.
@isnad1 id=iscoanal.0h0v.s3.73339bab47d7 from=translated src=- shape=c69f195a vocab=4f6975cc
-/
theorem isCoanalytic_coanalyticCompleteSet :
    IsCoanalytic coanalyticCompleteSet :=
  isCoanalytic_baireUniversalCoanalytic.preimage continuous_unpackBairePair

/-- The two packed complete-set candidates are exact complements.
@isnad1 id=eq.0h0v.s4.1e0e4a915843 from=translated src=- shape=893eb74e vocab=0611f0b2
-/
theorem coanalyticCompleteSet_eq_compl :
    coanalyticCompleteSet = analyticCompleteSetᶜ := by
  rw [coanalyticCompleteSet, analyticCompleteSet,
    baireUniversalCoanalytic_eq_compl, preimage_compl]

/-- Pair packing reduces the universal analytic relation to its one-coordinate copy.
@isnad1 id=continuo.0h0v.s5.7cf420b537d3 from=translated src=- shape=48ab77f0 vocab=05d44e87
-/
theorem continuouslyReduces_baireUniversalAnalytic_analyticCompleteSet :
    ContinuouslyReduces baireUniversalAnalytic analyticCompleteSet := by
  refine ⟨packBairePair, continuous_packBairePair, ?_⟩
  ext z
  simp [analyticCompleteSet]

/-- The coanalytic packing reduction is exactly the complement transport of the analytic one.
@isnad1 id=continuo.0h0v.s5.c2604737c596 from=translated src=- shape=48ab77f0 vocab=8130790e
-/
theorem continuouslyReduces_baireUniversalCoanalytic_coanalyticCompleteSet :
    ContinuouslyReduces baireUniversalCoanalytic coanalyticCompleteSet := by
  rw [baireUniversalCoanalytic_eq_compl, coanalyticCompleteSet_eq_compl]
  exact continuouslyReduces_baireUniversalAnalytic_analyticCompleteSet.compl

/-- The packed universal analytic relation is complete for analytic Baire subsets.
@isnad1 id=isanalyt.0h0v.s1.9541d5f66378 from=translated src=- shape=49959d42 vocab=80c82dac
-/
theorem isAnalyticComplete_analyticCompleteSet :
    IsAnalyticComplete analyticCompleteSet := by
  refine ⟨analyticSet_analyticCompleteSet, fun s hs => ?_⟩
  exact (isUniversalAnalytic_baireUniversalAnalytic.2.continuouslyReduces hs).trans
    continuouslyReduces_baireUniversalAnalytic_analyticCompleteSet

/-- The packed universal coanalytic relation is complete for coanalytic Baire subsets.
@isnad1 id=iscoanal.0h0v.s1.adecf1f6d60c from=translated src=- shape=49959d42 vocab=3c481c77
-/
theorem isCoanalyticComplete_coanalyticCompleteSet :
    IsCoanalyticComplete coanalyticCompleteSet := by
  refine ⟨isCoanalytic_coanalyticCompleteSet, fun s hs => ?_⟩
  exact (isUniversalCoanalytic_baireUniversalCoanalytic.2.continuouslyReduces hs).trans
    continuouslyReduces_baireUniversalCoanalytic_coanalyticCompleteSet

/-- Analytic completeness is proper: the packed analytic set is not coanalytic.
@isnad1 id=not.0h0v.s3.b4b3481d9474 from=translated src=- shape=c52ea885 vocab=445f27fd
-/
theorem not_isCoanalytic_analyticCompleteSet :
    ¬ IsCoanalytic analyticCompleteSet := by
  intro hcoanalytic
  obtain ⟨f, hf, hpre⟩ :=
    isAnalyticComplete_analyticCompleteSet.continuouslyReduces
      analyticSet_baireAnalyticNotCoanalytic
  apply not_isCoanalytic_baireAnalyticNotCoanalytic
  have hsource := hcoanalytic.preimage hf
  rw [hpre] at hsource
  exact hsource

/-- Coanalytic completeness is proper: the packed coanalytic set is not analytic.
@isnad1 id=not.0h0v.s3.4b93782b25c0 from=translated src=- shape=c52ea885 vocab=0d668815
-/
theorem not_analyticSet_coanalyticCompleteSet :
    ¬ MeasureTheory.AnalyticSet coanalyticCompleteSet := by
  intro hanalytic
  obtain ⟨f, hf, hpre⟩ :=
    isCoanalyticComplete_coanalyticCompleteSet.continuouslyReduces
      isCoanalytic_baireCoanalyticNotAnalytic
  apply not_analyticSet_baireCoanalyticNotAnalytic
  have hsource := hanalytic.preimage hf
  rw [hpre] at hsource
  exact hsource

end DescriptiveSetTheory
