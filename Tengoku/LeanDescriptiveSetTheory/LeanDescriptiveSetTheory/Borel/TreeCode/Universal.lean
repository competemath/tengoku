/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Borel.TreeCode.Complexity
import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Spaces.Cylinders
import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.StandardBorel.Code
import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Universal.Open

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Universal evaluation relations for standard Borel-tree codes

Valid parameters have exactly their proof-gated v2.3 denotation as a section of both completed
relations.  Invalid parameters give the full section on the analytic side and the empty section on
the coanalytic side.  Consequently both relations have exactly all Borel sets as sections, while
their pointclass bounds remain independent.
-/

open Set TopologicalSpace

universe u

namespace DescriptiveSetTheory.BorelTreeCode

variable {X : Type u}

/-- An invalid parameter has the full analytic-completion section.
@isnad1 id=eq.1h3v.s4.8f4401441b3b from=translated src=- shape=48eccfee vocab=66ff833c
-/
theorem verticalSection_analyticEvaluation_of_not_isValid (b : ℕ → Set X) {c : Raw}
    (h : ¬IsValid c) :
    verticalSection (analyticEvaluation b) c = Set.univ := by
  ext x
  exact iff_true_intro (evaluation_disagrees_of_not_isValid b h x).1

/-- An invalid parameter has the empty coanalytic-completion section.
@isnad1 id=eq.1h3v.s4.3e3ac940facf from=translated src=- shape=c37ce162 vocab=1d307920
-/
theorem verticalSection_coanalyticEvaluation_of_not_isValid (b : ℕ → Set X) {c : Raw}
    (h : ¬IsValid c) :
    verticalSection (coanalyticEvaluation b) c = ∅ := by
  ext x
  exact iff_false_intro (evaluation_disagrees_of_not_isValid b h x).2

/-- A topological basis supplies the measurable leaves needed by the independent analytic bound.
@isnad1 id=analytic.1h2v.s6.541b3229e029 from=translated src=- shape=c8885bc7 vocab=6892fc51
-/
theorem analyticSet_analyticEvaluation_of_isTopologicalBasis
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {b : ℕ → Set X} (hb : IsTopologicalBasis (range b)) :
    MeasureTheory.AnalyticSet (analyticEvaluation b) :=
  analyticSet_analyticEvaluation b fun n =>
    (hb.isOpen (mem_range_self n)).measurableSet

/-- A topological basis supplies the measurable leaves needed by the independent coanalytic
bound.
@isnad1 id=iscoanal.1h2v.s6.d9976822e9a4 from=translated src=- shape=c8885bc7 vocab=75357d30
-/
theorem isCoanalytic_coanalyticEvaluation_of_isTopologicalBasis
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {b : ℕ → Set X} (hb : IsTopologicalBasis (range b)) :
    IsCoanalytic (coanalyticEvaluation b) :=
  isCoanalytic_coanalyticEvaluation b fun n =>
    (hb.isOpen (mem_range_self n)).measurableSet

/-- Analytic completed evaluation for Baire space.-/
noncomputable def baireAnalyticEvaluation : Set (Raw × (ℕ → ℕ)) :=
  analyticEvaluation baireCylinderBasisSequence

/-- Coanalytic completed evaluation for Baire space.-/
noncomputable def baireCoanalyticEvaluation : Set (Raw × (ℕ → ℕ)) :=
  coanalyticEvaluation baireCylinderBasisSequence

/-- Analytic completed evaluation for Cantor space.-/
noncomputable def cantorAnalyticEvaluation : Set (Raw × (ℕ → Bool)) :=
  analyticEvaluation cantorCylinderBasisSequence

/-- Coanalytic completed evaluation for Cantor space.-/
noncomputable def cantorCoanalyticEvaluation : Set (Raw × (ℕ → Bool)) :=
  coanalyticEvaluation cantorCylinderBasisSequence

/--
@isnad1 id=analytic.0h0v.s6.391f5f080c69 from=translated src=- shape=b30e3453 vocab=4a73bfef
-/
theorem analyticSet_baireAnalyticEvaluation :
    MeasureTheory.AnalyticSet baireAnalyticEvaluation :=
  analyticSet_analyticEvaluation_of_isTopologicalBasis
    isTopologicalBasis_range_baireCylinderBasisSequence

/--
@isnad1 id=iscoanal.0h0v.s6.c4eda27e2a47 from=translated src=- shape=b30e3453 vocab=98a35bb0
-/
theorem isCoanalytic_baireCoanalyticEvaluation :
    IsCoanalytic baireCoanalyticEvaluation :=
  isCoanalytic_coanalyticEvaluation_of_isTopologicalBasis
    isTopologicalBasis_range_baireCylinderBasisSequence

/--
@isnad1 id=analytic.0h0v.s6.30146549cfed from=translated src=- shape=400c8940 vocab=7fccffe0
-/
theorem analyticSet_cantorAnalyticEvaluation :
    MeasureTheory.AnalyticSet cantorAnalyticEvaluation := by
  letI : MetricSpace (ℕ → Bool) :=
    PiNat.metricSpaceOfDiscreteUniformity fun _ => rfl
  exact analyticSet_analyticEvaluation_of_isTopologicalBasis
    isTopologicalBasis_range_cantorCylinderBasisSequence

/--
@isnad1 id=iscoanal.0h0v.s6.1d9ebca99ae9 from=translated src=- shape=400c8940 vocab=5d764915
-/
theorem isCoanalytic_cantorCoanalyticEvaluation :
    IsCoanalytic cantorCoanalyticEvaluation := by
  letI : MetricSpace (ℕ → Bool) :=
    PiNat.metricSpaceOfDiscreteUniformity fun _ => rfl
  exact isCoanalytic_coanalyticEvaluation_of_isTopologicalBasis
    isTopologicalBasis_range_cantorCylinderBasisSequence

section StandardBorel

variable [MeasurableSpace X] [StandardBorelSpace X]

/-- A noncanonical sequential basis for mathlib's compatible Polish realization of a standard
Borel space. Only the resulting measurable-section statements are topology-independent.-/
noncomputable def standardBorelBasisSequence : ℕ → Set X := by
  letI : TopologicalSpace X := (upgradeStandardBorel X).toTopologicalSpace
  exact (CountableBasisCode.exists_basis_coding (X := X)).choose

/-- The selected standard-Borel basis really is a basis for the compatible Polish topology.
@isnad1 id=istopolo.0h1v.s4.505937509c85 from=translated src=- shape=55bcfe96 vocab=2c7edfcd
-/
theorem isTopologicalBasis_range_standardBorelBasisSequence :
    @IsTopologicalBasis X (upgradeStandardBorel X).toTopologicalSpace
      (range (standardBorelBasisSequence (X := X))) := by
  letI : TopologicalSpace X := (upgradeStandardBorel X).toTopologicalSpace
  exact (CountableBasisCode.exists_basis_coding (X := X)).choose_spec.1

/-- Analytic completed evaluation in the selected compatible Polish realization.-/
noncomputable def standardBorelAnalyticEvaluation : Set (Raw × X) :=
  analyticEvaluation (standardBorelBasisSequence (X := X))

/-- Coanalytic completed evaluation in the selected compatible Polish realization.-/
noncomputable def standardBorelCoanalyticEvaluation : Set (Raw × X) :=
  coanalyticEvaluation (standardBorelBasisSequence (X := X))

end StandardBorel

end DescriptiveSetTheory.BorelTreeCode
