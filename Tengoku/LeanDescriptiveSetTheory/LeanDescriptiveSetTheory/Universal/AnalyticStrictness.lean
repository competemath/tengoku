/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Universal.Coanalytic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Analytic and coanalytic strictness on Baire space

The complement of the universal analytic relation, pulled back along the diagonal, is coanalytic.
If it were analytic, universality would give a parameter whose vertical section is this diagonal
set, and self-membership at that parameter would be equivalent to its negation. Complementing the
witness gives the dual analytic-not-coanalytic set.
-/

open Set

namespace DescriptiveSetTheory

/-- The coanalytic diagonal witness obtained from the universal analytic relation.-/
def baireCoanalyticNotAnalytic : Set (ℕ → ℕ) :=
  baireAnalyticDiagonalMap ⁻¹' baireUniversalCoanalytic

/-- Membership in the coanalytic diagonal witness is failure of self-membership in the universal
analytic relation.
@isnad1 id=iff.0h1v.s5.ef208065baf2 from=translated src=- shape=5370aea3 vocab=f1527c19
-/
@[simp]
theorem mem_baireCoanalyticNotAnalytic {p : ℕ → ℕ} :
    p ∈ baireCoanalyticNotAnalytic ↔ (p, p) ∉ baireUniversalAnalytic :=
  Iff.rfl

/-- The diagonal witness is coanalytic.
@isnad1 id=iscoanal.0h0v.s3.cc1d544ddae8 from=translated src=- shape=c69f195a vocab=9c86cabd
-/
theorem isCoanalytic_baireCoanalyticNotAnalytic :
    IsCoanalytic baireCoanalyticNotAnalytic :=
  isCoanalytic_baireUniversalCoanalytic.preimage
    continuous_baireAnalyticDiagonalMap

/-- Diagonalization prevents the analytic universal relation from coding its diagonal witness.
@isnad1 id=not.0h0v.s3.038aff67d97c from=translated src=- shape=c52ea885 vocab=e6d7628d
-/
theorem not_analyticSet_baireCoanalyticNotAnalytic :
    ¬ MeasureTheory.AnalyticSet baireCoanalyticNotAnalytic := by
  intro hdiagonal
  obtain ⟨p, hp⟩ :=
    exists_verticalSection_baireUniversalAnalytic hdiagonal
  have hself := Set.ext_iff.mp hp p
  simp only [verticalSection, mem_baireCoanalyticNotAnalytic, mem_ofPred_eq] at hself
  tauto

/-- The analytic witness dual to `baireCoanalyticNotAnalytic`.-/
def baireAnalyticNotCoanalytic : Set (ℕ → ℕ) :=
  baireCoanalyticNotAnalyticᶜ

/-- Membership in the analytic witness is self-membership in the universal analytic relation.
@isnad1 id=iff.0h1v.s5.a94260ee4aec from=translated src=- shape=49238401 vocab=eb46fa24
-/
@[simp]
theorem mem_baireAnalyticNotCoanalytic {p : ℕ → ℕ} :
    p ∈ baireAnalyticNotCoanalytic ↔ (p, p) ∈ baireUniversalAnalytic :=
  by simp [baireAnalyticNotCoanalytic, baireCoanalyticNotAnalytic,
    baireUniversalCoanalytic, baireAnalyticDiagonalMap]

/-- The dual witness is analytic.
@isnad1 id=analytic.0h0v.s3.9d23b6140e37 from=translated src=- shape=c69f195a vocab=37046bb5
-/
theorem analyticSet_baireAnalyticNotCoanalytic :
    MeasureTheory.AnalyticSet baireAnalyticNotCoanalytic := by
  simpa [IsCoanalytic, baireAnalyticNotCoanalytic] using
    isCoanalytic_baireCoanalyticNotAnalytic

/-- The dual witness is not coanalytic.
@isnad1 id=not.0h0v.s3.1550c5e6896a from=translated src=- shape=c52ea885 vocab=78a901df
-/
theorem not_isCoanalytic_baireAnalyticNotCoanalytic :
    ¬ IsCoanalytic baireAnalyticNotCoanalytic := by
  intro hcoanalytic
  apply not_analyticSet_baireCoanalyticNotAnalytic
  simpa [IsCoanalytic, baireAnalyticNotCoanalytic] using hcoanalytic

/-- Some coanalytic subset of Baire space is not analytic.
@isnad1 id=ex.0h0v.s5.e8b9756af690 from=translated src=- shape=00b9fa31 vocab=3a743d4e
-/
theorem exists_coanalytic_not_analytic_baire :
    ∃ s : Set (ℕ → ℕ), IsCoanalytic s ∧ ¬ MeasureTheory.AnalyticSet s :=
  ⟨baireCoanalyticNotAnalytic, isCoanalytic_baireCoanalyticNotAnalytic,
    not_analyticSet_baireCoanalyticNotAnalytic⟩

/-- Some analytic subset of Baire space is not coanalytic.
@isnad1 id=ex.0h0v.s5.672c38aef63a from=translated src=- shape=00b9fa31 vocab=3a743d4e
-/
theorem exists_analytic_not_coanalytic_baire :
    ∃ s : Set (ℕ → ℕ), MeasureTheory.AnalyticSet s ∧ ¬ IsCoanalytic s :=
  ⟨baireAnalyticNotCoanalytic, analyticSet_baireAnalyticNotCoanalytic,
    not_isCoanalytic_baireAnalyticNotCoanalytic⟩

end DescriptiveSetTheory
