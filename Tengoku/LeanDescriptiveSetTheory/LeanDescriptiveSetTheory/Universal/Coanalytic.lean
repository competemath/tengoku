/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Analytic.Coanalytic
import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Universal.Analytic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A universal coanalytic relation on Baire space

The complement of the universal analytic Baire relation is coanalytic. Section complementation
shows that its vertical sections are exactly all coanalytic subsets of Baire space. Explicit
relation, section, and diagonal-preimage complement equations fix the orientation used by the
subsequent diagonal strictness argument.
-/

open Set

namespace DescriptiveSetTheory

/-- A coanalytic relation whose vertical sections are exactly all coanalytic sets.-/
def IsUniversalCoanalytic {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
    (U : Set (P × X)) : Prop :=
  IsCoanalytic U ∧ IsUniversalFor IsCoanalytic U

/-- Every section of a universal coanalytic relation is coanalytic.-/
theorem IsUniversalCoanalytic.isCoanalytic_verticalSection {P X : Type*}
    [TopologicalSpace P] [TopologicalSpace X] {U : Set (P × X)}
    (hU : IsUniversalCoanalytic U) (p : P) :
    IsCoanalytic (verticalSection U p) :=
  (hU.2 (verticalSection U p)).2 ⟨p, rfl⟩

/-- Every coanalytic set occurs as a vertical section.-/
theorem IsUniversalCoanalytic.exists_section {P X : Type*}
    [TopologicalSpace P] [TopologicalSpace X] {U : Set (P × X)}
    (hU : IsUniversalCoanalytic U) {s : Set X} (hs : IsCoanalytic s) :
    ∃ p, verticalSection U p = s :=
  (hU.2 s).1 hs

/-- The Baire universal coanalytic relation is the complement of the universal analytic one.-/
def baireUniversalCoanalytic : Set ((ℕ → ℕ) × (ℕ → ℕ)) :=
  baireUniversalAnalyticᶜ

/-- The defining complement equation.-/
theorem baireUniversalCoanalytic_eq_compl :
    baireUniversalCoanalytic = baireUniversalAnalyticᶜ :=
  rfl

/-- Complementing back recovers the universal analytic relation.-/
@[simp]
theorem compl_baireUniversalCoanalytic :
    baireUniversalCoanalyticᶜ = baireUniversalAnalytic := by
  simp [baireUniversalCoanalytic]

/-- Coanalytic sections are the complements of the corresponding analytic sections.-/
@[simp]
theorem verticalSection_baireUniversalCoanalytic (p : ℕ → ℕ) :
    verticalSection baireUniversalCoanalytic p =
      (verticalSection baireUniversalAnalytic p)ᶜ :=
  rfl

/-- The total complemented relation is coanalytic.-/
theorem isCoanalytic_baireUniversalCoanalytic :
    IsCoanalytic baireUniversalCoanalytic := by
  simpa [IsCoanalytic, baireUniversalCoanalytic] using
    analyticSet_baireUniversalAnalytic

/-- Every section of the complemented relation is coanalytic.-/
theorem isCoanalytic_verticalSection_baireUniversalCoanalytic (p : ℕ → ℕ) :
    IsCoanalytic (verticalSection baireUniversalCoanalytic p) := by
  simpa [IsCoanalytic, verticalSection_baireUniversalCoanalytic] using
    analyticSet_verticalSection_baireUniversalAnalytic p

/-- Every coanalytic Baire set occurs as an exact section.-/
theorem exists_verticalSection_baireUniversalCoanalytic {s : Set (ℕ → ℕ)}
    (hs : IsCoanalytic s) :
    ∃ p, verticalSection baireUniversalCoanalytic p = s := by
  obtain ⟨p, hp⟩ :=
    exists_verticalSection_baireUniversalAnalytic (s := sᶜ) hs
  refine ⟨p, ?_⟩
  rw [verticalSection_baireUniversalCoanalytic, hp, compl_compl]

/-- `baireUniversalCoanalytic` is universal for coanalytic Baire subsets.-/
theorem isUniversalCoanalytic_baireUniversalCoanalytic :
    IsUniversalCoanalytic baireUniversalCoanalytic := by
  refine ⟨isCoanalytic_baireUniversalCoanalytic, fun s => ?_⟩
  constructor
  · exact exists_verticalSection_baireUniversalCoanalytic
  · rintro ⟨p, rfl⟩
    exact isCoanalytic_verticalSection_baireUniversalCoanalytic p

/-- The diagonal map used by the analytic/coanalytic universal relations.-/
def baireAnalyticDiagonalMap (x : ℕ → ℕ) : (ℕ → ℕ) × (ℕ → ℕ) :=
  (x, x)

/-- The analytic/coanalytic Baire diagonal is continuous.-/
theorem continuous_baireAnalyticDiagonalMap : Continuous baireAnalyticDiagonalMap :=
  continuous_id.prodMk continuous_id

/-- Pulling the coanalytic universal relation back along the diagonal gives the complement of the
analytic diagonal pullback.-/
theorem preimage_baireAnalyticDiagonalMap_baireUniversalCoanalytic :
    baireAnalyticDiagonalMap ⁻¹' baireUniversalCoanalytic =
      (baireAnalyticDiagonalMap ⁻¹' baireUniversalAnalytic)ᶜ := by
  rw [baireUniversalCoanalytic_eq_compl, preimage_compl]

/-- The reverse diagonal complement equation.-/
theorem preimage_baireAnalyticDiagonalMap_baireUniversalAnalytic :
    baireAnalyticDiagonalMap ⁻¹' baireUniversalAnalytic =
      (baireAnalyticDiagonalMap ⁻¹' baireUniversalCoanalytic)ᶜ := by
  rw [preimage_baireAnalyticDiagonalMap_baireUniversalCoanalytic, compl_compl]

end DescriptiveSetTheory
