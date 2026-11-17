/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Analytic.BorelCharacterization
import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Ranks.Boundedness

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Coanalytic reduction and rank-based Borel separation

Two coanalytic Baire sets are reduced to disjoint coanalytic subsets with the same union. Given
explicit well-founded-tree rank presentations, the left piece uses the non-strict comparison and
the right piece uses the reversed strict comparison. The global off-domain truth tables make the
subset, cover, and disjointness equations exact.

Applying reduction to the complements of two disjoint analytic sets gives a Borel separator and an
exact `BorelCode` witness. This is an independent rank proof of the same separator conclusion as
Lusin separation; it is not the v1.2 call to mathlib's separation theorem.
-/

open Cardinal Ordinal Set

namespace DescriptiveSetTheory

open Tree

namespace CoanalyticRankPresentation

variable {A B : Set (ℕ → ℕ)}

/-- The pointwise pair of tree codes supplied by two rank presentations.-/
def comparisonMap (P : CoanalyticRankPresentation A) (Q : CoanalyticRankPresentation B)
    (x : ℕ → ℕ) : TreeCode × TreeCode :=
  (P.treeCode x, Q.treeCode x)

/-- The pointwise comparison map is continuous.
@isnad1 id=continuo.0h4v.s6.23ec44c98284 from=translated src=- shape=821f2972 vocab=6e60e2ad
-/
theorem continuous_comparisonMap (P : CoanalyticRankPresentation A)
    (Q : CoanalyticRankPresentation B) : Continuous (comparisonMap P Q) :=
  P.continuous_treeCode.prodMk Q.continuous_treeCode

/-- The left reduced piece. An `A`-only point is included by the off-domain case; a point in both
domains is included exactly when its `P` rank is at most its `Q` rank.-/
def leftReduction (P : CoanalyticRankPresentation A) (Q : CoanalyticRankPresentation B) :
    Set (ℕ → ℕ) :=
  comparisonMap P Q ⁻¹' treeRankLeCoanalytic

/-- The right reduced piece, with reversed presentation order and strict comparison.-/
def rightReduction (P : CoanalyticRankPresentation A) (Q : CoanalyticRankPresentation B) :
    Set (ℕ → ℕ) :=
  comparisonMap Q P ⁻¹' treeRankLtCoanalytic

/-- The left reduced piece is coanalytic.
@isnad1 id=iscoanal.0h4v.s5.580bccfa0301 from=translated src=- shape=3c116961 vocab=0cf851ad
-/
theorem isCoanalytic_leftReduction (P : CoanalyticRankPresentation A)
    (Q : CoanalyticRankPresentation B) : IsCoanalytic (leftReduction P Q) :=
  isCoanalytic_treeRankLeCoanalytic.preimage (continuous_comparisonMap P Q)

/-- The right reduced piece is coanalytic.
@isnad1 id=iscoanal.0h4v.s5.d7ed6b38c30d from=translated src=- shape=3c116961 vocab=ff752129
-/
theorem isCoanalytic_rightReduction (P : CoanalyticRankPresentation A)
    (Q : CoanalyticRankPresentation B) : IsCoanalytic (rightReduction P Q) :=
  isCoanalytic_treeRankLtCoanalytic.preimage (continuous_comparisonMap Q P)

/-- Exact rank/off-domain semantics of the left reduced piece.
@isnad1 id=iff.0h5v.s7.a2b64b8eb045 from=translated src=- shape=809ff1a5 vocab=2795aa27
-/
theorem mem_leftReduction_iff (P : CoanalyticRankPresentation A)
    (Q : CoanalyticRankPresentation B) (x : ℕ → ℕ) :
    x ∈ leftReduction P Q ↔
      ∃ hxA : x ∈ A, x ∉ B ∨
        ∃ hxB : x ∈ B, P.rank x hxA ≤ Q.rank x hxB := by
  change (P.treeCode x, Q.treeCode x) ∈ treeRankLeCoanalytic ↔ _
  rw [mem_treeRankLeCoanalytic_iff]
  constructor
  · rintro ⟨hPA, hQB | ⟨hQB, hrank⟩⟩
    · exact ⟨(P.mem_iff x).2 hPA, Or.inl (fun hxB => hQB (Q.wellFounded hxB))⟩
    · let hxA : x ∈ A := (P.mem_iff x).2 hPA
      let hxB : x ∈ B := (Q.mem_iff x).2 hQB
      exact ⟨hxA, Or.inr ⟨hxB, by simpa [rank] using hrank⟩⟩
  · rintro ⟨hxA, hxB | ⟨hxB, hrank⟩⟩
    · exact ⟨P.wellFounded hxA, Or.inl (fun hQB => hxB ((Q.mem_iff x).2 hQB))⟩
    · exact ⟨P.wellFounded hxA, Or.inr ⟨Q.wellFounded hxB,
        by simpa [rank] using hrank⟩⟩

/-- Exact rank/off-domain semantics of the right reduced piece.
@isnad1 id=iff.0h5v.s7.640c4fe5f113 from=translated src=- shape=140c2280 vocab=26909ca2
-/
theorem mem_rightReduction_iff (P : CoanalyticRankPresentation A)
    (Q : CoanalyticRankPresentation B) (x : ℕ → ℕ) :
    x ∈ rightReduction P Q ↔
      ∃ hxB : x ∈ B, x ∉ A ∨
        ∃ hxA : x ∈ A, Q.rank x hxB < P.rank x hxA := by
  change (Q.treeCode x, P.treeCode x) ∈ treeRankLtCoanalytic ↔ _
  rw [mem_treeRankLtCoanalytic_iff]
  constructor
  · rintro ⟨hQB, hPA | ⟨hPA, hrank⟩⟩
    · exact ⟨(Q.mem_iff x).2 hQB, Or.inl (fun hxA => hPA (P.wellFounded hxA))⟩
    · let hxB : x ∈ B := (Q.mem_iff x).2 hQB
      let hxA : x ∈ A := (P.mem_iff x).2 hPA
      exact ⟨hxB, Or.inr ⟨hxA, by simpa [rank] using hrank⟩⟩
  · rintro ⟨hxB, hxA | ⟨hxA, hrank⟩⟩
    · exact ⟨Q.wellFounded hxB, Or.inl (fun hPA => hxA ((P.mem_iff x).2 hPA))⟩
    · exact ⟨Q.wellFounded hxB, Or.inr ⟨P.wellFounded hxA,
        by simpa [rank] using hrank⟩⟩

/-- The left reduction is contained in the first coanalytic set.
@isnad1 id=le.0h4v.s4.f557c14607cd from=translated src=- shape=23368e39 vocab=3d48e0c5
-/
theorem leftReduction_subset (P : CoanalyticRankPresentation A)
    (Q : CoanalyticRankPresentation B) : leftReduction P Q ⊆ A := by
  intro x hx
  exact (mem_leftReduction_iff P Q x).1 hx |>.choose

/-- The right reduction is contained in the second coanalytic set.
@isnad1 id=le.0h4v.s4.5eca95e3b687 from=translated src=- shape=2517e36a vocab=603fa6b9
-/
theorem rightReduction_subset (P : CoanalyticRankPresentation A)
    (Q : CoanalyticRankPresentation B) : rightReduction P Q ⊆ B := by
  intro x hx
  exact (mem_rightReduction_iff P Q x).1 hx |>.choose

/-- The rank tie-breaking convention makes the two reduced pieces disjoint.
@isnad1 id=disjoint.0h4v.s6.602f44016211 from=translated src=- shape=4b7a4984 vocab=fddafaf0
-/
theorem disjoint_reductions (P : CoanalyticRankPresentation A)
    (Q : CoanalyticRankPresentation B) : Disjoint (leftReduction P Q) (rightReduction P Q) := by
  rw [Set.disjoint_iff]
  rintro x ⟨hxLeft, hxRight⟩
  obtain ⟨hxA, hleft⟩ := (mem_leftReduction_iff P Q x).1 hxLeft
  obtain ⟨hxB, hright⟩ := (mem_rightReduction_iff P Q x).1 hxRight
  rcases hleft with hxnotB | ⟨hxB', hle⟩
  · exact hxnotB hxB
  rcases hright with hxnotA | ⟨hxA', hlt⟩
  · exact hxnotA hxA
  exact (not_lt_of_ge hle) (by simpa using hlt)

/-- The reduced pieces cover exactly the original union.
@isnad1 id=eq.0h4v.s5.0b471f6db356 from=translated src=- shape=3bacc8dd vocab=cac77834
-/
theorem union_reductions (P : CoanalyticRankPresentation A)
    (Q : CoanalyticRankPresentation B) :
    leftReduction P Q ∪ rightReduction P Q = A ∪ B := by
  apply Set.Subset.antisymm
  · exact Set.union_subset_union (leftReduction_subset P Q) (rightReduction_subset P Q)
  · intro x hx
    rcases hx with hxA | hxB
    · by_cases hxB : x ∈ B
      · by_cases hle : P.rank x hxA ≤ Q.rank x hxB
        · exact Or.inl ((mem_leftReduction_iff P Q x).2 ⟨hxA, Or.inr ⟨hxB, hle⟩⟩)
        · exact Or.inr ((mem_rightReduction_iff P Q x).2
            ⟨hxB, Or.inr ⟨hxA, lt_of_not_ge hle⟩⟩)
      · exact Or.inl ((mem_leftReduction_iff P Q x).2 ⟨hxA, Or.inl hxB⟩)
    · by_cases hxA : x ∈ A
      · by_cases hle : P.rank x hxA ≤ Q.rank x hxB
        · exact Or.inl ((mem_leftReduction_iff P Q x).2 ⟨hxA, Or.inr ⟨hxB, hle⟩⟩)
        · exact Or.inr ((mem_rightReduction_iff P Q x).2
            ⟨hxB, Or.inr ⟨hxA, lt_of_not_ge hle⟩⟩)
      · exact Or.inr ((mem_rightReduction_iff P Q x).2 ⟨hxB, Or.inl hxA⟩)

/-- The pullback of a strict countable tree-rank stage along a presentation.-/
def rankStage (P : CoanalyticRankPresentation A) (ξ : Ordinal.{0}) : Set (ℕ → ℕ) :=
  P.treeCode ⁻¹' treeRankLT ξ

/-- Exact semantics of a pulled-back rank stage.
@isnad1 id=iff.0h4v.s6.b6f4a925ee7c from=translated src=- shape=efb52213 vocab=09ade883
-/
theorem mem_rankStage_iff (P : CoanalyticRankPresentation A) (ξ : Ordinal.{0})
    (x : ℕ → ℕ) :
    x ∈ P.rankStage ξ ↔ ∃ hx : x ∈ A, P.rank x hx < ξ := by
  change P.treeCode x ∈ treeRankLT ξ ↔ _
  constructor
  · rintro ⟨hWF, hrank⟩
    let hx : x ∈ A := (P.mem_iff x).2 hWF
    exact ⟨hx, by simpa [rank] using hrank⟩
  · rintro ⟨hx, hrank⟩
    exact ⟨P.wellFounded hx, by simpa [rank] using hrank⟩

/-- Every pulled-back stage below `ω₁` is Borel measurable.
@isnad1 id=measurab.1h3v.s6.76bd731812d9 from=translated src=- shape=57f55120 vocab=6589a76b
-/
theorem measurableSet_rankStage (P : CoanalyticRankPresentation A) {ξ : Ordinal.{0}}
    (hξ : ξ < ω₁) : MeasurableSet (P.rankStage ξ) := by
  letI : MeasurableSpace TreeCode := borel TreeCode
  letI : BorelSpace TreeCode := ⟨rfl⟩
  have hstage : MeasurableSet (treeRankLT ξ) := borelMeasurableSet_treeRankLT hξ
  have hanalytic : MeasureTheory.AnalyticSet (treeRankLT ξ) := hstage.analyticSet
  have hcoanalytic : IsCoanalytic (treeRankLT ξ) := hstage.isCoanalytic
  exact measurableSet_iff_analyticSet_and_isCoanalytic.mpr
    ⟨hanalytic.preimage P.continuous_treeCode,
      hcoanalytic.preimage P.continuous_treeCode⟩

/-- Every pulled-back rank stage lies in the exact presentation domain.
@isnad1 id=le.0h3v.s4.dab1eb77532c from=translated src=- shape=8bd03040 vocab=2b1d6c28
-/
theorem rankStage_subset (P : CoanalyticRankPresentation A) (ξ : Ordinal.{0}) :
    P.rankStage ξ ⊆ A := by
  intro x hx
  exact (P.mem_rankStage_iff ξ x).1 hx |>.choose

/-- An analytic subfamily of a presented coanalytic set is contained in one Borel pulled-back
rank stage, and an exact code for that stage is returned.
@isnad1 id=ex.2h3v.s7.d63794c005ee from=translated src=- shape=7d297737 vocab=6f1b645f
-/
theorem exists_borelCode_envelope_of_rank (P : CoanalyticRankPresentation A)
    {S : Set (ℕ → ℕ)} (hS : MeasureTheory.AnalyticSet S) (hSA : S ⊆ A) :
    ∃ ξ : Ordinal.{0}, ξ < ω₁ ∧
      ∃ c : BorelCode (ℕ → ℕ), c.eval = P.rankStage ξ ∧
        S ⊆ c.eval ∧ c.eval ⊆ A := by
  obtain ⟨ξ, hξ, hbound⟩ := P.bounded_of_analytic hS hSA
  obtain ⟨c, hc⟩ := BorelCode.measurableSet_iff_exists_code.mp
    (P.measurableSet_rankStage hξ)
  refine ⟨ξ, hξ, c, hc, ?_, ?_⟩
  · intro x hx
    rw [hc]
    exact (P.mem_rankStage_iff ξ x).2 ⟨hSA hx, hbound x hx⟩
  · rw [hc]
    exact P.rankStage_subset ξ

end CoanalyticRankPresentation

/-- **Coanalytic reduction theorem on Baire space.** Any two coanalytic sets have disjoint
coanalytic subsets contained in the respective inputs and covering exactly their union.
@isnad1 id=ex.2h2v.s7.02cdebc526ae from=translated src=- shape=fdf19731 vocab=f245a97d
-/
theorem exists_coanalytic_reduction {A B : Set (ℕ → ℕ)}
    (hA : IsCoanalytic A) (hB : IsCoanalytic B) :
    ∃ C D : Set (ℕ → ℕ), IsCoanalytic C ∧ IsCoanalytic D ∧
      C ⊆ A ∧ D ⊆ B ∧ Disjoint C D ∧ C ∪ D = A ∪ B := by
  obtain ⟨P⟩ := exists_coanalyticRankPresentation hA
  obtain ⟨Q⟩ := exists_coanalyticRankPresentation hB
  exact ⟨P.leftReduction Q, P.rightReduction Q,
    P.isCoanalytic_leftReduction Q, P.isCoanalytic_rightReduction Q,
    P.leftReduction_subset Q, P.rightReduction_subset Q,
    P.disjoint_reductions Q, P.union_reductions Q⟩

/-- A rank-reduction proof of Borel separation for disjoint analytic Baire sets, with exact code
evaluation. Unlike `exists_borelCode_separator_of_disjoint_analytic`, this theorem constructs the
semantic separator from coanalytic ranks on the two complements before invoking code
completeness.
@isnad1 id=ex.3h2v.s7.e8f9382a1527 from=translated src=- shape=901e6501 vocab=cc7fa570
-/
theorem exists_borelCode_separator_of_rank {s t : Set (ℕ → ℕ)}
    (hs : MeasureTheory.AnalyticSet s) (ht : MeasureTheory.AnalyticSet t)
    (hst : Disjoint s t) :
    ∃ c : BorelCode (ℕ → ℕ), s ⊆ c.eval ∧ Disjoint t c.eval := by
  obtain ⟨P⟩ := exists_coanalyticRankPresentation (isCoanalytic_compl_iff.2 hs)
  obtain ⟨Q⟩ := exists_coanalyticRankPresentation (isCoanalytic_compl_iff.2 ht)
  let C := P.leftReduction Q
  let D := P.rightReduction Q
  have hCco : IsCoanalytic C := P.isCoanalytic_leftReduction Q
  have hDco : IsCoanalytic D := P.isCoanalytic_rightReduction Q
  have hCsub : C ⊆ sᶜ := P.leftReduction_subset Q
  have hDsub : D ⊆ tᶜ := P.rightReduction_subset Q
  have hCD : Disjoint C D := P.disjoint_reductions Q
  have hcover : C ∪ D = Set.univ := by
    rw [P.union_reductions Q]
    ext x
    constructor
    · intro
      trivial
    · intro
      by_cases hxs : x ∈ s
      · exact Or.inr (fun hxt => hst.notMem_of_mem_left hxs hxt)
      · exact Or.inl hxs
  have hCcompl : Cᶜ = D := by
    ext x
    constructor
    · intro hxnotC
      have hxuniv : x ∈ C ∪ D := by rw [hcover]; trivial
      rcases hxuniv with hxC | hxD
      · exact (hxnotC hxC).elim
      · exact hxD
    · intro hxD hxC
      exact hCD.notMem_of_mem_right hxD hxC
  have hDanalytic : MeasureTheory.AnalyticSet D := by
    rw [← hCcompl]
    exact hCco
  obtain ⟨c, hc⟩ :=
    exists_borelCode_iff_analyticSet_and_isCoanalytic.mpr ⟨hDanalytic, hDco⟩
  refine ⟨c, ?_, ?_⟩
  · intro x hxs
    rw [hc]
    have hxuniv : x ∈ C ∪ D := by rw [hcover]; trivial
    rcases hxuniv with hxC | hxD
    · exact (hCsub hxC hxs).elim
    · exact hxD
  · rw [hc, Set.disjoint_iff]
    rintro x ⟨hxt, hxD⟩
    exact hDsub hxD hxt

end DescriptiveSetTheory
