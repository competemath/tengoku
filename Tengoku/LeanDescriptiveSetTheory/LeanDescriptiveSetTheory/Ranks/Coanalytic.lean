/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Tree.Boundedness

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Coanalytic ranks pulled back from well-founded trees

Every coanalytic subset of Baire space continuously reduces to the well-founded tree codes. A
`CoanalyticRankPresentation A` records one such reduction without selecting it globally. Pulling
back the released tree rank gives an ordinal value exactly on `A`, analytic and coanalytic
comparison polarities, and boundedness on analytic subfamilies.

The presentation is intentionally noncanonical: different continuous reductions may give
different ordinal values. This file proves existence and the laws of each supplied presentation,
but no uniqueness or choice-independence theorem.
-/

open Cardinal Ordinal Set

namespace DescriptiveSetTheory

open Tree

/-- One explicit continuous presentation of a coanalytic Baire set by well-founded tree codes.
The structure records data supplied by the caller; no globally selected reduction is exported.-/
structure CoanalyticRankPresentation (A : Set (ℕ → ℕ)) where
  /-- Continuous tree code assigned to each Baire point.-/
  treeCode : (ℕ → ℕ) → TreeCode
  /-- Continuity of the tree-code assignment.-/
  continuous_treeCode : Continuous treeCode
  /-- The rank domain is exactly the original set.-/
  mem_iff : ∀ x, x ∈ A ↔ IsWellFounded (decodeTree (treeCode x))

namespace CoanalyticRankPresentation

variable {A : Set (ℕ → ℕ)} (P : CoanalyticRankPresentation A)

/-- The explicit domain cut out by the well-foundedness of the presented tree code.-/
def domain : Set (ℕ → ℕ) :=
  {x | IsWellFounded (decodeTree (P.treeCode x))}

/-- The presented tree is well-founded at every point of `A`.-/
theorem wellFounded {x : ℕ → ℕ} (hx : x ∈ A) :
    IsWellFounded (decodeTree (P.treeCode x)) :=
  (P.mem_iff x).1 hx

/-- The explicit rank domain is exactly `A`.-/
theorem domain_eq : P.domain = A := by
  ext x
  exact (P.mem_iff x).symm

/-- The ordinal rank obtained from the presented well-founded tree.-/
noncomputable def rank (x : ℕ → ℕ) (hx : x ∈ A) : Ordinal.{0} :=
  Tree.rank (decodeTree (P.treeCode x)) (P.wellFounded hx)

/-- Every value of a pulled-back tree rank is countable.-/
theorem rank_lt_omega_one (x : ℕ → ℕ) (hx : x ∈ A) :
    P.rank x hx < (ω₁ : Ordinal.{0}) :=
  Tree.treeRank_lt_omega_one _ (P.wellFounded hx)

/-- The coordinatewise map used to pull tree-rank comparisons back to Baire space.-/
def pairMap (p : (ℕ → ℕ) × (ℕ → ℕ)) : TreeCode × TreeCode :=
  (P.treeCode p.1, P.treeCode p.2)

/-- The comparison pullback map is continuous.-/
theorem continuous_pairMap : Continuous P.pairMap :=
  (P.continuous_treeCode.comp continuous_fst).prodMk
    (P.continuous_treeCode.comp continuous_snd)

/-- Analytic non-strict comparison pulled back from the tree rank.-/
def leAnalytic : Set ((ℕ → ℕ) × (ℕ → ℕ)) :=
  P.pairMap ⁻¹' treeRankLeAnalytic

/-- Coanalytic non-strict comparison pulled back from the tree rank.-/
def leCoanalytic : Set ((ℕ → ℕ) × (ℕ → ℕ)) :=
  P.pairMap ⁻¹' treeRankLeCoanalytic

/-- Analytic strict comparison pulled back from the tree rank.-/
def ltAnalytic : Set ((ℕ → ℕ) × (ℕ → ℕ)) :=
  P.pairMap ⁻¹' treeRankLtAnalytic

/-- Coanalytic strict comparison pulled back from the tree rank.-/
def ltCoanalytic : Set ((ℕ → ℕ) × (ℕ → ℕ)) :=
  P.pairMap ⁻¹' treeRankLtCoanalytic

/-- The pulled-back non-strict comparison has the analytic polarity.-/
theorem analyticSet_leAnalytic : MeasureTheory.AnalyticSet P.leAnalytic :=
  analyticSet_treeRankLeAnalytic.preimage P.continuous_pairMap

/-- The pulled-back non-strict comparison has the coanalytic polarity.-/
theorem isCoanalytic_leCoanalytic : IsCoanalytic P.leCoanalytic :=
  isCoanalytic_treeRankLeCoanalytic.preimage P.continuous_pairMap

/-- The pulled-back strict comparison has the analytic polarity.-/
theorem analyticSet_ltAnalytic : MeasureTheory.AnalyticSet P.ltAnalytic :=
  analyticSet_treeRankLtAnalytic.preimage P.continuous_pairMap

/-- The pulled-back strict comparison has the coanalytic polarity.-/
theorem isCoanalytic_ltCoanalytic : IsCoanalytic P.ltCoanalytic :=
  isCoanalytic_treeRankLtCoanalytic.preimage P.continuous_pairMap

/-- On a second coordinate in `A`, the analytic non-strict relation has exact rank semantics.-/
theorem mem_leAnalytic_iff {x y : ℕ → ℕ} (hy : y ∈ A) :
    (x, y) ∈ P.leAnalytic ↔
      ∃ hx : x ∈ A, P.rank x hx ≤ P.rank y hy := by
  change (P.treeCode x, P.treeCode y) ∈ treeRankLeAnalytic ↔ _
  rw [mem_treeRankLeAnalytic_iff_of_isWellFounded (P.wellFounded hy)]
  constructor
  · rintro ⟨hxf, hle⟩
    let hx : x ∈ A := (P.mem_iff x).2 hxf
    exact ⟨hx, by simpa [rank] using hle⟩
  · rintro ⟨hx, hle⟩
    exact ⟨P.wellFounded hx, by simpa [rank] using hle⟩

/-- On a second coordinate in `A`, the coanalytic non-strict relation has the same semantics.-/
theorem mem_leCoanalytic_iff {x y : ℕ → ℕ} (hy : y ∈ A) :
    (x, y) ∈ P.leCoanalytic ↔
      ∃ hx : x ∈ A, P.rank x hx ≤ P.rank y hy := by
  change (P.treeCode x, P.treeCode y) ∈ treeRankLeCoanalytic ↔ _
  rw [mem_treeRankLeCoanalytic_iff_of_isWellFounded (P.wellFounded hy)]
  constructor
  · rintro ⟨hxf, hle⟩
    let hx : x ∈ A := (P.mem_iff x).2 hxf
    exact ⟨hx, by simpa [rank] using hle⟩
  · rintro ⟨hx, hle⟩
    exact ⟨P.wellFounded hx, by simpa [rank] using hle⟩

/-- On a second coordinate in `A`, the analytic strict relation has exact rank semantics.-/
theorem mem_ltAnalytic_iff {x y : ℕ → ℕ} (hy : y ∈ A) :
    (x, y) ∈ P.ltAnalytic ↔
      ∃ hx : x ∈ A, P.rank x hx < P.rank y hy := by
  change (P.treeCode x, P.treeCode y) ∈ treeRankLtAnalytic ↔ _
  rw [mem_treeRankLtAnalytic_iff_of_isWellFounded (P.wellFounded hy)]
  constructor
  · rintro ⟨hxf, hlt⟩
    let hx : x ∈ A := (P.mem_iff x).2 hxf
    exact ⟨hx, by simpa [rank] using hlt⟩
  · rintro ⟨hx, hlt⟩
    exact ⟨P.wellFounded hx, by simpa [rank] using hlt⟩

/-- On a second coordinate in `A`, the coanalytic strict relation has the same semantics.-/
theorem mem_ltCoanalytic_iff {x y : ℕ → ℕ} (hy : y ∈ A) :
    (x, y) ∈ P.ltCoanalytic ↔
      ∃ hx : x ∈ A, P.rank x hx < P.rank y hy := by
  change (P.treeCode x, P.treeCode y) ∈ treeRankLtCoanalytic ↔ _
  rw [mem_treeRankLtCoanalytic_iff_of_isWellFounded (P.wellFounded hy)]
  constructor
  · rintro ⟨hxf, hlt⟩
    let hx : x ∈ A := (P.mem_iff x).2 hxf
    exact ⟨hx, by simpa [rank] using hlt⟩
  · rintro ⟨hx, hlt⟩
    exact ⟨P.wellFounded hx, by simpa [rank] using hlt⟩

/-- The two non-strict pointclass polarities agree on the exact rank domain.-/
theorem le_polarities_agree {x y : ℕ → ℕ} (hy : y ∈ A) :
    (x, y) ∈ P.leAnalytic ↔ (x, y) ∈ P.leCoanalytic := by
  rw [P.mem_leAnalytic_iff hy, P.mem_leCoanalytic_iff hy]

/-- The two strict pointclass polarities agree on the exact rank domain.-/
theorem lt_polarities_agree {x y : ℕ → ℕ} (hy : y ∈ A) :
    (x, y) ∈ P.ltAnalytic ↔ (x, y) ∈ P.ltCoanalytic := by
  rw [P.mem_ltAnalytic_iff hy, P.mem_ltCoanalytic_iff hy]

/-- The four definability and semantic clauses for the pulled-back coanalytic rank.-/
theorem comparison_isCoanalyticNorm :
    MeasureTheory.AnalyticSet P.leAnalytic ∧
      IsCoanalytic P.leCoanalytic ∧
        MeasureTheory.AnalyticSet P.ltAnalytic ∧
          IsCoanalytic P.ltCoanalytic ∧
            ∀ (y : ℕ → ℕ), ∀ hy : y ∈ A,
              (∀ x, ((∃ hx : x ∈ A, P.rank x hx ≤ P.rank y hy) ↔
                (x, y) ∈ P.leAnalytic)) ∧
              (∀ x, ((∃ hx : x ∈ A, P.rank x hx ≤ P.rank y hy) ↔
                (x, y) ∈ P.leCoanalytic)) ∧
              (∀ x, ((∃ hx : x ∈ A, P.rank x hx < P.rank y hy) ↔
                (x, y) ∈ P.ltAnalytic)) ∧
              (∀ x, ((∃ hx : x ∈ A, P.rank x hx < P.rank y hy) ↔
                (x, y) ∈ P.ltCoanalytic)) := by
  refine ⟨P.analyticSet_leAnalytic, P.isCoanalytic_leCoanalytic,
    P.analyticSet_ltAnalytic, P.isCoanalytic_ltCoanalytic, ?_⟩
  intro y hy
  exact ⟨fun x => (P.mem_leAnalytic_iff hy).symm,
    fun x => (P.mem_leCoanalytic_iff hy).symm,
    fun x => (P.mem_ltAnalytic_iff hy).symm,
    fun x => (P.mem_ltCoanalytic_iff hy).symm⟩

/-- Every analytic subset of the rank domain has one strict bound below `ω₁`.-/
theorem bounded_of_analytic {B : Set (ℕ → ℕ)} (hB : MeasureTheory.AnalyticSet B)
    (hBA : B ⊆ A) :
    ∃ ξ : Ordinal.{0}, ξ < ω₁ ∧
      ∀ (x : ℕ → ℕ), ∀ hx : x ∈ B, P.rank x (hBA hx) < ξ := by
  have himage : MeasureTheory.AnalyticSet (P.treeCode '' B) :=
    hB.image_of_continuous P.continuous_treeCode
  have himageWF : P.treeCode '' B ⊆ wellFoundedTrees := by
    rintro T ⟨x, hx, rfl⟩
    exact P.wellFounded (hBA hx)
  obtain ⟨ξ, hξ, hbound⟩ :=
    rank_bounded_of_analytic_subset_wellFounded himage himageWF
  refine ⟨ξ, hξ, fun x hx => ?_⟩
  simpa [rank] using
    hbound (P.treeCode x) ⟨x, hx, rfl⟩ (P.wellFounded (hBA hx))

end CoanalyticRankPresentation

/-- Every coanalytic subset of Baire space admits at least one continuous well-founded-tree rank
presentation. The theorem returns the presentation existentially and does not select a canonical
one.-/
theorem exists_coanalyticRankPresentation {A : Set (ℕ → ℕ)} (hA : IsCoanalytic A) :
    Nonempty (CoanalyticRankPresentation A) := by
  obtain ⟨f, hf, hmem⟩ :=
    (Tree.continuouslyReduces_wellFoundedTrees_of_isCoanalytic hA).exists_map
  exact ⟨{
    treeCode := f
    continuous_treeCode := hf
    mem_iff := fun x => (hmem x).trans Tree.mem_wellFoundedTrees
  }⟩

end DescriptiveSetTheory
