/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Analytic.BorelCharacterization
import Tengoku.Seed.SetTheory.Cardinal.Aleph

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Abstract coanalytic ranks

`CoanalyticRank A` packages an ordinal-valued rank on a coanalytic subset `A` of a Polish space.
It records analytic and coanalytic presentations of the strict and non-strict comparisons, their
exact semantics on `A`, countability of every value, and the analytic boundedness law.

The boundedness law is an explicit field: this file does not claim to derive it solely from the
four comparison pointclasses. Concrete constructors must supply that proof. This enriched
interface is useful because both well-founded-tree ranks and continuously pulled-back ranks
satisfy all of its clauses.
-/

open Cardinal Ordinal Set

universe u v

namespace DescriptiveSetTheory

/-- An enriched coanalytic rank on `A`. The value is proof-indexed so it is defined only on the
rank domain; proof irrelevance makes all comparison statements independent of membership proofs.
The four relation fields may differ away from a second coordinate in `A`.-/
structure CoanalyticRank (X : Type u) [TopologicalSpace X] [PolishSpace X] (A : Set X) where
  /-- Ordinal value on the exact rank domain.-/
  rank : ∀ x, x ∈ A → Ordinal.{0}
  /-- Analytic presentation of non-strict comparison.-/
  leAnalytic : Set (X × X)
  /-- Coanalytic presentation of non-strict comparison.-/
  leCoanalytic : Set (X × X)
  /-- Analytic presentation of strict comparison.-/
  ltAnalytic : Set (X × X)
  /-- Coanalytic presentation of strict comparison.-/
  ltCoanalytic : Set (X × X)
  /-- The exact rank domain is coanalytic.-/
  isCoanalytic_domain : IsCoanalytic A
  /-- Pointclass of the analytic non-strict presentation.-/
  analyticSet_leAnalytic : MeasureTheory.AnalyticSet leAnalytic
  /-- Pointclass of the coanalytic non-strict presentation.-/
  isCoanalytic_leCoanalytic : IsCoanalytic leCoanalytic
  /-- Pointclass of the analytic strict presentation.-/
  analyticSet_ltAnalytic : MeasureTheory.AnalyticSet ltAnalytic
  /-- Pointclass of the coanalytic strict presentation.-/
  isCoanalytic_ltCoanalytic : IsCoanalytic ltCoanalytic
  /-- Exact non-strict semantics for the analytic presentation.-/
  mem_leAnalytic_iff : ∀ {x y}, ∀ hy : y ∈ A,
    (x, y) ∈ leAnalytic ↔ ∃ hx : x ∈ A, rank x hx ≤ rank y hy
  /-- Exact non-strict semantics for the coanalytic presentation.-/
  mem_leCoanalytic_iff : ∀ {x y}, ∀ hy : y ∈ A,
    (x, y) ∈ leCoanalytic ↔ ∃ hx : x ∈ A, rank x hx ≤ rank y hy
  /-- Exact strict semantics for the analytic presentation.-/
  mem_ltAnalytic_iff : ∀ {x y}, ∀ hy : y ∈ A,
    (x, y) ∈ ltAnalytic ↔ ∃ hx : x ∈ A, rank x hx < rank y hy
  /-- Exact strict semantics for the coanalytic presentation.-/
  mem_ltCoanalytic_iff : ∀ {x y}, ∀ hy : y ∈ A,
    (x, y) ∈ ltCoanalytic ↔ ∃ hx : x ∈ A, rank x hx < rank y hy
  /-- Every value is a countable ordinal.-/
  rank_lt_omega_one : ∀ x, ∀ hx : x ∈ A, rank x hx < (ω₁ : Ordinal.{0})
  /-- Every analytic subfamily of the domain has one strict countable bound.-/
  boundedOn_analytic : ∀ {B : Set X}, ∀ _hB : MeasureTheory.AnalyticSet B,
    ∀ hBA : B ⊆ A, ∃ ξ : Ordinal.{0}, ξ < ω₁ ∧
      ∀ x, ∀ hx : x ∈ B, rank x (hBA hx) < ξ

namespace CoanalyticRank

variable {X : Type u} [TopologicalSpace X] [PolishSpace X]
variable {A : Set X} (R : CoanalyticRank X A)

/-- Strict stage below the realized rank of `y`.-/
def stageAt (y : X) (hy : y ∈ A) : Set X :=
  {x | ∃ hx : x ∈ A, R.rank x hx < R.rank y hy}

/-- A realized strict stage is the horizontal section of the analytic comparison.
@isnad1 id=eq.1h4v.s6.2a60c5a2a3f9 from=translated src=- shape=e53d216a vocab=91cb45d1
-/
theorem stageAt_eq_ltAnalytic_section (y : X) (hy : y ∈ A) :
    R.stageAt y hy = {x | (x, y) ∈ R.ltAnalytic} := by
  ext x
  exact (R.mem_ltAnalytic_iff hy).symm

/-- The same realized strict stage is the horizontal section of the coanalytic comparison.
@isnad1 id=eq.1h4v.s6.33dcc7b6cf8d from=translated src=- shape=e53d216a vocab=a405e300
-/
theorem stageAt_eq_ltCoanalytic_section (y : X) (hy : y ∈ A) :
    R.stageAt y hy = {x | (x, y) ∈ R.ltCoanalytic} := by
  ext x
  exact (R.mem_ltCoanalytic_iff hy).symm

/-- Every realized strict stage is analytic.
@isnad1 id=analytic.1h4v.s5.fe3bb7c71150 from=translated src=- shape=11582703 vocab=347b66a2
-/
theorem analyticSet_stageAt (y : X) (hy : y ∈ A) :
    MeasureTheory.AnalyticSet (R.stageAt y hy) := by
  rw [R.stageAt_eq_ltAnalytic_section y hy]
  simpa [Set.preimage] using
    R.analyticSet_ltAnalytic.preimage (continuous_id.prodMk continuous_const)

/-- Every realized strict stage is coanalytic.
@isnad1 id=iscoanal.1h4v.s5.de275170eabc from=translated src=- shape=11582703 vocab=1e58c8d8
-/
theorem isCoanalytic_stageAt (y : X) (hy : y ∈ A) :
    IsCoanalytic (R.stageAt y hy) := by
  rw [R.stageAt_eq_ltCoanalytic_section y hy]
  simpa [Set.preimage] using
    R.isCoanalytic_ltCoanalytic.preimage (continuous_id.prodMk continuous_const)

/-- Every realized strict stage is Borel. This derives measurability from the two comparison
polarities instead of repeating a recursion on tree ranks.
@isnad1 id=measurab.1h4v.s5.4d2e6506b15d from=translated src=- shape=08da6862 vocab=f4ebe099
-/
theorem measurableSet_stageAt [MeasurableSpace X] [BorelSpace X]
    (y : X) (hy : y ∈ A) : MeasurableSet (R.stageAt y hy) :=
  measurableSet_iff_analyticSet_and_isCoanalytic.mpr
    ⟨R.analyticSet_stageAt y hy, R.isCoanalytic_stageAt y hy⟩

/-- The coordinatewise map induced by a continuous reduction.-/
def pullbackPairMap {Y : Type v} (f : X → Y) (p : X × X) : Y × Y :=
  (f p.1, f p.2)

omit [PolishSpace X] in
/-- The coordinatewise map induced by a continuous reduction is continuous.
@isnad1 id=continuo.1h3v.s5.ddf847a6d392 from=translated src=- shape=8224b57e vocab=2ebc2046
-/
theorem continuous_pullbackPairMap {Y : Type v} [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f) : Continuous (pullbackPairMap f) :=
  (hf.comp continuous_fst).prodMk (hf.comp continuous_snd)

/-- Pull a coanalytic rank back along a continuous map. The new domain is exactly the preimage;
all four comparison polarities and the analytic boundedness law are preserved.-/
noncomputable def pullback {Y : Type v} [TopologicalSpace Y] [PolishSpace Y]
    {B : Set Y} (S : CoanalyticRank Y B) (f : X → Y) (hf : Continuous f) :
    CoanalyticRank X (f ⁻¹' B) where
  rank x hx := S.rank (f x) hx
  leAnalytic := pullbackPairMap f ⁻¹' S.leAnalytic
  leCoanalytic := pullbackPairMap f ⁻¹' S.leCoanalytic
  ltAnalytic := pullbackPairMap f ⁻¹' S.ltAnalytic
  ltCoanalytic := pullbackPairMap f ⁻¹' S.ltCoanalytic
  isCoanalytic_domain := S.isCoanalytic_domain.preimage hf
  analyticSet_leAnalytic :=
    S.analyticSet_leAnalytic.preimage (continuous_pullbackPairMap f hf)
  isCoanalytic_leCoanalytic :=
    S.isCoanalytic_leCoanalytic.preimage (continuous_pullbackPairMap f hf)
  analyticSet_ltAnalytic :=
    S.analyticSet_ltAnalytic.preimage (continuous_pullbackPairMap f hf)
  isCoanalytic_ltCoanalytic :=
    S.isCoanalytic_ltCoanalytic.preimage (continuous_pullbackPairMap f hf)
  mem_leAnalytic_iff := by
    intro x y hy
    exact S.mem_leAnalytic_iff hy
  mem_leCoanalytic_iff := by
    intro x y hy
    exact S.mem_leCoanalytic_iff hy
  mem_ltAnalytic_iff := by
    intro x y hy
    exact S.mem_ltAnalytic_iff hy
  mem_ltCoanalytic_iff := by
    intro x y hy
    exact S.mem_ltCoanalytic_iff hy
  rank_lt_omega_one := fun x hx => S.rank_lt_omega_one (f x) hx
  boundedOn_analytic := by
    intro C hC hCB
    have himage : MeasureTheory.AnalyticSet (f '' C) := hC.image_of_continuous hf
    have himageB : f '' C ⊆ B := by
      rintro y ⟨x, hx, rfl⟩
      exact hCB hx
    obtain ⟨ξ, hξ, hbound⟩ := S.boundedOn_analytic himage himageB
    refine ⟨ξ, hξ, fun x hx => ?_⟩
    exact hbound (f x) ⟨x, hx, rfl⟩

/-- Pullback rank values are definitionally the original values after applying the map.
@isnad1 id=eq.2h6v.s6.4a3fa57abe92 from=translated src=- shape=5a88d27b vocab=5ae6ad4b
-/
@[simp] theorem pullback_rank {Y : Type v} [TopologicalSpace Y] [PolishSpace Y]
    {B : Set Y} (S : CoanalyticRank Y B) (f : X → Y) (hf : Continuous f)
    (x : X) (hx : x ∈ f ⁻¹' B) :
    (S.pullback f hf).rank x hx = S.rank (f x) hx := rfl

end CoanalyticRank

end DescriptiveSetTheory
