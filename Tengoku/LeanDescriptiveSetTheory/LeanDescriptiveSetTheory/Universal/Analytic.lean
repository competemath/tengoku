/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Analytic.TreeNormalForm
import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Spaces.BairePacking
import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Universal.Closed

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A universal analytic relation on Baire space

The parameter of the existing universal closed relation is a Cantor point. A Baire parameter is
sent continuously onto that Cantor code. The object and a Baire witness are packed into one Baire
point, producing a closed three-coordinate witness relation. Projecting the witness coordinate
gives an analytic subset of Baire space times Baire space whose vertical sections are exactly all
analytic subsets of Baire space.
-/

open Set

namespace DescriptiveSetTheory

/-- An analytic relation whose vertical sections are exactly a specified analytic pointclass.-/
def IsUniversalAnalytic {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
    (U : Set (P × X)) : Prop :=
  MeasureTheory.AnalyticSet U ∧ IsUniversalFor MeasureTheory.AnalyticSet U

/-- Every section of a universal analytic relation is analytic.
@isnad1 id=analytic.1h4v.s5.5c86b9e01b96 from=translated src=- shape=4dd7ecaa vocab=286a15f5
-/
theorem IsUniversalAnalytic.isAnalyticSet_verticalSection {P X : Type*}
    [TopologicalSpace P] [TopologicalSpace X] {U : Set (P × X)}
    (hU : IsUniversalAnalytic U) (p : P) :
    MeasureTheory.AnalyticSet (verticalSection U p) :=
  (hU.2 (verticalSection U p)).2 ⟨p, rfl⟩

/-- Every analytic set occurs as a vertical section of a universal analytic relation.
@isnad1 id=ex.2h4v.s5.630221dc844c from=translated src=- shape=4a7382ed vocab=286a15f5
-/
theorem IsUniversalAnalytic.exists_section {P X : Type*}
    [TopologicalSpace P] [TopologicalSpace X] {U : Set (P × X)}
    (hU : IsUniversalAnalytic U) {s : Set X} (hs : MeasureTheory.AnalyticSet s) :
    ∃ p, verticalSection U p = s :=
  (hU.2 s).1 hs

/-- Map a parameter/object/witness triple to the existing universal closed relation.-/
def baireUniversalAnalyticWitnessMap
    (z : ((ℕ → ℕ) × (ℕ → ℕ)) × (ℕ → ℕ)) : (ℕ → Bool) × (ℕ → ℕ) :=
  (baireToCantor z.1.1, packBairePair (z.1.2, z.2))

/-- The map defining the universal analytic witness relation is continuous.
@isnad1 id=continuo.0h0v.s6.8bf5611443b7 from=translated src=- shape=d327f42a vocab=4a118ca7
-/
theorem continuous_baireUniversalAnalyticWitnessMap :
    Continuous baireUniversalAnalyticWitnessMap := by
  exact (continuous_baireToCantor.comp (continuous_fst.comp continuous_fst)).prodMk
    (continuous_packBairePair.comp
      ((continuous_snd.comp continuous_fst).prodMk continuous_snd))

/-- The closed relation on `((parameter, object), witness)` triples.-/
def baireUniversalAnalyticWitness :
    Set (((ℕ → ℕ) × (ℕ → ℕ)) × (ℕ → ℕ)) :=
  baireUniversalAnalyticWitnessMap ⁻¹' baireUniversalClosed

/-- The three-coordinate witness relation is closed.
@isnad1 id=isclosed.0h0v.s5.5d861bea168a from=translated src=- shape=9a7a58f0 vocab=1af3129a
-/
theorem isClosed_baireUniversalAnalyticWitness :
    IsClosed baireUniversalAnalyticWitness :=
  isUniversalClosed_baireUniversalClosed.1.preimage
    continuous_baireUniversalAnalyticWitnessMap

/-- Project away the witness coordinate to obtain the universal analytic relation.-/
def baireUniversalAnalytic : Set ((ℕ → ℕ) × (ℕ → ℕ)) :=
  Prod.fst '' baireUniversalAnalyticWitness

/-- Membership is witnessed by a Baire point in the packed closed section.
@isnad1 id=iff.0h2v.s6.62fc5133bf87 from=translated src=- shape=9383ccb6 vocab=d8d66f4a
-/
theorem mem_baireUniversalAnalytic {p x : ℕ → ℕ} :
    (p, x) ∈ baireUniversalAnalytic ↔
      ∃ y : ℕ → ℕ,
        (baireToCantor p, packBairePair (x, y)) ∈ baireUniversalClosed := by
  constructor
  · rintro ⟨z, hz, hzx⟩
    rcases z with ⟨z, y⟩
    change z = (p, x) at hzx
    subst z
    exact ⟨y, hz⟩
  · rintro ⟨y, hy⟩
    exact ⟨((p, x), y), hy, rfl⟩

/-- Vertical-section membership has the expected parameter/object/witness orientation.
@isnad1 id=iff.0h2v.s6.83bbbf88f73f from=translated src=- shape=c16c225f vocab=39a3bbbd
-/
theorem mem_verticalSection_baireUniversalAnalytic {p x : ℕ → ℕ} :
    x ∈ verticalSection baireUniversalAnalytic p ↔
      ∃ y : ℕ → ℕ,
        (baireToCantor p, packBairePair (x, y)) ∈ baireUniversalClosed :=
  mem_baireUniversalAnalytic

/-- Code the three-coordinate witness relation as a closed subset of one Baire space.-/
def codedBaireUniversalAnalyticWitness : Set (ℕ → ℕ) :=
  unpackBaireTriple ⁻¹' baireUniversalAnalyticWitness

/-- The one-coordinate code of the witness relation is closed.
@isnad1 id=isclosed.0h0v.s3.f028e0634cb6 from=translated src=- shape=c69f195a vocab=312760e6
-/
theorem isClosed_codedBaireUniversalAnalyticWitness :
    IsClosed codedBaireUniversalAnalyticWitness :=
  isClosed_baireUniversalAnalyticWitness.preimage baireTripleHomeomorph.continuous

/-- Projecting the decoded parameter/object pair gives the same total relation.
@isnad1 id=eq.0h0v.s5.932aa4c7b9a7 from=translated src=- shape=2f26d161 vocab=ba234b1f
-/
theorem baireUniversalAnalytic_eq_image_codedWitness :
    baireUniversalAnalytic =
      (fun z => (unpackBaireTriple z).1) '' codedBaireUniversalAnalyticWitness := by
  apply Set.Subset.antisymm
  · rintro q ⟨z, hz, rfl⟩
    refine ⟨packBaireTriple z, ?_, ?_⟩
    · simpa [codedBaireUniversalAnalyticWitness] using hz
    · simp
  · rintro q ⟨z, hz, rfl⟩
    exact ⟨unpackBaireTriple z, hz, rfl⟩

/-- The total universal relation is analytic.
@isnad1 id=analytic.0h0v.s5.77c1a0a31d40 from=translated src=- shape=387f5a23 vocab=9f8cfa8f
-/
theorem analyticSet_baireUniversalAnalytic :
    MeasureTheory.AnalyticSet baireUniversalAnalytic := by
  rw [baireUniversalAnalytic_eq_image_codedWitness]
  exact isClosed_codedBaireUniversalAnalyticWitness.analyticSet.image_of_continuous
    (continuous_fst.comp baireTripleHomeomorph.continuous)

/-- Every vertical section of the relation is analytic.
@isnad1 id=analytic.0h1v.s4.472c9d89a483 from=translated src=- shape=8746caf6 vocab=85635da8
-/
theorem analyticSet_verticalSection_baireUniversalAnalytic (p : ℕ → ℕ) :
    MeasureTheory.AnalyticSet (verticalSection baireUniversalAnalytic p) :=
  analyticSet_baireUniversalAnalytic.preimage (continuous_const.prodMk continuous_id)

/-- Every analytic subset of Baire space occurs as an exact section.
@isnad1 id=ex.1h1v.s5.998a309f1f5c from=translated src=- shape=051a22be vocab=b70937c4
-/
theorem exists_verticalSection_baireUniversalAnalytic {s : Set (ℕ → ℕ)}
    (hs : MeasureTheory.AnalyticSet s) :
    ∃ p, verticalSection baireUniversalAnalytic p = s := by
  obtain ⟨T, hT⟩ :=
    (Tree.analyticSet_iff_exists_projectedBody_baire s).1 hs
  let c : Set (ℕ → ℕ) :=
    bairePairHomeomorph ⁻¹' Tree.pairedBody T
  have hc : IsClosed c :=
    (Tree.isClosed_pairedBody T).preimage bairePairHomeomorph.continuous
  obtain ⟨q, hq⟩ :=
    isUniversalClosed_baireUniversalClosed.exists_section hc
  refine ⟨cantorToBaire q, ?_⟩
  ext x
  rw [mem_verticalSection_baireUniversalAnalytic,
    baireToCantor_cantorToBaire]
  constructor
  · rintro ⟨y, hy⟩
    have hpack : packBairePair (x, y) ∈ c := by
      rw [← hq]
      exact hy
    have hxy : (x, y) ∈ Tree.pairedBody T := by
      simpa [c, packBairePair] using hpack
    rw [← hT]
    exact Tree.mem_projectedBody.2 ⟨y, hxy⟩
  · intro hx
    have hxT : x ∈ Tree.projectedBody T := by
      rw [hT]
      exact hx
    obtain ⟨y, hxy⟩ := Tree.mem_projectedBody.1 hxT
    refine ⟨y, ?_⟩
    have hpack : packBairePair (x, y) ∈ c := by
      simpa [c, packBairePair, Tree.pairedBody] using hxy
    rw [← hq] at hpack
    exact hpack

/-- `baireUniversalAnalytic` is universal for analytic subsets of Baire space.
@isnad1 id=isuniver.0h0v.s4.5f41d839b71b from=translated src=- shape=3b95f885 vocab=e984fc9b
-/
theorem isUniversalAnalytic_baireUniversalAnalytic :
    IsUniversalAnalytic baireUniversalAnalytic := by
  refine ⟨analyticSet_baireUniversalAnalytic, fun s => ?_⟩
  constructor
  · exact exists_verticalSection_baireUniversalAnalytic
  · rintro ⟨p, rfl⟩
    exact analyticSet_verticalSection_baireUniversalAnalytic p

end DescriptiveSetTheory
