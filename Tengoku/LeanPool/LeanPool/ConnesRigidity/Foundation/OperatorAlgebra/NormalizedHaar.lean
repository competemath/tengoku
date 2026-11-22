/-
Copyright (c) 2026 Utensil Song, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song, OpenAI
-/
/-

Derived in part from Apache-2.0 `openai/ten-proofs`, `ConnesRigidity.lean` at
94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6, lines 12472-12581.
Modifications: generalized the compact additive Haar lemmas from the paper
carriers to arbitrary compact groups and updated simplification proofs. Paper:
§3. See the upstream PORT_MAP.md.
-/
module

public import Tengoku.Seed.MeasureTheory.Measure.Haar.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
The normalized haar component of the Connes rigidity formalization.
-/

@[expose] public section
namespace Tengoku.LeanPool end Tengoku.LeanPool open Tengoku.LeanPool 
namespace Connes
namespace NormalizedHaar

open MeasureTheory TopologicalSpace

noncomputable section

universe u v

/-- The probability normalization of additive Haar measure on a compact group. Paper: §3. -/
def normalizedAddHaar
    (A : Type u) [AddGroup A] [TopologicalSpace A] [CompactSpace A]
    [IsTopologicalAddGroup A] [MeasurableSpace A] [BorelSpace A] : Measure A :=
  Measure.addHaarMeasure
    (⟨⟨Set.univ, isCompact_univ⟩, by
      simp only [interior_univ, Set.univ_nonempty]⟩ : PositiveCompacts A)

/--
@isnad1 id=isprobab.0h1v.s5.52b6777fd9cd from=translated src=- shape=de699033 vocab=ee8a4ab1
-/
instance normalizedAddHaar_isProbabilityMeasure
    (A : Type u) [AddGroup A] [TopologicalSpace A] [CompactSpace A]
    [IsTopologicalAddGroup A] [MeasurableSpace A] [BorelSpace A] :
    IsProbabilityMeasure (normalizedAddHaar A) where
  measure_univ := by
    simpa only [normalizedAddHaar, interior_univ, Set.univ_nonempty,
      PositiveCompacts.coe_mk, Compacts.coe_mk] using
      (Measure.addHaarMeasure_self
        (K₀ := (⟨⟨Set.univ, isCompact_univ⟩, by
          simp only [interior_univ, Set.univ_nonempty]⟩ : PositiveCompacts A)))

/--
@isnad1 id=isaddhaa.0h1v.s5.a43dd07ac52e from=translated src=- shape=21c02aa3 vocab=3859bd96
-/
instance normalizedAddHaar_isAddHaarMeasure
    (A : Type u) [AddGroup A] [TopologicalSpace A] [CompactSpace A]
    [IsTopologicalAddGroup A] [MeasurableSpace A] [BorelSpace A] :
    Measure.IsAddHaarMeasure (normalizedAddHaar A) := by
  unfold normalizedAddHaar
  infer_instance

/-- Probability-normalized additive Haar measure is unique. Paper: §3.
@isnad1 id=eq.0h2v.s6.f11deea69e1a from=translated src=- shape=40f860b8 vocab=bb2f18ea
-/
theorem normalizedAddHaar_unique
    (A : Type u) [AddGroup A] [TopologicalSpace A] [CompactSpace A]
    [IsTopologicalAddGroup A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ]
    [Measure.IsAddLeftInvariant μ] :
    μ = normalizedAddHaar A := by
  let U : PositiveCompacts A :=
    ⟨⟨Set.univ, isCompact_univ⟩, by
      simp only [interior_univ, Set.univ_nonempty]⟩
  have h := Measure.addHaarMeasure_unique μ U
  change μ = μ Set.univ • normalizedAddHaar A at h
  simpa only [measure_univ, one_smul] using h

/-- A continuous fiber shear by an additive term preserves product Haar measure. Paper: §3.
@isnad1 id=measurep.1h7v.s7.b1dc06159437 from=translated src=- shape=46e81bff vocab=04f72401
-/
theorem skew_add_translation_measurePreserving
    {P : Type u} {Q : Type v} [AddCommGroup P] [AddCommGroup Q]
    [TopologicalSpace P] [TopologicalSpace Q]
    [IsTopologicalAddGroup P] [IsTopologicalAddGroup Q]
    [SecondCountableTopology Q]
    [MeasurableSpace P] [BorelSpace P]
    [MeasurableSpace Q] [BorelSpace Q]
    (μ : Measure P) (ν : Measure Q) [SFinite μ] [SFinite ν]
    [Measure.IsAddLeftInvariant μ] [Measure.IsAddLeftInvariant ν]
    (a : P) (b : Q) (c : P → Q) (hc : Continuous c) :
    MeasurePreserving
      (fun z : P × Q ↦ (a + z.1, b + z.2 + c z.1))
      (μ.prod ν) (μ.prod ν) := by
  refine MeasurePreserving.skew_product (μc := ν) (μd := ν)
    (g := fun x : P ↦ fun y : Q ↦ b + y + c x)
    (measurePreserving_add_left μ a) ?_ ?_
  · exact (measurable_const.add measurable_snd).add
      (hc.measurable.comp measurable_fst)
  · refine Filter.Eventually.of_forall fun x ↦ ?_
    convert map_add_left_eq_self ν (b + c x) using 1
    congr 1
    funext y
    abel

/-- Product probability Haar measure for two compact additive groups. Paper: §3. -/
def productHaar
    (P : Type u) (Q : Type v)
    [AddGroup P] [AddGroup Q]
    [TopologicalSpace P] [TopologicalSpace Q]
    [CompactSpace P] [CompactSpace Q]
    [IsTopologicalAddGroup P] [IsTopologicalAddGroup Q]
    [MeasurableSpace P] [BorelSpace P]
    [MeasurableSpace Q] [BorelSpace Q] : Measure (P × Q) :=
  (normalizedAddHaar P).prod (normalizedAddHaar Q)

/--
@isnad1 id=isprobab.0h2v.s6.5192e6e4d6b1 from=translated src=- shape=5c1f54c0 vocab=1b3fbf49
-/
instance productHaar_isProbabilityMeasure
    (P : Type u) (Q : Type v)
    [AddGroup P] [AddGroup Q]
    [TopologicalSpace P] [TopologicalSpace Q]
    [CompactSpace P] [CompactSpace Q]
    [IsTopologicalAddGroup P] [IsTopologicalAddGroup Q]
    [MeasurableSpace P] [BorelSpace P]
    [MeasurableSpace Q] [BorelSpace Q] :
    IsProbabilityMeasure (productHaar P Q) := by
  unfold productHaar
  infer_instance

/--
@isnad1 id=isaddlef.0h2v.s6.3dcb5dc5f50d from=translated src=- shape=e6b57b50 vocab=7ae53f5b
-/
instance productHaar_isAddLeftInvariant
    (P : Type u) (Q : Type v)
    [AddCommGroup P] [AddCommGroup Q]
    [TopologicalSpace P] [TopologicalSpace Q]
    [CompactSpace P] [CompactSpace Q]
    [IsTopologicalAddGroup P] [IsTopologicalAddGroup Q]
    [MeasurableSpace P] [BorelSpace P]
    [MeasurableSpace Q] [BorelSpace Q] :
    Measure.IsAddLeftInvariant (productHaar P Q) where
  map_add_left_eq_self z := by
    have hp := measurePreserving_add_left (normalizedAddHaar P) z.1
    have hq := measurePreserving_add_left (normalizedAddHaar Q) z.2
    change
      Measure.map
          (fun p : P × Q ↦ (z.1 + p.1, z.2 + p.2))
          ((normalizedAddHaar P).prod (normalizedAddHaar Q)) =
        (normalizedAddHaar P).prod (normalizedAddHaar Q)
    exact (hp.prod hq).map_eq

/-- The product measure agrees with normalized Haar measure on the product group. Paper: §3.
@isnad1 id=eq.0h2v.s6.85b764881d36 from=translated src=- shape=9917c3b3 vocab=c925cf76
-/
theorem productHaar_eq_normalizedAddHaar
    (P : Type u) (Q : Type v)
    [AddCommGroup P] [AddCommGroup Q]
    [TopologicalSpace P] [TopologicalSpace Q]
    [CompactSpace P] [CompactSpace Q]
    [IsTopologicalAddGroup P] [IsTopologicalAddGroup Q]
    [SecondCountableTopology P] [SecondCountableTopology Q]
    [MeasurableSpace P] [BorelSpace P]
    [MeasurableSpace Q] [BorelSpace Q] :
    productHaar P Q = normalizedAddHaar (P × Q) :=
  normalizedAddHaar_unique (P × Q) (productHaar P Q)

end
end NormalizedHaar
end Connes
-- Tengoku: root names of this library moved to Tengoku.LeanPool so they do not collide with other libraries (generated)
