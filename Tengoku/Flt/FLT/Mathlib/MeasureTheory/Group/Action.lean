/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Kevin Buzzard, Ruben Van de Velde, David Ledvinka
-/
module

public import Tengoku
/-!
# TODO

* Make `α` implicit in `SMulInvariantMeasure`
* Rename `SMulInvariantMeasure` to `Measure.IsSMulInvariant`
-/

@[expose] public section

section MeasurableEmbeddingComap

open MeasureTheory Measure

@[to_additive]
lemma _root_.MeasurableEmbedding.isMulLeftInvariant_comap {G H : Type*}
    [Group G] [MeasurableSpace G] [MeasurableMul G]
    [Monoid H] [MeasurableSpace H] [MeasurableMul H]
    {φ : G →* H} (hφ : MeasurableEmbedding φ) (μ : Measure H) [IsMulLeftInvariant μ] :
    IsMulLeftInvariant (comap φ μ) where
  map_mul_left_eq_self g := by
    ext s hs
    rw [map_apply (by fun_prop) hs]
    repeat rw [MeasurableEmbedding.comap_apply hφ]
    have : φ '' ((fun x ↦ g * x) ⁻¹' s) = (fun x ↦ φ g * x) ⁻¹' (φ '' s) := by
      ext
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨g * y, hy, by simp⟩
      · intro ⟨y, yins, hy⟩
        refine ⟨g⁻¹ * y, by simp [yins], ?_⟩
        apply congrArg (φ g⁻¹ * ·) at hy
        simp_rw [← mul_assoc, ← φ.map_mul, inv_mul_cancel, map_one, one_mul] at hy
        exact hy
    rw [this, ← map_apply (by fun_prop), IsMulLeftInvariant.map_mul_left_eq_self]
    exact hφ.measurableSet_image.mpr hs

@[to_additive]
lemma _root_.MeasurableEmbedding.isMulRightInvariant_comap {G H : Type*}
    [Group G] [MeasurableSpace G] [MeasurableMul G]
    [Monoid H] [MeasurableSpace H] [MeasurableMul H]
    {φ : G →* H} (hφ : MeasurableEmbedding φ) (μ : Measure H) [IsMulRightInvariant μ] :
    IsMulRightInvariant (comap φ μ) where
  map_mul_right_eq_self g := by
    ext s hs
    rw [map_apply (by fun_prop) hs]
    repeat rw [MeasurableEmbedding.comap_apply hφ]
    have : φ '' ((fun x ↦ x * g) ⁻¹' s) = (fun x ↦ x * φ g) ⁻¹' (φ '' s) := by
      ext
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y * g, hy, by simp⟩
      · intro ⟨y, yins, hy⟩
        refine ⟨y * g⁻¹, by simp [yins], ?_⟩
        apply congrArg (· * φ g⁻¹) at hy
        simp_rw [mul_assoc, ← φ.map_mul, mul_inv_cancel, map_one, mul_one] at hy
        exact hy
    rw [this, ← map_apply (by fun_prop), IsMulRightInvariant.map_mul_right_eq_self]
    exact hφ.measurableSet_image.mpr hs

end MeasurableEmbeddingComap

open Subgroup Set
open scoped Pointwise

namespace MeasureTheory
variable {G α : Type*} [Group G] [MeasurableSpace G] [MeasurableSpace α]
  {H K : Subgroup G}

variable [MeasurableMul G]

@[to_additive]
local instance : MeasurableMul H where
  measurable_mul_const c := Measurable.subtype_mk (by measurability)
  measurable_const_mul c := Measurable.subtype_mk (by measurability)

/--
@isnad1 id=ismullef.1h3v.s7.93338d2fe38f from=translated src=- shape=ce572e78 vocab=85b36564
-/
@[to_additive]
lemma isMulLeftInvariant_subtypeVal (μ : Measure G) [μ.IsMulLeftInvariant]
  (hH : MeasurableSet (H : Set G)) : (μ.comap Subtype.val : Measure H).IsMulLeftInvariant :=
  have hφ : MeasurableEmbedding H.subtype := MeasurableEmbedding.subtype_coe hH
  hφ.isMulLeftInvariant_comap μ

/--
@isnad1 id=ismulrig.1h3v.s7.c676e163e9a1 from=translated src=- shape=ce572e78 vocab=8d83b814
-/
@[to_additive]
lemma isMulRightInvariant_subtypeVal (μ : Measure G) [μ.IsMulRightInvariant]
    (hH : MeasurableSet (H : Set G)) : (μ.comap Subtype.val : Measure H).IsMulRightInvariant :=
  have hφ : MeasurableEmbedding H.subtype := MeasurableEmbedding.subtype_coe hH
  hφ.isMulRightInvariant_comap μ

/--
@isnad1 id=eq.3h4v.s7.833f9cf4f19d from=translated src=- shape=c6983c45 vocab=1198ad0d
-/
@[to_additive index_mul_addHaar_addSubgroup_eq_addHaar_addSubgroup]
lemma index_mul_haar_subgroup_eq_haar_subgroup [H.IsFiniteRelIndex K] (hHK : H ≤ K)
    (hH : MeasurableSet (H : Set G)) (hK : MeasurableSet (K : Set G)) (μ : Measure G)
    [μ.IsMulLeftInvariant] : H.relIndex K * μ H = μ K := by
  have := isMulLeftInvariant_subtypeVal μ hK
  have := Subgroup.index_mul_measure (H.subgroupOf K) (measurable_subtype_coe hH)
    (μ.comap Subtype.val)
  rw [MeasurableEmbedding.comap_apply, MeasurableEmbedding.comap_apply] at this
  · simp only [image_univ, Subtype.range_coe_subtype, SetLike.setOfPred_mem_eq] at this
    unfold subgroupOf at this
    rwa [coe_comap, coe_subtype, Set.image_preimage_eq_of_subset (by simpa)] at this
  · exact .subtype_coe hK
  · exact .subtype_coe hK

end MeasureTheory
-- Tengoku: 1 registration(s) of this module made local so they do not change other libraries (generated)
