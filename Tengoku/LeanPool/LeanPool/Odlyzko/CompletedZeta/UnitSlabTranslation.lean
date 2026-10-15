/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Tengoku.LeanPool.LeanPool.Odlyzko.CompletedZeta.UnitFundamentalDomain

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.Units Set
  dirichletUnitTheorem

namespace NumberField.Odlyzko

open mixedEmbedding

variable {K : Type*} [Field K] [NumberField K]

open Classical in
/-- An unit coordinate shift hom used in the Odlyzko-bound argument. -/
noncomputable def unitCoordinateShiftHom :
    ({w : InfinitePlace K // w ≠ w₀} → ℤ) →+
      mixedEmbedding.realSpace K where
  toFun := unitCoordinateShift
  map_zero' := by
    ext w
    by_cases hw : w = w₀ <;> simp [unitCoordinateShift, hw]
  map_add' z z' := by
    ext w
    by_cases hw : w = w₀ <;> simp [unitCoordinateShift, hw]

open Classical in
/--
@isnad1 id=eq.0h2v.s8.496c7dfb7c21 from=translated src=- shape=112ea730 vocab=15f4d5e5
-/
@[simp]
theorem unitCoordinateShiftHom_apply
    (z : {w : InfinitePlace K // w ≠ w₀} → ℤ) :
    unitCoordinateShiftHom (K := K) z = unitCoordinateShift z :=
  rfl

open Classical in
/-- An unit coordinate lattice used in the Odlyzko-bound argument. -/
noncomputable def unitCoordinateLattice :
    AddSubgroup (mixedEmbedding.realSpace K) :=
  (unitCoordinateShiftHom (K := K)).range

open Classical in
/--
@isnad1 id=mem.0h2v.s6.1e76d4e1251a from=translated src=- shape=24ff2e8c vocab=e966da3c
-/
theorem unitCoordinateShift_mem_lattice
    (z : {w : InfinitePlace K // w ≠ w₀} → ℤ) :
    unitCoordinateShift z ∈ unitCoordinateLattice (K := K) :=
  ⟨z, rfl⟩

open Classical in
/--
@isnad1 id=eq.0h2v.s7.8fdd0571fbd5 from=translated src=- shape=f9eaa0c0 vocab=f0883a16
-/
theorem unitCoordinateLattice_apply_w₀
    (g : unitCoordinateLattice (K := K)) :
    (g : mixedEmbedding.realSpace K) w₀ = 0 := by
  obtain ⟨z, hz⟩ := g.prop
  rw [← hz]
  simp [unitCoordinateShift]

open Classical in
/--
@isnad1 id=countabl.0h1v.s6.77f302532d07 from=translated src=- shape=8f50d87a vocab=a53c9920
-/
noncomputable instance countable_unitCoordinateLattice :
    Countable (unitCoordinateLattice (K := K)) :=
  Function.Surjective.countable
    (f := fun z : {w : InfinitePlace K // w ≠ w₀} → ℤ ↦
      (⟨unitCoordinateShift z, unitCoordinateShift_mem_lattice z⟩ :
        unitCoordinateLattice (K := K)))
    (by
      intro g
      obtain ⟨z, hz⟩ := g.prop
      refine ⟨z, Subtype.ext ?_⟩
      simpa using hz)

open Classical in
/--
@isnad1 id=existsun.0h2v.s8.613b1e6fdd68 from=translated src=- shape=e517efce vocab=79075271
-/
theorem existsUnique_vadd_mem_unitFundamentalParamSet
    (x : mixedEmbedding.realSpace K) :
    ∃! g : unitCoordinateLattice (K := K),
      (g : mixedEmbedding.realSpace K) + x ∈ unitFundamentalParamSet K := by
  let z : {w : InfinitePlace K // w ≠ w₀} → ℤ :=
    fun i ↦ -unitFloor x i
  let g : unitCoordinateLattice (K := K) :=
    ⟨unitCoordinateShift z, unitCoordinateShift_mem_lattice z⟩
  refine ⟨g, ?_, ?_⟩
  · change (g : mixedEmbedding.realSpace K) + x ∈
      unitFundamentalParamSet K
    rw [mem_unitFundamentalParamSet_iff]
    intro w hw
    have hfract :
        Int.fract (x w) = (z ⟨w, hw⟩ : ℝ) + x w := by
      have h := Int.fract_add_floor (x w)
      dsimp [z]
      simp only [unitFloor, ite_eq_right hw]
      grind
    change unitCoordinateShift z w + x w ∈ Ico (0 : ℝ) 1
    rw [show unitCoordinateShift z w = (z ⟨w, hw⟩ : ℝ) by
      simp [unitCoordinateShift, hw]]
    rw [← hfract]
    exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  · intro g' hg'
    obtain ⟨z', hz'⟩ := g'.prop
    ext w
    by_cases hw : w = w₀
    · subst w
      rw [← hz']
      simp [g, unitCoordinateShift]
    · have hmem :=
        (mem_unitFundamentalParamSet_iff
          ((g' : mixedEmbedding.realSpace K) + x)).mp hg' w hw
      rw [← hz'] at hmem
      have hfloor :
          ⌊(z' ⟨w, hw⟩ : ℝ) + x w⌋ = 0 := by
        apply Int.floor_eq_zero_iff.mpr
        simpa [unitCoordinateShift, hw] using hmem
      have hzfloor :
          z' ⟨w, hw⟩ + ⌊x w⌋ = 0 := by simp_all
      rw [← hz']
      simp only [unitCoordinateShiftHom_apply]
      change unitCoordinateShift z' w = unitCoordinateShift z w
      rw [show unitCoordinateShift z' w = (z' ⟨w, hw⟩ : ℝ) by
        simp [unitCoordinateShift, hw]]
      rw [show unitCoordinateShift z w =
          ((-(unitFloor x w) : ℤ) : ℝ) by
        simp [unitCoordinateShift, z, hw]]
      norm_cast
      simpa [unitFloor, hw] using
        (eq_neg_of_add_eq_zero_left hzfloor)

open Classical in
/--
@isnad1 id=isaddfun.0h1v.s9.2b8c844b37b9 from=translated src=- shape=35b8c568 vocab=55654de7
-/
theorem isAddFundamentalDomain_unitFundamentalParamSet :
    IsAddFundamentalDomain (unitCoordinateLattice (K := K))
      (unitFundamentalParamSet K) volume :=
  IsAddFundamentalDomain.mk'
    measurableSet_unitFundamentalParamSet.nullMeasurableSet
    existsUnique_vadd_mem_unitFundamentalParamSet

open Classical in
/-- An unit fundamental real translate used in the Odlyzko-bound argument. -/
def unitFundamentalRealTranslate
    (a : mixedEmbedding.realSpace K) :
    Set (mixedEmbedding.realSpace K) :=
  (fun x ↦ x - a) ⁻¹' unitFundamentalParamSet K

open Classical in
/--
@isnad1 id=eq.0h2v.s6.b7e4b8cfb09c from=translated src=- shape=1040e849 vocab=a987e684
-/
theorem unitFundamentalRealTranslate_eq_image
    (a : mixedEmbedding.realSpace K) :
    unitFundamentalRealTranslate (K := K) a =
      (fun x ↦ x + a) '' unitFundamentalParamSet K := by
  ext x
  constructor
  · intro hx
    exact ⟨x - a, hx, by simp⟩
  · rintro ⟨y, hy, rfl⟩
    simpa [unitFundamentalRealTranslate] using hy

open Classical in
/--
@isnad1 id=measurab.0h2v.s5.7fb0398773b4 from=translated src=- shape=079b69e2 vocab=98a549f1
-/
theorem measurableSet_unitFundamentalRealTranslate
    (a : mixedEmbedding.realSpace K) :
    MeasurableSet (unitFundamentalRealTranslate (K := K) a) := by
  exact (measurable_id.sub_const a)
    measurableSet_unitFundamentalParamSet

open Classical in
/--
@isnad1 id=isaddfun.0h2v.s9.4ba16b963e08 from=translated src=- shape=70d83399 vocab=30b3c817
-/
theorem isAddFundamentalDomain_unitFundamentalRealTranslate
    (a : mixedEmbedding.realSpace K) :
    IsAddFundamentalDomain (unitCoordinateLattice (K := K))
      (unitFundamentalRealTranslate (K := K) a) volume := by
  apply IsAddFundamentalDomain.mk'
    (measurableSet_unitFundamentalRealTranslate a).nullMeasurableSet
  intro x
  obtain ⟨g, hg, huniq⟩ :=
    existsUnique_vadd_mem_unitFundamentalParamSet (K := K) (x - a)
  refine ⟨g, ?_, ?_⟩
  · change (g : mixedEmbedding.realSpace K) + x - a ∈
      unitFundamentalParamSet K
    (convert hg using 1; grind)
  · intro g' hg'
    apply huniq
    change (g' : mixedEmbedding.realSpace K) + x - a ∈
      unitFundamentalParamSet K at hg'
    (convert hg' using 1; grind)

open Classical in
/--
@isnad1 id=eq.0h4v.s7.af2bc65cd78e from=translated src=- shape=de377fa7 vocab=a2b9c7aa
-/
theorem setIntegral_add_unitFundamentalParamSet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : mixedEmbedding.realSpace K → E)
    (a : mixedEmbedding.realSpace K) :
    (∫ x in unitFundamentalParamSet K, f (x + a)) =
      ∫ x in unitFundamentalRealTranslate (K := K) a, f x := by
  let e : mixedEmbedding.realSpace K ≃ᵐ mixedEmbedding.realSpace K :=
    MeasurableEquiv.addRight a
  have he : MeasurePreserving e volume volume :=
    ⟨e.measurable, by
      simpa [e] using (map_add_right_eq_self volume a)⟩
  symm
  rw [unitFundamentalRealTranslate_eq_image]
  exact he.setIntegral_image_emb e.measurableEmbedding f
    (unitFundamentalParamSet K)

open Classical in
/--
@isnad1 id=eq.1h4v.s8.269166b20c04 from=translated src=- shape=f888fa1e vocab=e7e5cc5c
-/
theorem setIntegral_unitFundamentalParamSet_add_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : mixedEmbedding.realSpace K → E)
    (hf : ∀ (g : unitCoordinateLattice (K := K)) x,
      f ((g : mixedEmbedding.realSpace K) + x) = f x)
    (a : mixedEmbedding.realSpace K) :
    (∫ x in unitFundamentalParamSet K, f (x + a)) =
      ∫ x in unitFundamentalParamSet K, f x := by
  rw [setIntegral_add_unitFundamentalParamSet]
  exact
    (isAddFundamentalDomain_unitFundamentalRealTranslate a).setIntegral_eq
      isAddFundamentalDomain_unitFundamentalParamSet hf

open Classical in
/--
@isnad1 id=iff.1h4v.s8.fffa37e08e9e from=translated src=- shape=424be39d vocab=4b223b3e
-/
theorem integrableOn_unitFundamentalParamSet_comp_add_iff
    {E : Type*} [NormedAddCommGroup E]
    (f : mixedEmbedding.realSpace K → E)
    (hf : ∀ (g : unitCoordinateLattice (K := K)) x,
      f ((g : mixedEmbedding.realSpace K) + x) = f x)
    (a : mixedEmbedding.realSpace K) :
    IntegrableOn (fun x ↦ f (x + a)) (unitFundamentalParamSet K) ↔
      IntegrableOn f (unitFundamentalParamSet K) := by
  let e : mixedEmbedding.realSpace K ≃ᵐ mixedEmbedding.realSpace K :=
    MeasurableEquiv.addRight a
  have he : MeasurePreserving e volume volume :=
    ⟨e.measurable, by
      simpa [e] using (map_add_right_eq_self volume a)⟩
  have hpre :
      e ⁻¹' unitFundamentalRealTranslate (K := K) a =
        unitFundamentalParamSet K := by
    ext x
    simp [e, unitFundamentalRealTranslate]
  calc
    IntegrableOn (fun x ↦ f (x + a)) (unitFundamentalParamSet K) ↔
        IntegrableOn f (unitFundamentalRealTranslate (K := K) a) := by
      change IntegrableOn (f ∘ e) (unitFundamentalParamSet K) ↔ _
      rw [← hpre]
      exact he.integrableOn_comp_preimage e.measurableEmbedding
    _ ↔ IntegrableOn f (unitFundamentalParamSet K) :=
      (isAddFundamentalDomain_unitFundamentalRealTranslate a).integrableOn_iff
        isAddFundamentalDomain_unitFundamentalParamSet hf

end NumberField.Odlyzko
