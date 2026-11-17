import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_Scheme_PartialMap_mem_domain_toRationalMap_of_valuationRing_stalk.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_Scheme_PartialMap_mem_domain_toRationalMap_of_valuationRing_stalk

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace ValuativePartialMap

variable {X Y S : Scheme.{u}}

/--
@isnad1 id=eq.3h4v.s8.6f716629feb2 from=translated src=- shape=9509a4a1 vocab=07f09e15
-/
theorem fromSpecStalkOfMem_eq_of_specializes (U : X.Opens) {ξ x : X} (h : ξ ⤳ x)
    (hx : x ∈ U) (hξ : ξ ∈ U) :
    U.fromSpecStalkOfMem ξ hξ =
      Spec.map (X.presheaf.stalkSpecializes h) ≫ U.fromSpecStalkOfMem x hx := by
  rw [← cancel_mono U.ι, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι,
    Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]

/--
@isnad1 id=eq.3h5v.s8.06bb4ab6ed98 from=translated src=- shape=004aeeac vocab=09b25a7f
-/
theorem partialMap_fromSpecStalkOfMem_eq_of_specializes (f : X.PartialMap Y) {ξ x : X}
    (h : ξ ⤳ x) (hx : x ∈ f.domain) (hξ : ξ ∈ f.domain) :
    f.fromSpecStalkOfMem hξ =
      Spec.map (X.presheaf.stalkSpecializes h) ≫ f.fromSpecStalkOfMem hx := by
  change f.domain.fromSpecStalkOfMem ξ hξ ≫ f.hom =
    Spec.map (X.presheaf.stalkSpecializes h) ≫ f.domain.fromSpecStalkOfMem x hx ≫ f.hom
  rw [fromSpecStalkOfMem_eq_of_specializes f.domain h hx hξ, Category.assoc]

/--
@isnad1 id=eq.1h4v.s8.330959f21113 from=translated src=- shape=9c27422b vocab=0134a6e7
-/
theorem partialMap_fromFunctionField_eq_of_mem [IrreducibleSpace X] (f : X.PartialMap Y)
    {x : X} (hx : x ∈ f.domain) :
    f.fromFunctionField =
      Spec.map (X.presheaf.stalkSpecializes (genericPoint_specializes x)) ≫
        f.fromSpecStalkOfMem hx :=
  partialMap_fromSpecStalkOfMem_eq_of_specializes f (genericPoint_specializes x) hx
    ((genericPoint_specializes _).mem_open f.domain.2 f.dense_domain.nonempty.choose_spec)

/--
@isnad1 id=eq.0h2v.s8.72283ab4051d from=translated src=- shape=25eb15d4 vocab=b66501ca
-/
theorem ofHom_algebraMap_stalk_functionField [IrreducibleSpace X] (x : X) :
    CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField) =
      X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial) := by
  simp_rw [RingHom.algebraMap_toAlgebra]
  exact CommRingCat.ofHom_hom _

end ValuativePartialMap

open ValuativePartialMap in
set_option maxHeartbeats 6400000 in
set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=mem.2h8v.s7.b292f61e4db5 from=translated src=- shape=a1e0ed9f vocab=93eb4f53
-/
theorem solution {X Y S : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S) [IsIntegral X]
    [LocallyOfFiniteType sY] (hY : ValuativeCriterion.Existence sY) (f : X.PartialMap Y)
    (hf : f.hom ≫ sY = f.domain.ι ≫ sX) (x : X) (hx : ValuationRing (X.presheaf.stalk x)) :
    x ∈ f.toRationalMap.domain := by
  haveI := hx

  have hcomm : f.fromFunctionField ≫ sY =
      Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField)) ≫
        (X.fromSpecStalk x ≫ sX) := by
    rw [ofHom_algebraMap_stalk_functionField]
    change (f.domain.fromSpecStalkOfMem (genericPoint X) _ ≫ f.hom) ≫ sY = _
    rw [Category.assoc, hf, ← Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk_assoc]

  obtain ⟨l, hl₁, hl₂⟩ := (hY
    { R := X.presheaf.stalk x
      commRing := inferInstance
      domain := (inferInstance : IsDomain (X.presheaf.stalk x))
      valuationRing := hx
      K := X.functionField
      field := inferInstance
      algebra := (inferInstance : Algebra (X.presheaf.stalk x) X.functionField)
      isFractionRing := (inferInstance : IsFractionRing (X.presheaf.stalk x) X.functionField)
      i₁ := f.fromFunctionField
      i₂ := X.fromSpecStalk x ≫ sX
      commSq := ⟨hcomm⟩ }).exists_lift
  have hl₂' : l ≫ sY = X.fromSpecStalk x ≫ sX := hl₂
  have hl₁' : Spec.map (X.presheaf.stalkSpecializes
      ((genericPoint_spec X).specializes trivial)) ≫ l = f.fromFunctionField := by
    rw [← ofHom_algebraMap_stalk_functionField]
    exact hl₁

  refine Scheme.RationalMap.mem_domain.mpr
    ⟨Scheme.PartialMap.ofFromSpecStalk sX sY l hl₂',
     Scheme.PartialMap.mem_domain_ofFromSpecStalk sX sY l hl₂', ?_⟩
  apply Scheme.RationalMap.eq_of_fromFunctionField_eq
  rw [Scheme.RationalMap.fromFunctionField_toRationalMap,
    Scheme.RationalMap.fromFunctionField_toRationalMap,
    partialMap_fromFunctionField_eq_of_mem _
      (Scheme.PartialMap.mem_domain_ofFromSpecStalk sX sY l hl₂'),
    Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk sX sY l hl₂']
  exact hl₁'

end
