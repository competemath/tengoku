import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_CurveModel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicCurve_essFiniteType_functionField.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicCurve_essFiniteType_functionField

universe u

open CategoryTheory AlgebraicGeometry AlgebraicCurve

/--
@isnad1 id=essfinit.0h3v.s6.ae5d32fb169c from=translated src=- shape=cb7ab727 vocab=596afa84
-/
theorem solution
    {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [LocallyOfFiniteType c] :
    letI := (baseToFunctionField c).toAlgebra
    Algebra.EssFiniteType K C.functionField := by
  letI algKF : Algebra K C.functionField := (baseToFunctionField c).toAlgebra
  obtain ⟨x⟩ := (inferInstance : Nonempty C)
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
  haveI : Nonempty V := ⟨⟨x, hxV⟩⟩
  have e : V ≤ c ⁻¹ᵁ ⊤ := le_top

  let eK : Γ(Spec (CommRingCat.of K), ⊤) ≃+* K :=
    (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv
  have hft : ((c.appLE ⊤ V e).hom.comp eK.symm.toRingHom).FiniteType :=
    (c.finiteType_appLE (isAffineOpen_top _) hV e).comp
      (RingHom.FiniteType.of_surjective _ eK.symm.surjective)
  letI algKA : Algebra K Γ(C, V) := ((c.appLE ⊤ V e).hom.comp eK.symm.toRingHom).toAlgebra
  haveI : Algebra.FiniteType K Γ(C, V) := hft

  haveI : IsFractionRing Γ(C, V) C.functionField :=
    functionField_isFractionRing_of_isAffineOpen C V hV
  haveI : IsScalarTower K Γ(C, V) C.functionField := by
    refine IsScalarTower.of_algebraMap_eq fun k => ?_
    change baseToFunctionField c k =
      (C.germToFunctionField V).hom ((c.appLE ⊤ V e).hom (eK.symm k))
    simp only [baseToFunctionField, RingHom.coe_comp, Function.comp_apply, Scheme.Hom.appLE,
      Scheme.germToFunctionField, CommRingCat.hom_comp]
    rw [TopCat.Presheaf.germ_res_apply]
    rfl
  haveI : Algebra.EssFiniteType Γ(C, V) C.functionField :=
    Algebra.EssFiniteType.of_isLocalization C.functionField (nonZeroDivisors Γ(C, V))
  exact Algebra.EssFiniteType.comp K Γ(C, V) C.functionField
