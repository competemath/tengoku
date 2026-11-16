import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_CurveModel
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_GluedPic0

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicCurve_CurveModel_sub_algebraMap_mem_of_hasValue_placeOfPoint.lean`: wrote out 4 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_export`, 2 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicCurve_CurveModel_sub_algebraMap_mem_of_hasValue_placeOfPoint

set_option autoImplicit false

open _root_.CategoryTheory open _root_.CategoryTheory.Limits open _root_.AlgebraicGeometry open _root_.AlgebraicCurve
open scoped TensorProduct

universe u v

noncomputable section

namespace AlgebraicCurve
export _root_.AlgebraicCurve (baseToFunctionField CurveModel Place Place.coe_algebraMap Place.residue_algebraMap)
namespace CurveModel
export _root_.AlgebraicCurve.CurveModel (placeOfPoint toBase C range_stalk_eq ffEquiv ffEquiv_algebraMap mk)
namespace PlaceRead
open _root_.AlgebraicCurve.CurveModel open _root_.AlgebraicCurve

/--
@isnad1 id=eq.1h7v.s12.45d6a8124c3a from=translated src=- shape=6a887928 vocab=fab9df55
-/
theorem germToFunctionField_appIso_inv_base {Y : Scheme.{u}} [IsIntegral Y] {B : CommRingCat.{u}} (G : Spec B ⟶ Y)
    [IsOpenImmersion G] {K : Type u} [Field K] (y : Y ⟶ Spec (CommRingCat.of K)) (c : CommRingCat.of K ⟶ B)
    (hc : G ≫ y = Spec.map c) [Nonempty ((G ''ᵁ ⊤ : Y.Opens) : Scheme.{u})] (k : K) :
    Y.germToFunctionField (G ''ᵁ ⊤) ((G.appIso ⊤).inv ((Scheme.ΓSpecIso B).inv (c k))) =
      baseToFunctionField y k := by
  have e6 := CategoryTheory.ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality c) k
  rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply] at e6
  rw [e6, ← hc, Scheme.Hom.comp_appTop, CategoryTheory.comp_apply]
  have h2k := CategoryTheory.ConcreteCategory.congr_hom (G.app_appIso_inv ⊤) (y.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv k))
  rw [CategoryTheory.comp_apply] at h2k
  erw [h2k]
  erw [TopCat.Presheaf.germ_res_apply]
  rfl

variable {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]

/--
@isnad1 id=mem.3h8v.s13.970592f4ce13 from=translated src=- shape=9e6e2e39 vocab=72e17ffe
-/
theorem sub_algebraMap_mem_of_hasValue_placeOfPoint (M : CurveModel K L)
    {B : Type u} [CommRing B] [Algebra K B] (G : Spec (CommRingCat.of B) ⟶ M.C) [IsOpenImmersion G]
    (hG : G ≫ M.toBase = Spec.map (CommRingCat.ofHom (algebraMap K B)))
    [Nonempty ((G ''ᵁ ⊤ : M.C.Opens) : Scheme.{u})]
    (z : ↥(Spec (CommRingCat.of B))) (hz : G.base z ∈ closedPoints M.C)
    (f : B) (a : K)
    (hv : (M.placeOfPoint ⟨G.base z, hz⟩).HasValue
      (M.ffEquiv.symm (M.C.germToFunctionField (G ''ᵁ ⊤)
        ((G.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of B)).inv f)))) a) :
    f - algebraMap K B a ∈ z.asIdeal := by
  classical
  by_contra hfa
  set v := M.placeOfPoint ⟨G.base z, hz⟩ with hvdef

  let φ : M.C.presheaf.stalk (G.base z) →+* L :=
    (M.ffEquiv.symm : M.C.functionField ≃+* L).toRingHom.comp (algebraMap (M.C.presheaf.stalk (G.base z)) M.C.functionField)
  have hφrange : φ.range = v.toValuationSubring.toSubring := M.range_stalk_eq ⟨G.base z, hz⟩
  have hzW : G.base z ∈ (G ''ᵁ ⊤ : M.C.Opens) := ⟨z, trivial, rfl⟩
  let sec : B → Γ(M.C, G ''ᵁ ⊤) := fun b => (G.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b)
  have hread : ∀ b, M.ffEquiv.symm (M.C.germToFunctionField (G ''ᵁ ⊤) (sec b)) =
      φ (M.C.presheaf.germ (G ''ᵁ ⊤) (G.base z) hzW (sec b)) := by
    intro b
    show M.ffEquiv.symm _ = M.ffEquiv.symm _
    congr 1
    rw [RingHom.algebraMap_toAlgebra]
    exact (TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _).symm

  have hunit : IsUnit (M.C.presheaf.germ (G ''ᵁ ⊤) (G.base z) hzW (sec (f - algebraMap K B a))) := by
    rw [← Scheme.mem_basicOpen]
    show G.base z ∈ M.C.basicOpen ((G.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (f - algebraMap K B a)))
    rw [← Scheme.image_basicOpen, basicOpen_eq_of_affine]
    exact ⟨z, (PrimeSpectrum.mem_basicOpen _ z).mpr hfa, rfl⟩

  obtain ⟨u, hu⟩ := hunit
  have hmemφ : ∀ t, φ t ∈ v.toValuationSubring := fun t => by
    rw [← ValuationSubring.mem_toSubring, ← hφrange]; exact ⟨t, rfl⟩
  have hU : IsUnit (⟨φ u, hmemφ u⟩ : v.toValuationSubring) := by
    refine ⟨⟨⟨φ u, hmemφ u⟩, ⟨φ ↑u⁻¹, hmemφ _⟩, ?_, ?_⟩, rfl⟩
    · apply Subtype.ext; show φ u * φ ↑u⁻¹ = 1; rw [← map_mul, Units.mul_inv, map_one]
    · apply Subtype.ext; show φ ↑u⁻¹ * φ u = 1; rw [← map_mul, Units.inv_mul, map_one]

  have hconst : M.ffEquiv.symm (M.C.germToFunctionField (G ''ᵁ ⊤) (sec (algebraMap K B a))) = algebraMap K L a := by
    apply M.ffEquiv.injective
    rw [RingEquiv.apply_symm_apply, M.ffEquiv_algebraMap]
    exact germToFunctionField_appIso_inv_base G M.toBase (CommRingCat.ofHom (algebraMap K B)) hG a
  obtain ⟨hmem, hres⟩ := hv
  have hsecsub : sec (f - algebraMap K B a) = sec f - sec (algebraMap K B a) := by
    show (G.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (f - algebraMap K B a)) = _
    rw [map_sub, map_sub]
  have hval : (⟨φ u, hmemφ u⟩ : v.toValuationSubring) =
      ⟨_, hmem⟩ - algebraMap K v.toValuationSubring a := by
    apply Subtype.ext
    show φ u = (((⟨_, hmem⟩ : v.toValuationSubring) - algebraMap K v.toValuationSubring a : v.toValuationSubring) : L)
    rw [AddSubgroupClass.coe_sub, Place.coe_algebraMap, hu, hsecsub, map_sub, map_sub, ← hread, ← hread, hconst]
  have hres0 : IsLocalRing.residue v.toValuationSubring (⟨φ u, hmemφ u⟩ : v.toValuationSubring) = 0 := by
    rw [hval, map_sub, hres, ← Place.residue_algebraMap, sub_self]
  rw [IsLocalRing.residue_eq_zero_iff] at hres0
  exact hres0 hU

end AlgebraicCurve.CurveModel.PlaceRead

/--
@isnad1 id=mem.3h8v.s13.970592f4ce13 from=translated src=- shape=9e6e2e39 vocab=72e17ffe
-/
theorem solution
    {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L] (M : CurveModel K L)
    {B : Type u} [CommRing B] [Algebra K B] (G : Spec (CommRingCat.of B) ⟶ M.C) [IsOpenImmersion G]
    (hG : G ≫ M.toBase = Spec.map (CommRingCat.ofHom (algebraMap K B)))
    [Nonempty (Scheme.Opens.toScheme (G ''ᵁ ⊤))]
    (z : ↥(Spec (CommRingCat.of B))) (hz : G.base z ∈ closedPoints M.C)
    (f : B) (a : K)
    (hv : (M.placeOfPoint ⟨G.base z, hz⟩).HasValue
      (M.ffEquiv.symm (M.C.germToFunctionField (G ''ᵁ ⊤)
        ((G.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of B)).inv f)))) a) :
    f - algebraMap K B a ∈ z.asIdeal :=
  AlgebraicCurve.CurveModel.PlaceRead.sub_algebraMap_mem_of_hasValue_placeOfPoint M G hG z hz f a hv
