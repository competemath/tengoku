import Tengoku.Seed.AlgebraicGeometry.Morphisms.Flat
import Tengoku.Seed.AlgebraicGeometry.Morphisms.UnderlyingMap
import Tengoku.Seed.AlgebraicGeometry.IdealSheaf.Functorial
import Tengoku.Seed.RingTheory.RingHom.Flat
import Tengoku.Seed.RingTheory.LocalProperties.Basic
import Tengoku.Seed.RingTheory.Flat.FaithfullyFlat.Algebra
import Tengoku.Seed.Algebra.Category.Ring.Constructions
import Tengoku.Seed.LinearAlgebra.TensorProduct.RightExactness
import Tengoku.Seed.RingTheory.IsTensorProduct

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_Scheme_IdealSheafData_ideal_comap_of_le.lean`: wrote out 10 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 6 `p2m_export`, 4 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_ideal_comap_of_le

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TensorProduct

namespace Algebra
export _root_.Algebra (TensorProduct.rid ofId IsPushout TensorProduct.includeRight algebraMap TensorProduct.lTensor_ker IsPushout.equiv smul_def TensorProduct.includeLeft id TensorProduct.map)
namespace IsPushout
export _root_.Algebra.IsPushout (equiv symm)
open _root_.Algebra.IsPushout open _root_.Algebra

/--
@isnad1 id=eq.1h4v.s8.d0aafa13ee9a from=translated src=- shape=370924e3 vocab=81926f3d
-/
theorem ker_algebraMap_eq_map_ker
    (R B C P : Type*) [CommRing R] [CommRing B] [CommRing C] [CommRing P]
    [Algebra R B] [Algebra R C] [Algebra B P] [Algebra C P] [Algebra R P]
    [IsScalarTower R B P] [IsScalarTower R C P] [Algebra.IsPushout R B C P]
    (hC : Function.Surjective (algebraMap R C)) :
    RingHom.ker (algebraMap B P) = (RingHom.ker (algebraMap R C)).map (algebraMap R B) := by
  let e : B ⊗[R] C ≃ₐ[B] P := Algebra.IsPushout.equiv R B C P

  have h1 : algebraMap B P = e.toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := B) (B := C)).toRingHom := by
    ext b
    simp [e]
  rw [h1, RingHom.ker_comp_of_injective _ e.toRingEquiv.injective]

  let g : R →ₐ[R] C := Algebra.ofId R C
  have h2 : (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := B) (B := C)).toRingHom =
      (Algebra.TensorProduct.map (AlgHom.id R B) g).toRingHom.comp
        (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := B) (B := R)).toRingHom := by
    ext b
    simp [g]
  have h3 : RingHom.ker (Algebra.TensorProduct.map (AlgHom.id R B) g).toRingHom =
      (RingHom.ker (algebraMap R C)).map
        (Algebra.TensorProduct.includeRight (R := R) (A := B) (B := R)).toRingHom := by
    have := Algebra.TensorProduct.lTensor_ker (A := B) g hC
    simp [g] at this
    exact this
  rw [h2, ← RingHom.comap_ker, h3]

  let r : B ⊗[R] R ≃ₐ[R] B := Algebra.TensorProduct.rid R R B
  have h4 : (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := B) (B := R)).toRingHom =
      (r.toRingEquiv.symm : B →+* B ⊗[R] R) := by
    ext b
    apply r.toRingEquiv.injective
    simp [r]
  have h5 : (algebraMap R B) = (r.toRingEquiv : B ⊗[R] R →+* B).comp
      (Algebra.TensorProduct.includeRight (R := R) (A := B) (B := R)).toRingHom := by
    ext x
    simp [r, Algebra.smul_def]
  rw [h4, h5, ← Ideal.map_map, Ideal.comap_coe, Ideal.map_coe, Ideal.comap_symm]

end Algebra.IsPushout

namespace CommRingCat
export _root_.CommRingCat (hom_comp of Hom isPushout_iff_isPushout)
open _root_.CommRingCat

/--
@isnad1 id=eq.2h8v.s8.534dc51546b1 from=translated src=- shape=e58c2bc1 vocab=328958c0
-/
theorem ker_eq_map_ker_of_isPushout {R B C P : CommRingCat.{u}} {f : R ⟶ B} {g : R ⟶ C}
    {inl : B ⟶ P} {inr : C ⟶ P} (h : IsPushout f g inl inr)
    (hg : Function.Surjective g.hom) :
    RingHom.ker inl.hom = (RingHom.ker g.hom).map f.hom := by
  algebraize [f.hom, g.hom, inl.hom, inr.hom, inl.hom.comp f.hom]
  have hw : inl.hom.comp f.hom = inr.hom.comp g.hom := by
    simpa only [CommRingCat.hom_comp] using congr(($(h.w)).hom)
  have : IsScalarTower R C P := .of_algebraMap_eq' hw
  have : Algebra.IsPushout R B C P := CommRingCat.isPushout_iff_isPushout.mp h
  exact Algebra.IsPushout.ker_algebraMap_eq_map_ker R B C P hg

end CommRingCat

namespace AlgebraicGeometry
export _root_.AlgebraicGeometry (Scheme.Hom.resLE_comp_ι Scheme.Hom.map_appLE Scheme.Opens.topIso_inv Surjective isPushout_appTop_of_isPullback Scheme.Hom Scheme.Opens.ι_appIso isAffine_of_isAffineHom IsAffine Scheme Scheme.Hom.appTop Scheme.Opens.topIso_hom Flat isAffineOpen_top Scheme.IdealSheafData.ideal_map_of_isAffineHom Scheme.Hom.ker_apply Scheme.Opens Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE Scheme.Hom.resLE_app_top Scheme.Opens.ι_image_top IsAffineHom Scheme.IdealSheafData)
namespace Scheme
export _root_.AlgebraicGeometry.Scheme (Hom.resLE_comp_ι Hom.map_appLE Opens.topIso_inv Hom Γ Opens.ι_appIso topIso_hom Hom.appTop Opens.topIso_hom affineOpens IdealSheafData.ideal_map_of_isAffineHom Hom.ker_apply Opens Hom.appLE_map Hom.app_eq_appLE Hom.resLE_app_top Opens.ι_image_top restrict IdealSheafData)
namespace IdealSheafData
export _root_.AlgebraicGeometry.Scheme.IdealSheafData (comap_comp map subscheme subschemeι_app_surjective ideal ideal_map_of_isAffineHom subschemeι comap ker_subschemeι_app ideal_comap_of_isOpenImmersion)
namespace ComapLocal
open _root_.AlgebraicGeometry.Scheme.IdealSheafData open _root_.AlgebraicGeometry.Scheme open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y : Scheme.{u}}

/--
@isnad1 id=eq.0h4v.s12.7db7504f9d5e from=translated src=- shape=334aa15b vocab=ed26f500
-/
theorem ideal_comap_top [IsAffine X] [IsAffine Y] (I : X.IdealSheafData) (f : Y ⟶ X) :
    (I.comap f).ideal ⟨⊤, isAffineOpen_top Y⟩ =
      (I.ideal ⟨⊤, isAffineOpen_top X⟩).map f.appTop.hom := by
  have : IsAffine I.subscheme := isAffine_of_isAffineHom I.subschemeι
  have H := isPushout_appTop_of_isPullback (IsPullback.of_hasPullback f I.subschemeι)
  have := CommRingCat.ker_eq_map_ker_of_isPushout H
    (I.subschemeι_app_surjective ⟨⊤, isAffineOpen_top X⟩)
  rw [← ker_subschemeι_app I ⟨⊤, isAffineOpen_top X⟩, comap, Scheme.Hom.ker_apply]
  exact this

set_option backward.isDefEq.respectTransparency false in

/--
@isnad1 id=eq.1h6v.s12.5bc057259d13 from=translated src=- shape=bd63163f vocab=702ed77a
-/
theorem ideal_comap_of_le (I : X.IdealSheafData) (f : Y ⟶ X) (U : X.affineOpens)
    (V : Y.affineOpens) (hVU : (V : Y.Opens) ≤ f ⁻¹ᵁ (U : X.Opens)) :
    (I.comap f).ideal V = (I.ideal U).map (f.appLE U V hVU).hom := by

  suffices key : ∀ (U' : X.affineOpens) (V' : Y.affineOpens),
      U' = ⟨(U : X.Opens).ι ''ᵁ ⊤, by simpa only [Scheme.Opens.ι_image_top] using U.2⟩ →
      V' = ⟨(V : Y.Opens).ι ''ᵁ ⊤, by simpa only [Scheme.Opens.ι_image_top] using V.2⟩ →
      ∀ (e : (V' : Y.Opens) ≤ f ⁻¹ᵁ (U' : X.Opens)),
        (I.comap f).ideal V' = (I.ideal U').map (f.appLE U' V' e).hom from
    key U V (Subtype.ext (U : X.Opens).ι_image_top.symm)
      (Subtype.ext (V : Y.Opens).ι_image_top.symm) hVU
  rintro _ _ rfl rfl e
  have : IsAffine (U : X.Opens) := U.2
  have : IsAffine (V : Y.Opens) := V.2

  have h := ideal_comap_top (I.comap (U : X.Opens).ι) (f.resLE U V hVU)
  rw [← comap_comp, Scheme.Hom.resLE_comp_ι, comap_comp,
    ideal_comap_of_isOpenImmersion (I.comap f) (V : Y.Opens).ι,
    ideal_comap_of_isOpenImmersion I (U : X.Opens).ι] at h
  simp only [Scheme.Opens.ι_appIso, Iso.refl_inv, Scheme.Hom.appTop,
    Scheme.Hom.resLE_app_top] at h
  convert h using 2 <;> try rfl
  congr 1
  simp only [Scheme.Opens.topIso_hom, Scheme.Opens.topIso_inv, eqToHom_op, Scheme.Hom.appLE_map,
    Scheme.Hom.map_appLE]

end AlgebraicGeometry.Scheme.IdealSheafData.ComapLocal

open CategoryTheory _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_ideal_comap_of_le.AlgebraicGeometry in

/--
@isnad1 id=eq.1h6v.s12.5bc057259d13 from=translated src=- shape=bd63163f vocab=702ed77a
-/
theorem solution
    {X Y : Scheme.{u}} (I : X.IdealSheafData) (f : Y ⟶ X) (U : X.affineOpens)
    (V : Y.affineOpens) (hVU : (V : Y.Opens) ≤ f ⁻¹ᵁ (U : X.Opens)) :
    (I.comap f).ideal V = (I.ideal U).map (f.appLE U V hVU).hom :=
  AlgebraicGeometry.Scheme.IdealSheafData.ComapLocal.ideal_comap_of_le I f U V hVU
