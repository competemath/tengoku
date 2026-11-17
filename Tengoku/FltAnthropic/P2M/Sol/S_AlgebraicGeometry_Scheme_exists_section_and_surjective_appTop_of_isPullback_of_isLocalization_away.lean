import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_Scheme_exists_section_and_surjective_appTop_of_isPullback_of_isLocalization_away.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_Scheme_exists_section_and_surjective_appTop_of_isPullback_of_isLocalization_away

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AwayBC

/--
@isnad1 id=surjecti.0h3v.s12.657aaaef832f from=translated src=- shape=8bd3024c vocab=f832f3b4
-/
theorem surjective_appTop_hom_of_iso {X Y : Scheme.{u}} (i : X ≅ Y) : Function.Surjective (i.hom.appTop).hom := by
  intro y
  refine ⟨i.inv.appTop.hom y, ?_⟩
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, Iso.hom_inv_id, Scheme.Hom.id_appTop]
  rfl

/--
@isnad1 id=surjecti.0h3v.s12.50a1f056db40 from=translated src=- shape=5a4cb813 vocab=6bdac895
-/
theorem surjective_appTop_inv_of_iso {X Y : Scheme.{u}} (i : X ≅ Y) : Function.Surjective (i.inv.appTop).hom :=
  surjective_appTop_hom_of_iso i.symm

/--
@isnad1 id=surjecti.2h8v.s16.8524253ab245 from=translated src=- shape=c0da2469 vocab=01f3fc3b
-/
theorem surjective_appTop_snd {B C₁ : Type u} [CommRing B] [CommRing C₁] [Algebra B C₁] (t : B) [IsLocalization.Away t C₁]
    {A P : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of B))
    (hΓt : Function.Surjective
      ((pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away t))))).appTop).hom)
    (fst : P ⟶ A) (snd : P ⟶ Spec (CommRingCat.of C₁))
    (hP : IsPullback fst snd f (Spec.map (CommRingCat.ofHom (algebraMap B C₁)))) :
    Function.Surjective (snd.appTop).hom := by
  classical
  set L := Localization.Away t with hL
  let φ : C₁ ≃ₐ[B] Localization.Away t := IsLocalization.algEquiv (Submonoid.powers t) C₁ (Localization.Away t)
  let iC : CommRingCat.of C₁ ≅ CommRingCat.of (Localization.Away t) := φ.toRingEquiv.toCommRingCatIso

  let e₃ : Spec (CommRingCat.of C₁) ≅ Spec (CommRingCat.of (Localization.Away t)) := (Scheme.Spec.mapIso iC.op).symm
  have he₃ : e₃.hom = Spec.map iC.inv := rfl
  have hkey : Spec.map (CommRingCat.ofHom (algebraMap B C₁)) ≫ (Iso.refl _).hom =
      e₃.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away t))) := by
    rw [Iso.refl_hom, Category.comp_id, he₃, ← Spec.map_comp]
    congr 1

    refine CommRingCat.hom_ext (RingHom.ext fun b => ?_)
    show algebraMap B C₁ b = φ.symm (algebraMap B (Localization.Away t) b)
    exact (φ.symm.commutes b).symm
  have hP' : IsPullback fst (snd ≫ e₃.hom) f (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away t)))) :=
    IsPullback.of_iso hP (Iso.refl _) (Iso.refl _) e₃ (Iso.refl _)
      (by simp) (by simp) (by simp) hkey
  have hsnd : snd = hP'.isoPullback.hom ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away t)))) ≫
      e₃.inv := by
    rw [← Category.assoc, IsPullback.isoPullback_hom_snd, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hsnd, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop]
  intro x
  obtain ⟨y, hy⟩ := surjective_appTop_hom_of_iso hP'.isoPullback x
  obtain ⟨z, hz⟩ := hΓt y
  obtain ⟨w, hw⟩ := surjective_appTop_inv_of_iso e₃ z
  refine ⟨w, ?_⟩
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply, hw, hz, hy]

end AwayBC

open AwayBC in
/--
@isnad1 id=ex.3h9v.s17.4713aa9222da from=translated src=- shape=99adcf89 vocab=abfbfde9
-/
theorem solution
    {B C : Type u} [CommRing B] [CommRing C] [Algebra B C] (t₀ : B) [IsLocalization.Away t₀ C]
    {A A' : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of B)) (e : Spec (CommRingCat.of B) ⟶ A) (he : e ≫ f = 𝟙 _)
    (hΓ : Function.Surjective (f.appTop).hom ∧
      ∀ t : B, Function.Surjective
        ((pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away t))))).appTop).hom)
    (f' : A' ⟶ Spec (CommRingCat.of C)) (g : A' ⟶ A)
    (hsq : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap B C)))) :
    ∃ e' : Spec (CommRingCat.of C) ⟶ A',
      e' ≫ f' = 𝟙 _ ∧ e' ≫ g = Spec.map (CommRingCat.ofHom (algebraMap B C)) ≫ e ∧
      Function.Surjective (f'.appTop).hom ∧
      ∀ r' : C, Function.Surjective
        ((pullback.snd f' (Spec.map (CommRingCat.ofHom (algebraMap C (Localization.Away r'))))).appTop).hom := by
  classical

  have hw : (Spec.map (CommRingCat.ofHom (algebraMap B C)) ≫ e) ≫ f =
      𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap B C)) := by
    rw [Category.assoc, he, Category.comp_id, Category.id_comp]
  refine ⟨hsq.lift _ _ hw, hsq.lift_snd _ _ hw, hsq.lift_fst _ _ hw, ?_, ?_⟩
  · exact surjective_appTop_snd t₀ f (hΓ.2 t₀) g f' hsq
  · intro r'

    set L' := Localization.Away r' with hL'
    obtain ⟨b, hb⟩ : ∃ b : B, Associated (algebraMap B C b) r' :=
      ⟨(IsLocalization.Away.sec t₀ r').1, IsLocalization.Away.associated_sec_fst t₀ r'⟩
    haveI : IsLocalization.Away (t₀ * b) (Localization.Away r') := IsLocalization.Away.mul_of_associated t₀ b r' hb

    have hsq1 := IsPullback.of_hasPullback f' (Spec.map (CommRingCat.ofHom (algebraMap C (Localization.Away r'))))
    have hbig := IsPullback.paste_horiz hsq1 hsq
    have hbot : Spec.map (CommRingCat.ofHom (algebraMap C (Localization.Away r'))) ≫ Spec.map (CommRingCat.ofHom (algebraMap B C)) =
        Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away r'))) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
    rw [hbot] at hbig
    exact surjective_appTop_snd (t₀ * b) f (hΓ.2 (t₀ * b)) _ _ hbig
