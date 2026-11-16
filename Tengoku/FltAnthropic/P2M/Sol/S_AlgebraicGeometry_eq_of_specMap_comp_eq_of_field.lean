import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_eq_of_specMap_comp_eq_of_field.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_eq_of_specMap_comp_eq_of_field

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem solution
    {X : Scheme.{0}} {κ κ' : Type} [Field κ] [Field κ'] (i : κ →+* κ')
    (P Q : Spec (CommRingCat.of κ) ⟶ X)
    (h : Spec.map (CommRingCat.ofHom i) ≫ P = Spec.map (CommRingCat.ofHom i) ≫ Q) :
    P = Q := by
  obtain ⟨⟨xP, φP⟩, rfl⟩ := (Scheme.SpecToEquivOfField κ X).symm.surjective P
  obtain ⟨⟨xQ, φQ⟩, rfl⟩ := (Scheme.SpecToEquivOfField κ X).symm.surjective Q
  have key : ∀ (x : ↥X) (φ : X.residueField x ⟶ CommRingCat.of κ),
      Spec.map (CommRingCat.ofHom i) ≫ (Scheme.SpecToEquivOfField κ X).symm ⟨x, φ⟩ =
        (Scheme.SpecToEquivOfField κ' X).symm ⟨x, φ ≫ CommRingCat.ofHom i⟩ := by
    intro x φ
    show Spec.map (CommRingCat.ofHom i) ≫ (Spec.map φ ≫ X.fromSpecResidueField x) =
      Spec.map (φ ≫ CommRingCat.ofHom i) ≫ X.fromSpecResidueField x
    rw [Spec.map_comp, Category.assoc]
  rw [key, key] at h
  have h2 := (Scheme.SpecToEquivOfField κ' X).symm.injective h
  rw [Scheme.SpecToEquivOfField_eq_iff] at h2
  obtain ⟨hx, hφ⟩ := h2
  dsimp only at hx
  subst hx
  congr 1
  rw [Scheme.SpecToEquivOfField_eq_iff]
  refine ⟨rfl, ?_⟩
  haveI : Mono (CommRingCat.ofHom i) := ConcreteCategory.mono_of_injective _ i.injective
  rw [← cancel_mono (CommRingCat.ofHom i)]
  simpa using hφ
