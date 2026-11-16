import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_Etale_of_forall_existsUnique_lift.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_Etale_of_forall_existsUnique_lift

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace EtaleInfinitesimalEngine

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

def LiftProp : Prop :=
  ∀ (R S : Type u) [CommRing R] [CommRing S] (φ : R →+* S), Function.Surjective φ →
    RingHom.ker φ ^ 2 = ⊥ → ∀ (a : Spec (CommRingCat.of S) ⟶ X) (b : Spec (CommRingCat.of R) ⟶ Y),
      a ≫ f = Spec.map (CommRingCat.ofHom φ) ≫ b →
      ∃! l : Spec (CommRingCat.of R) ⟶ X, Spec.map (CommRingCat.ofHom φ) ≫ l = a ∧ l ≫ f = b

variable {f}

theorem formallyUnramified (hlift : LiftProp f) : FormallyUnramified f := by
  refine FormallyUnramified.of_hom_ext f fun R S φ hφ hker g₁ g₂ h₁ h₂ => ?_
  obtain ⟨l, -, huniq⟩ := hlift R S φ.hom hφ hker (Spec.map φ ≫ g₁) (g₁ ≫ f)
    (by simp only [CommRingCat.ofHom_hom, Category.assoc])
  have e₁ : g₁ = l := huniq g₁ ⟨by simp only [CommRingCat.ofHom_hom], rfl⟩
  have e₂ : g₂ = l := huniq g₂ ⟨by simp only [CommRingCat.ofHom_hom, h₁], h₂.symm⟩
  exact e₁.trans e₂.symm

section Smooth

variable (hlift : LiftProp f)
include hlift

end Smooth

end EtaleInfinitesimalEngine
