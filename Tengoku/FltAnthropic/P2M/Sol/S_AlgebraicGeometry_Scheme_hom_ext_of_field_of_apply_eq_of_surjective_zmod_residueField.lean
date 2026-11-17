import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_Scheme_hom_ext_of_field_of_apply_eq_of_surjective_zmod_residueField.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_Scheme_hom_ext_of_field_of_apply_eq_of_surjective_zmod_residueField

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

/--
@isnad1 id=eq.3h7v.s9.5e21e0970d4a from=translated src=- shape=e142a698 vocab=61658d32
-/
theorem solution
    {X : Scheme.{u}} (x : X) (q : ℕ) [Fact q.Prime]
    (π : ZMod q →+* X.residueField x) (hπ : Function.Surjective π)
    {K : Type u} [Field K] (f g : Spec (CommRingCat.of K) ⟶ X)
    (hf : f.base (IsLocalRing.closedPoint K) = x) (hg : g.base (IsLocalRing.closedPoint K) = x) :
    f = g := by
  subst hf

  have hsub : ∀ (φ ψ : X.residueField (f.base (IsLocalRing.closedPoint K)) ⟶ CommRingCat.of K), φ = ψ := by
    intro φ ψ
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro t
    obtain ⟨a, rfl⟩ := hπ t
    have h1 : φ.hom.comp π = ψ.hom.comp π := Subsingleton.elim _ _
    exact RingHom.congr_fun h1 a
  apply (Scheme.SpecToEquivOfField K X).injective
  rw [Scheme.SpecToEquivOfField_eq_iff]
  exact ⟨hg.symm, hsub _ _⟩
