import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_pullback_snd_specMap_comp_of_isStableUnderBaseChange.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_pullback_snd_specMap_comp_of_isStableUnderBaseChange

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/--
@isnad1 id=var.0h9v.s7.f3c77ff96cb1 from=translated src=- shape=fa8d9b9e vocab=d8b581f9
-/
theorem solution
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] (i : R →+* S) (j : S →+* T)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (h : P (pullback.snd f (Spec.map (CommRingCat.ofHom i)))) :
    P (pullback.snd f (Spec.map (CommRingCat.ofHom (j.comp i)))) := by
  have hcomp : Spec.map (CommRingCat.ofHom (j.comp i)) =
      Spec.map (CommRingCat.ofHom j) ≫ Spec.map (CommRingCat.ofHom i) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  rw [hcomp, ← pullbackLeftPullbackSndIso_inv_snd_snd f (Spec.map (CommRingCat.ofHom i)) (Spec.map (CommRingCat.ofHom j))]
  rw [P.cancel_left_of_respectsIso]
  exact P.pullback_snd _ _ h
