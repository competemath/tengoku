import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_IsClosedImmersion_exists_iso_hom_comp_eq_of_range_eq.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_IsClosedImmersion_exists_iso_hom_comp_eq_of_range_eq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/--
@isnad1 id=ex.1h5v.s8.26dc14e885fa from=translated src=- shape=3d988fc5 vocab=66d708ab
-/
theorem solution
    {A B X : Scheme.{u}} (f : A ⟶ X) (g : B ⟶ X) [IsClosedImmersion f] [IsClosedImmersion g]
    [IsReduced A] [IsReduced B] (h : Set.range f.base = Set.range g.base) :
    ∃ e : A ≅ B, e.hom ≫ g = f := by

  haveI : Surjective (pullback.fst f g) := ⟨by
    rw [← Set.range_eq_univ, Scheme.Pullback.range_fst, ← h, Set.preimage_range]⟩
  haveI : Surjective (pullback.snd f g) := ⟨by
    rw [← Set.range_eq_univ, Scheme.Pullback.range_snd, h, Set.preimage_range]⟩
  haveI : IsIso (pullback.fst f g) := isIso_of_isClosedImmersion_of_surjective _
  haveI : IsIso (pullback.snd f g) := isIso_of_isClosedImmersion_of_surjective _
  refine ⟨(asIso (pullback.fst f g)).symm ≪≫ asIso (pullback.snd f g), ?_⟩
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_inv, asIso_hom, Category.assoc]
  rw [IsIso.inv_comp_eq, pullback.condition]
