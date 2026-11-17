import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicGeometry_IsClosedImmersion_exists_ideal_fg_forall_exists_comp_eq_specMap_iff_map_eq_bot

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicGeometry_IsClosedImmersion_exists_ideal_fg_forall_exists_comp_eq_specMap_iff_map_eq_bot.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

/--
@isnad1 id=ex.0h3v.s7.95b771104baa from=translated src=- shape=c215cbd6 vocab=5909f8f5
-/
theorem AlgebraicGeometry.IsClosedImmersion.exists_ideal_fg_forall_exists_comp_eq_specMap_iff_map_eq_bot
    {S : Type u} [CommRing S] {Z : Scheme.{u}} (ι : Z ⟶ Spec (CommRingCat.of S))
    [IsClosedImmersion ι] [LocallyOfFinitePresentation ι] :
    ∃ J : Ideal S, J.FG ∧ ∀ (R : Type u) [CommRing R] (φ : S →+* R),
      (∃ y : Spec (CommRingCat.of R) ⟶ Z, y ≫ ι = Spec.map (CommRingCat.ofHom φ)) ↔ J.map φ = ⊥ := by exact @_root_.P2MW.S_AlgebraicGeometry_IsClosedImmersion_exists_ideal_fg_forall_exists_comp_eq_specMap_iff_map_eq_bot.solution S _ Z ι _ _
