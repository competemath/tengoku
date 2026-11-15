import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_CategoryTheory_IsPullback_fst_pullbackMap_of_comp_eq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_finrank_pullbackMap_of_comp_eq.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_finrank_pullbackMap_of_comp_eq

set_option autoImplicit false

universe v w u

open CategoryTheory CategoryTheory.Limits

theorem solution {X X' S T : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S) (t : T ⟶ S) (π : X' ⟶ X) (hπ : π ≫ f = f')
    [AlgebraicGeometry.Flat π] [AlgebraicGeometry.IsFinite π] (y : ↑(pullback f t)) :
    (pullback.map f' t f t π (𝟙 T) (𝟙 S) (by rw [Category.comp_id, hπ])
        (by rw [Category.comp_id, Category.id_comp])).finrank y =
      π.finrank (pullback.fst f t y) :=
  AlgebraicGeometry.Scheme.Hom.finrank_of_isPullback _ _ _ _
    (CategoryTheory.IsPullback.fst_pullbackMap_of_comp_eq f f' t π hπ) y
