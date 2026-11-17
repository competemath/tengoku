import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_map_germ_ker_ideal_eq_ker_stalkMap

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicGeometry_Scheme_Hom_map_germ_ker_ideal_eq_ker_stalkMap.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

theorem AlgebraicGeometry.Scheme.Hom.map_germ_ker_ideal_eq_ker_stalkMap {X Y : Scheme.{u}} (σ : Y ⟶ X) [IsClosedImmersion σ]
    (y : Y) (U : X.affineOpens) (hx : σ.base y ∈ (U : X.Opens)) :
    Ideal.map (X.presheaf.germ (U : X.Opens) (σ.base y) hx).hom (σ.ker.ideal U) = RingHom.ker (σ.stalkMap y).hom := by exact @_root_.P2MW.S_AlgebraicGeometry_Scheme_Hom_map_germ_ker_ideal_eq_ker_stalkMap.solution X Y σ _ y U hx
