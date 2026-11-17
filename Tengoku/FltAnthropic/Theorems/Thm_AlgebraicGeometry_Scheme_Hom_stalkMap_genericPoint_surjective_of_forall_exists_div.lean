import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_stalkMap_genericPoint_surjective_of_forall_exists_div

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicGeometry_Scheme_Hom_stalkMap_genericPoint_surjective_of_forall_exists_div.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

/--
@isnad1 id=surjecti.2h4v.s13.fabf15519ab4 from=translated src=- shape=0635a3a2 vocab=40fd76cc
-/
theorem AlgebraicGeometry.Scheme.Hom.stalkMap_genericPoint_surjective_of_forall_exists_div
    {Y Z : Scheme.{u}} [IsIntegral Y] (f : Y ⟶ Z) (V : Z.Opens) (hV : f (genericPoint Y) ∈ V)
    (hgen : ∀ x : Y.functionField, ∃ a b : Γ(Z, V),
      Y.presheaf.germ (f ⁻¹ᵁ V) (genericPoint Y) hV (f.app V b) ≠ 0 ∧
        x * Y.presheaf.germ (f ⁻¹ᵁ V) (genericPoint Y) hV (f.app V b) =
          Y.presheaf.germ (f ⁻¹ᵁ V) (genericPoint Y) hV (f.app V a)) :
    Function.Surjective (f.stalkMap (genericPoint Y)) := by exact @_root_.P2MW.S_AlgebraicGeometry_Scheme_Hom_stalkMap_genericPoint_surjective_of_forall_exists_div.solution Y Z _ f V hV hgen
