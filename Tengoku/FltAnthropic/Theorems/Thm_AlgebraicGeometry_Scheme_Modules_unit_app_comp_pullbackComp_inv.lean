import Tengoku.Seed.AlgebraicGeometry.Modules.Sheaf
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_unit_app_comp_pullbackComp_inv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicGeometry_Scheme_Modules_unit_app_comp_pullbackComp_inv.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.unit_app_comp_pullbackComp_inv
    {X Y Z : Scheme.{u}} (g : Z ⟶ Y) (f : Y ⟶ X) (M : X.Modules) (U : X.Opens) :
    ((Scheme.Modules.pullbackPushforwardAdjunction (g ≫ f)).unit.app M).app U ≫
        ((Scheme.Modules.pullbackComp g f).inv.app M).app ((g ≫ f) ⁻¹ᵁ U) =
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U ≫
        ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
          ((Scheme.Modules.pullback f).obj M)).app (f ⁻¹ᵁ U) := by exact @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_unit_app_comp_pullbackComp_inv.solution X Y Z g f M U
