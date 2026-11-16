import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_ModulesBaseChangeHom
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_of_isOpenImmersion

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_of_isOpenImmersion.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.isIso_baseChangeHom_of_isOpenImmersion
    {X T Y S : Scheme.{u}} {π : X ⟶ T} {j : S ⟶ T} [IsOpenImmersion j] {ρ : Y ⟶ S} {u : Y ⟶ X}
    (hu : IsPullback u ρ π j) (F : X.Modules) :
    IsIso (Scheme.Modules.baseChangeHom hu.w F) := by exact @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_of_isOpenImmersion.solution X T Y S π j _ ρ u hu F
