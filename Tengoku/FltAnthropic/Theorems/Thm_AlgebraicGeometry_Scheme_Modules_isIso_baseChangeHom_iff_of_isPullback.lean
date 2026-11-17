import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_ModulesBaseChangeHom
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_iff_of_isPullback

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_iff_of_isPullback.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/--
@isnad1 id=iff.2h12v.s7.3f9e6806bf98 from=translated src=- shape=46ad6603 vocab=78f1eb4f
-/
theorem AlgebraicGeometry.Scheme.Modules.isIso_baseChangeHom_iff_of_isPullback
    {X T T' X₁ X₂ : Scheme.{u}} {π : X ⟶ T} {ψ : T' ⟶ T}
    {π₁ : X₁ ⟶ T'} {g₁ : X₁ ⟶ X} {π₂ : X₂ ⟶ T'} {g₂ : X₂ ⟶ X}
    (h₁ : IsPullback g₁ π₁ π ψ) (h₂ : IsPullback g₂ π₂ π ψ) (F : X.Modules) :
    IsIso (Scheme.Modules.baseChangeHom h₁.w F) ↔ IsIso (Scheme.Modules.baseChangeHom h₂.w F) := by exact @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_iff_of_isPullback.solution X T T' X₁ X₂ π ψ π₁ g₁ π₂ g₂ h₁ h₂ F
