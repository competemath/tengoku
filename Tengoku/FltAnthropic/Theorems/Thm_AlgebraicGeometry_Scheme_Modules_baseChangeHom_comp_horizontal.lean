import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_ModulesBaseChangeHom
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_baseChangeHom_comp_horizontal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicGeometry_Scheme_Modules_baseChangeHom_comp_horizontal.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.baseChangeHom_comp_horizontal
    {X T X' T' X'' T'' : Scheme.{u}} {π : X ⟶ T} {ψ : T' ⟶ T} {π' : X' ⟶ T'} {g' : X' ⟶ X}
    {ψ' : T'' ⟶ T'} {π'' : X'' ⟶ T''} {g'' : X'' ⟶ X'}
    (h₁ : g' ≫ π = π' ≫ ψ) (h₂ : g'' ≫ π' = π'' ≫ ψ') (h₁₂ : (g'' ≫ g') ≫ π = π'' ≫ (ψ' ≫ ψ))
    (F : X.Modules) :
    Scheme.Modules.baseChangeHom h₁₂ F =
      (Scheme.Modules.pullbackComp ψ' ψ).inv.app ((Scheme.Modules.pushforward π).obj F) ≫
        (Scheme.Modules.pullback ψ').map (Scheme.Modules.baseChangeHom h₁ F) ≫
          Scheme.Modules.baseChangeHom h₂ ((Scheme.Modules.pullback g').obj F) ≫
            (Scheme.Modules.pushforward π'').map ((Scheme.Modules.pullbackComp g'' g').hom.app F) := by exact @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_baseChangeHom_comp_horizontal.solution X T X' T' X'' T'' π ψ π' g' ψ' π'' g'' h₁ h₂ h₁₂ F
