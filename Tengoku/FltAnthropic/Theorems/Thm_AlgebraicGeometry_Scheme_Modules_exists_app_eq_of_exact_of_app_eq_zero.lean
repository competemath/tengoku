import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_app_eq_of_exact_of_app_eq_zero

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_app_eq_of_exact_of_app_eq_zero.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

/--
@isnad1 id=ex.2h4v.s12.f60eff1020e2 from=translated src=- shape=525834a1 vocab=70d657c4
-/
theorem AlgebraicGeometry.Scheme.Modules.exists_app_eq_of_exact_of_app_eq_zero
    {X : Scheme.{u}} (S : ShortComplex X.Modules) (hS : S.Exact) [Mono S.f]
    (U : X.Opens) (m : Γ(S.X₂, U)) (hm : S.g.app U m = 0) :
    ∃ e : Γ(S.X₁, U), S.f.app U e = m := by exact @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_app_eq_of_exact_of_app_eq_zero.solution X S hS _ U m hm
