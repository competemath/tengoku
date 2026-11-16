import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicGeometry_IsAffineOpen_range_algebraMap_functionField_eq_iInf

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicGeometry_IsAffineOpen_range_algebraMap_functionField_eq_iInf.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.IsAffineOpen.range_algebraMap_functionField_eq_iInf
    {X : Scheme.{u}} [IsIntegral X] {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U] :
    (algebraMap Γ(X, U) X.functionField).range =
      ⨅ (x : X) (_ : x ∈ U), (algebraMap (X.presheaf.stalk x) X.functionField).range := by exact @_root_.P2MW.S_AlgebraicGeometry_IsAffineOpen_range_algebraMap_functionField_eq_iInf.solution X _ U hU _
