import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicGeometry_jacobsonSpace_of_locallyOfFiniteType

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicGeometry_jacobsonSpace_of_locallyOfFiniteType.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.jacobsonSpace_of_locallyOfFiniteType
    {k : Type u} [Field k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType t] :
    JacobsonSpace X := by exact @_root_.P2MW.S_AlgebraicGeometry_jacobsonSpace_of_locallyOfFiniteType.solution k _ X t _
