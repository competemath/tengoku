import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_le

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_le.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.SmoothOfRelativeDimension.topologicalKrullDim_le
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) (n : ℕ)
    [SmoothOfRelativeDimension n f] :
    topologicalKrullDim X ≤ n := by exact @_root_.P2MW.S_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_le.solution K _ X f n _
