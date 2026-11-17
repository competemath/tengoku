import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicGeometry_isReduced_of_mem_nonZeroDivisors_of_isReduced_basicOpen

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicGeometry_isReduced_of_mem_nonZeroDivisors_of_isReduced_basicOpen.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite

/--
@isnad1 id=isreduce.1h2v.s12.12a28aa74dd1 from=translated src=- shape=23272e67 vocab=dc44d87d
-/
theorem AlgebraicGeometry.isReduced_of_mem_nonZeroDivisors_of_isReduced_basicOpen
    {Y : Scheme} (p : Γ(Y, ⊤))
    (hreg : ∀ U : Y.Opens, IsAffineOpen U → Y.presheaf.map (homOfLE le_top).op p ∈ nonZeroDivisors Γ(Y, U))
    [IsReduced (Y.basicOpen p : Scheme)] : IsReduced Y := by exact @_root_.P2MW.S_AlgebraicGeometry_isReduced_of_mem_nonZeroDivisors_of_isReduced_basicOpen.solution Y p hreg _
