import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_IsAlgebraic_mem_range_algebraMap_rat_of_isDomain_tensorProduct_of_isAlgClosed

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IsAlgebraic_mem_range_algebraMap_rat_of_isDomain_tensorProduct_of_isAlgClosed.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem IsAlgebraic.mem_range_algebraMap_rat_of_isDomain_tensorProduct_of_isAlgClosed
    (K : Type) [Field K] [CharZero K]
    (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (h : IsDomain (K ⊗[ℚ] C))
    (x : K) (hx : IsAlgebraic ℚ x) :
    x ∈ Set.range (algebraMap ℚ K) := by exact @_root_.P2MW.S_IsAlgebraic_mem_range_algebraMap_rat_of_isDomain_tensorProduct_of_isAlgClosed.solution K _ _ C _ _ _ h x hx
