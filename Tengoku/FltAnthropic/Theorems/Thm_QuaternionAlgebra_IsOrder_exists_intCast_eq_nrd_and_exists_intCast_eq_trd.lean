import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_QuaternionAlgebra_Order
import Tengoku.FltAnthropic.Definitions.Def_QuaternionAlgebra_ReducedNorm
import Tengoku.FltAnthropic.P2M.Sol.S_QuaternionAlgebra_IsOrder_exists_intCast_eq_nrd_and_exists_intCast_eq_trd

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_QuaternionAlgebra_IsOrder_exists_intCast_eq_nrd_and_exists_intCast_eq_trd.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped Quaternion

theorem QuaternionAlgebra.IsOrder.exists_intCast_eq_nrd_and_exists_intCast_eq_trd
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    {x : ℍ[ℚ, a, b]} (hx : x ∈ Λ) :
    (∃ n : ℤ, (n : ℚ) = QuaternionAlgebra.nrd x) ∧ ∃ t : ℤ, (t : ℚ) = QuaternionAlgebra.trd x := by exact @_root_.P2MW.S_QuaternionAlgebra_IsOrder_exists_intCast_eq_nrd_and_exists_intCast_eq_trd.solution a b Λ hΛ x hx
