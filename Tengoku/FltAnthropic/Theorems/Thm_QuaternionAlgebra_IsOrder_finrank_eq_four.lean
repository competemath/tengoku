import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_QuaternionAlgebra_Order
import Tengoku.FltAnthropic.P2M.Sol.S_QuaternionAlgebra_IsOrder_finrank_eq_four

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_QuaternionAlgebra_IsOrder_finrank_eq_four.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open scoped Quaternion

/--
@isnad1 id=eq.1h3v.s9.3da52c4c1d94 from=translated src=- shape=db225be1 vocab=2b5516fe
-/
theorem QuaternionAlgebra.IsOrder.finrank_eq_four {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    (hΛ : QuaternionAlgebra.IsOrder Λ) : Module.finrank ℤ Λ = 4 := by exact @_root_.P2MW.S_QuaternionAlgebra_IsOrder_finrank_eq_four.solution a b Λ hΛ
