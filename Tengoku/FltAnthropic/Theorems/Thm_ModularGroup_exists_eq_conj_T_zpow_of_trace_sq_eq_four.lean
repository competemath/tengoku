import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_ModularGroup_exists_eq_conj_T_zpow_of_trace_sq_eq_four

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ModularGroup_exists_eq_conj_T_zpow_of_trace_sq_eq_four.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularGroup.exists_eq_conj_T_zpow_of_trace_sq_eq_four (γ : SL(2, ℤ))
    (hγ : ((γ : Matrix (Fin 2) (Fin 2) ℤ).trace) ^ 2 = 4) :
    ∃ (ε δ : SL(2, ℤ)) (h : ℤ), (ε = 1 ∨ ε = -1) ∧ γ = ε * (δ * ModularGroup.T ^ h * δ⁻¹) := by exact @_root_.P2MW.S_ModularGroup_exists_eq_conj_T_zpow_of_trace_sq_eq_four.solution γ hγ
