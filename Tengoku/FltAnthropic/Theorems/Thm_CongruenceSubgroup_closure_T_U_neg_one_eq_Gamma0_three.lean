import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_CongruenceSubgroup_closure_T_U_neg_one_eq_Gamma0_three

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_CongruenceSubgroup_closure_T_U_neg_one_eq_Gamma0_three.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open scoped MatrixGroups in

/--
@isnad1 id=eq.1h1v.s9.56f1f6ec2051 from=translated src=- shape=52bc809b vocab=d2a43df6
-/
theorem CongruenceSubgroup.closure_T_U_neg_one_eq_Gamma0_three (U : SL(2, ℤ))
    (hU : (U : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; -3, 1]) :
    Subgroup.closure ({ModularGroup.T, U, -1} : Set SL(2, ℤ)) = CongruenceSubgroup.Gamma0 3 := by exact @_root_.P2MW.S_CongruenceSubgroup_closure_T_U_neg_one_eq_Gamma0_three.solution U hU
