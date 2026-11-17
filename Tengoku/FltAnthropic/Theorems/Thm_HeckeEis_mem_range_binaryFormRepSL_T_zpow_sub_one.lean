import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HeckeEis_BinaryFormRep
import Tengoku.FltAnthropic.P2M.Sol.S_HeckeEis_mem_range_binaryFormRepSL_T_zpow_sub_one

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HeckeEis_mem_range_binaryFormRepSL_T_zpow_sub_one.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.mem_range_binaryFormRepSL_T_zpow_sub_one {K : Type*} [Field K] [CharZero K] (n : ℕ) {h : ℤ}
    (hh : h ≠ 0) (P : ↥(HeckeEis.BinaryForm K n))
    (hP : MvPolynomial.coeff (Finsupp.single 1 n) (P : MvPolynomial (Fin 2) K) = 0) :
    P ∈ LinearMap.range (HeckeEis.binaryFormRepSL K n (ModularGroup.T ^ h) - 1) := by exact @_root_.P2MW.S_HeckeEis_mem_range_binaryFormRepSL_T_zpow_sub_one.solution K _ _ n h hh P hP
