import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HeckeEis_BinaryFormRep
import Tengoku.FltAnthropic.P2M.Sol.S_HeckeEis_mem_range_binaryFormRepSL_T_zpow_sub_one_of_prime_smul_mem

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HeckeEis_mem_range_binaryFormRepSL_T_zpow_sub_one_of_prime_smul_mem.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped MatrixGroups

/--
@isnad1 id=mem.4h4v.s14.ba6af366356f from=translated src=- shape=0ee54e53 vocab=21800f9f
-/
theorem HeckeEis.mem_range_binaryFormRepSL_T_zpow_sub_one_of_prime_smul_mem (n : ℕ) {p : ℕ} (hp : p.Prime) (hn : n < p)
    {h : ℤ} (hph : ¬ (p : ℤ) ∣ h) (v : ↥(HeckeEis.BinaryForm ℤ n))
    (hv : (p : ℤ) • v ∈ LinearMap.range (HeckeEis.binaryFormRepSL ℤ n (ModularGroup.T ^ h) - 1)) :
    v ∈ LinearMap.range (HeckeEis.binaryFormRepSL ℤ n (ModularGroup.T ^ h) - 1) := by exact @_root_.P2MW.S_HeckeEis_mem_range_binaryFormRepSL_T_zpow_sub_one_of_prime_smul_mem.solution n p hp hn h hph v hv
