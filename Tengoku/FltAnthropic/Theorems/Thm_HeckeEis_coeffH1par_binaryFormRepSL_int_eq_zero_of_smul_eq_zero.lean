import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HeckeEis_BinaryFormRep
import Tengoku.FltAnthropic.Definitions.Def_Gamma0CoeffCohomology
import Tengoku.FltAnthropic.P2M.Sol.S_HeckeEis_coeffH1par_binaryFormRepSL_int_eq_zero_of_smul_eq_zero

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HeckeEis_coeffH1par_binaryFormRepSL_int_eq_zero_of_smul_eq_zero.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped MatrixGroups

/--
@isnad1 id=eq.2h4v.s16.9bb79db49015 from=translated src=- shape=46ecc8c9 vocab=fdaf032e
-/
theorem HeckeEis.coeffH1par_binaryFormRepSL_int_eq_zero_of_smul_eq_zero (n N : ℕ) [NeZero N] (m : ℤ) (hm : m ≠ 0)
    (x : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℤ n).comp (CongruenceSubgroup.Gamma0 N).subtype))
    (hx : m • x = 0) : x = 0 := by exact @_root_.P2MW.S_HeckeEis_coeffH1par_binaryFormRepSL_int_eq_zero_of_smul_eq_zero.solution n N _ m hm x hx
