import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HeckeEis_BinaryFormRep
import Tengoku.FltAnthropic.P2M.Sol.S_HeckeEis_binaryFormRepSL_neg_one_apply

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HeckeEis_binaryFormRepSL_neg_one_apply.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped MatrixGroups

/--
@isnad1 id=eq.0h3v.s12.ec0c156f4bd9 from=translated src=- shape=e57903e6 vocab=db68f359
-/
theorem HeckeEis.binaryFormRepSL_neg_one_apply (K : Type*) [CommRing K] (n : ℕ) (P : ↥(HeckeEis.BinaryForm K n)) :
    HeckeEis.binaryFormRepSL K n (-1) P = ((-1 : K) ^ n) • P := by exact @_root_.P2MW.S_HeckeEis_binaryFormRepSL_neg_one_apply.solution K _ n P
