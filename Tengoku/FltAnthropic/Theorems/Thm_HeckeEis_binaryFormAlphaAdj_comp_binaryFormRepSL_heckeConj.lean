import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_Gamma0HeckeOperatorHom
import Tengoku.FltAnthropic.Definitions.Def_HeckeEis_BinaryFormRep
import Tengoku.FltAnthropic.P2M.Sol.S_HeckeEis_binaryFormAlphaAdj_comp_binaryFormRepSL_heckeConj

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HeckeEis_binaryFormAlphaAdj_comp_binaryFormRepSL_heckeConj.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped MatrixGroups

/--
@isnad1 id=eq.0h5v.s15.83f6fc61f043 from=translated src=- shape=1bcf6acd vocab=2dc4d323
-/
theorem HeckeEis.binaryFormAlphaAdj_comp_binaryFormRepSL_heckeConj (K : Type*) [CommRing K] (n N ℓ : ℕ) [NeZero ℓ]
    (u : ↥(HeckeEis.heckeUpper N ℓ)) :
    HeckeEis.binaryFormAlphaAdj K n ℓ ∘ₗ ((HeckeEis.binaryFormRepSL K n).comp (CongruenceSubgroup.Gamma0 N).subtype) (HeckeEis.heckeConj N ℓ u)
      = ((HeckeEis.binaryFormRepSL K n).comp (CongruenceSubgroup.Gamma0 N).subtype) (u : CongruenceSubgroup.Gamma0 N)
          ∘ₗ HeckeEis.binaryFormAlphaAdj K n ℓ := by exact @_root_.P2MW.S_HeckeEis_binaryFormAlphaAdj_comp_binaryFormRepSL_heckeConj.solution K _ n N ℓ _ u
