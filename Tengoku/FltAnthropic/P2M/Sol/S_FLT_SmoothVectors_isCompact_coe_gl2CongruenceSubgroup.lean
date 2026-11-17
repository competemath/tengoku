import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_RepTheory_GL2CongruenceSubgroup
import Tengoku.FltAnthropic.Definitions.Def_LocalLanglands_LocalHeckeInstance
import Tengoku.FltAnthropic.Definitions.Def_LocalLanglands_IntegralSubgroupCompact
import Tengoku.FltAnthropic.Theorems.Thm_FLT_SmoothVectors_gl2CongruenceSubgroup_le_integralSubgroup

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_FLT_SmoothVectors_isCompact_coe_gl2CongruenceSubgroup.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_FLT_SmoothVectors_isCompact_coe_gl2CongruenceSubgroup

open FLT.SmoothVectors

theorem solution (p : ℕ) [Fact p.Prime] (n : ℕ) :
    IsCompact ((gl2CongruenceSubgroup p n : Subgroup (GL (Fin 2) ℚ_[p])) :
      Set (GL (Fin 2) ℚ_[p])) := by
  refine IsCompact.of_isClosed_subset
    (FLT.SpectralSide.isCompact_coe_integralSubgroup ℤ_[p] ℚ_[p] continuous_subtype_val)
    (Subgroup.isClosed_of_isOpen _ (isOpen_coe_gl2CongruenceSubgroup p n)) ?_
  exact fun g hg => gl2CongruenceSubgroup_le_integralSubgroup p n hg
