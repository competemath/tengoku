import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_RepTheory_GL2CongruenceSubgroup
import Tengoku.FltAnthropic.Definitions.Def_LocalLanglands_LocalHeckeInstance
import Tengoku.FltAnthropic.Definitions.Def_LocalLanglands_IntegralSubgroupOpen
import Tengoku.FltAnthropic.Theorems.Thm_FLT_SmoothVectors_gl2CongruenceSubgroup_zero_eq_integralSubgroup

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_FLT_SmoothVectors_gl2CongruenceSubgroup_le_integralSubgroup.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_FLT_SmoothVectors_gl2CongruenceSubgroup_le_integralSubgroup

open FLT.SmoothVectors

/--
@isnad1 id=le.0h2v.s8.7f8f0e22dc61 from=translated src=- shape=1c6df9fe vocab=317a30b3
-/
theorem solution (p : ℕ) [Fact p.Prime] (n : ℕ) :
    gl2CongruenceSubgroup p n ≤ LocalGL2.integralSubgroup ℤ_[p] ℚ_[p] := by
  rw [← gl2CongruenceSubgroup_zero_eq_integralSubgroup p]
  exact gl2CongruenceSubgroup_antitone p (Nat.zero_le n)
