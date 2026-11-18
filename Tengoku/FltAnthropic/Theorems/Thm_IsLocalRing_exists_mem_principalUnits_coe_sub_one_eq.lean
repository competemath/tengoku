import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_LocalRing_PrincipalUnits
import Tengoku.FltAnthropic.P2M.Sol.S_IsLocalRing_exists_mem_principalUnits_coe_sub_one_eq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IsLocalRing_exists_mem_principalUnits_coe_sub_one_eq.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false
open IsLocalRing
/--
@isnad1 id=ex.2h3v.s8.46aff96aab49 from=translated src=- shape=256e8f01 vocab=9a537ab4
-/
theorem IsLocalRing.exists_mem_principalUnits_coe_sub_one_eq {R : Type*} [CommRing R] [IsLocalRing R]
    {k : ℕ} (hk : 1 ≤ k) {x : R} (hx : x ∈ maximalIdeal R ^ k) :
    ∃ u ∈ principalUnits R k, (u : R) - 1 = x := by exact @_root_.P2MW.S_IsLocalRing_exists_mem_principalUnits_coe_sub_one_eq.solution R _ _ k hk x hx
