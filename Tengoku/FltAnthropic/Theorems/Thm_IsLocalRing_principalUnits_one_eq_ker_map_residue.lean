import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_LocalRing_PrincipalUnits
import Tengoku.FltAnthropic.P2M.Sol.S_IsLocalRing_principalUnits_one_eq_ker_map_residue

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IsLocalRing_principalUnits_one_eq_ker_map_residue.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false
open IsLocalRing
/--
@isnad1 id=eq.0h1v.s8.577812e2042e from=translated src=- shape=4e51f56e vocab=ef9416dd
-/
theorem IsLocalRing.principalUnits_one_eq_ker_map_residue {R : Type*} [CommRing R] [IsLocalRing R] :
    principalUnits R 1 = (Units.map (residue R : R →* ResidueField R)).ker := by exact @_root_.P2MW.S_IsLocalRing_principalUnits_one_eq_ker_map_residue.solution R _ _
