import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_LocalRing_PrincipalUnits
import Tengoku.FltAnthropic.P2M.Sol.S_IsLocalRing_index_principalUnits_one

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IsLocalRing_index_principalUnits_one.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false
open IsLocalRing
/--
@isnad1 id=eq.0h1v.s6.06836955d354 from=translated src=- shape=2c3438e0 vocab=dc784e61
-/
theorem IsLocalRing.index_principalUnits_one {R : Type*} [CommRing R] [IsLocalRing R] :
    (principalUnits R 1).index = Nat.card (ResidueField R)ˣ := by exact @_root_.P2MW.S_IsLocalRing_index_principalUnits_one.solution R _ _
