import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_LocalRing_PrincipalUnits
import Tengoku.FltAnthropic.P2M.Sol.S_IsLocalRing_pow_mem_principalUnits

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IsLocalRing_pow_mem_principalUnits.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false
open IsLocalRing
/--
@isnad1 id=mem.3h5v.s8.c7df38cd6c1b from=translated src=- shape=7af7d334 vocab=d59ef843
-/
theorem IsLocalRing.pow_mem_principalUnits {R : Type*} [CommRing R] [IsLocalRing R]
    {p : ℕ} (hp : p.Prime) {e : ℕ} (hpe : (p : R) ∈ maximalIdeal R ^ e)
    {k : ℕ} {u : Rˣ} (hu : u ∈ principalUnits R k) :
    u ^ p ∈ principalUnits R (min (p * k) (k + e)) := by exact @_root_.P2MW.S_IsLocalRing_pow_mem_principalUnits.solution R _ _ p hp e hpe k u hu
