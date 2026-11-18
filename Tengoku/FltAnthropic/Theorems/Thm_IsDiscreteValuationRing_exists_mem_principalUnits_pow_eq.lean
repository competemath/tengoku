import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_LocalRing_PrincipalUnits
import Tengoku.FltAnthropic.P2M.Sol.S_IsDiscreteValuationRing_exists_mem_principalUnits_pow_eq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IsDiscreteValuationRing_exists_mem_principalUnits_pow_eq.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false
open IsLocalRing
/--
@isnad1 id=ex.4h5v.s8.324fd3d1abe3 from=translated src=- shape=be9e9333 vocab=c73c4dd6
-/
theorem IsDiscreteValuationRing.exists_mem_principalUnits_pow_eq {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    {n : ℕ} (hn : 0 < n) {e : ℕ} (hne : Ideal.span {(n : R)} = IsLocalRing.maximalIdeal R ^ e)
    {k : ℕ} (hk : e < k) {w : Rˣ} (hw : w ∈ principalUnits R (k + e)) :
    ∃ u ∈ principalUnits R k, u ^ n = w := by exact @_root_.P2MW.S_IsDiscreteValuationRing_exists_mem_principalUnits_pow_eq.solution R _ _ _ _ n hn e hne k hk w hw
