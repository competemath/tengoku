import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_LocalRing_PrincipalUnits
import Tengoku.FltAnthropic.P2M.Sol.S_IsDiscreteValuationRing_relIndex_principalUnits_add

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IsDiscreteValuationRing_relIndex_principalUnits_add.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false
open IsLocalRing
theorem IsDiscreteValuationRing.relIndex_principalUnits_add {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    (principalUnits R (k + n)).relIndex (principalUnits R k) = Nat.card (IsLocalRing.ResidueField R) ^ n := by exact @_root_.P2MW.S_IsDiscreteValuationRing_relIndex_principalUnits_add.solution R _ _ _ k hk n
