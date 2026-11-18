import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_IsDiscreteValuationRing_natCard_quotient_maximalIdeal_pow

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IsDiscreteValuationRing_natCard_quotient_maximalIdeal_pow.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false
/--
@isnad1 id=eq.0h2v.s6.bf6b80fcef01 from=translated src=- shape=5aa45293 vocab=c7142b22
-/
theorem IsDiscreteValuationRing.natCard_quotient_maximalIdeal_pow {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (n : ℕ) :
    Nat.card (R ⧸ IsLocalRing.maximalIdeal R ^ n) = Nat.card (IsLocalRing.ResidueField R) ^ n := by exact @_root_.P2MW.S_IsDiscreteValuationRing_natCard_quotient_maximalIdeal_pow.solution R _ _ _ n
