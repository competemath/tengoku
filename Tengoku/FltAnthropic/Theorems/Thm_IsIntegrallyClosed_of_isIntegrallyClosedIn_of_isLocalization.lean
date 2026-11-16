import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_IsIntegrallyClosed_of_isIntegrallyClosedIn_of_isLocalization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IsIntegrallyClosed_of_isIntegrallyClosedIn_of_isLocalization.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/--
@isnad1 id=isintegr.1h3v.s7.14ecb2fddcac from=translated src=- shape=4bd727db vocab=8cb37b80
-/
theorem IsIntegrallyClosed.of_isIntegrallyClosedIn_of_isLocalization
    {C : Type*} [CommRing C] [IsDomain C] (M : Submonoid C) (hM : M ≤ nonZeroDivisors C)
    (L : Type*) [CommRing L] [IsDomain L] [Algebra C L] [IsLocalization M L]
    [IsIntegrallyClosedIn C L] [IsIntegrallyClosed L] : IsIntegrallyClosed C := by exact @_root_.P2MW.S_IsIntegrallyClosed_of_isIntegrallyClosedIn_of_isLocalization.solution C _ _ M hM L _ _ _ _ _ _
