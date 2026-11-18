import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Ideal_height_eq_height_under_of_isIntegrallyClosed_of_isIntegral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Ideal_height_eq_height_under_of_isIntegrallyClosed_of_isIntegral.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

universe u
theorem Ideal.height_eq_height_under_of_isIntegrallyClosed_of_isIntegral
    (P B : Type u) [CommRing P] [IsDomain P] [IsNoetherianRing P] [IsIntegrallyClosed P]
    [CommRing B] [IsDomain B] [IsNoetherianRing B] [Algebra P B] [FaithfulSMul P B]
    [Algebra.IsIntegral P B] (q : Ideal B) [q.IsPrime] :
    q.height = (q.under P).height := by exact @_root_.P2MW.S_Ideal_height_eq_height_under_of_isIntegrallyClosed_of_isIntegral.solution P B _ _ _ _ _ _ _ _ _ _ q _
