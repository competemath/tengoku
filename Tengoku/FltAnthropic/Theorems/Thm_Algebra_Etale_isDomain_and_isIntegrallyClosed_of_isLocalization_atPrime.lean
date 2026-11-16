import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Algebra_Etale_isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Algebra_Etale_isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

universe u

theorem Algebra.Etale.isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime
    (P : Type u) [CommRing P] [IsDomain P] [IsIntegrallyClosed P]
    (A : Type u) [CommRing A] [Algebra P A] [Algebra.Etale P A]
    (q : Ideal A) [q.IsPrime] (A_q : Type u) [CommRing A_q] [Algebra A A_q] [IsLocalization.AtPrime A_q q] :
    IsDomain A_q ∧ IsIntegrallyClosed A_q := by exact @_root_.P2MW.S_Algebra_Etale_isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime.solution P _ _ _ A _ _ _ q _ A_q _ _ _
