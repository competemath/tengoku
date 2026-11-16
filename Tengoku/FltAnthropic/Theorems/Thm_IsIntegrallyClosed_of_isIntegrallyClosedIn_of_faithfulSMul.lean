import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_IsIntegrallyClosed_of_isIntegrallyClosedIn_of_faithfulSMul

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IsIntegrallyClosed_of_isIntegrallyClosedIn_of_faithfulSMul.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/--
@isnad1 id=isintegr.0h2v.s5.e05adb1c0b10 from=translated src=- shape=ef068099 vocab=4dbce9f8
-/
theorem IsIntegrallyClosed.of_isIntegrallyClosedIn_of_faithfulSMul
    (A F : Type*) [CommRing A] [IsDomain A] [Field F] [Algebra A F] [FaithfulSMul A F]
    [IsIntegrallyClosedIn A F] : IsIntegrallyClosed A := by exact @_root_.P2MW.S_IsIntegrallyClosed_of_isIntegrallyClosedIn_of_faithfulSMul.solution A F _ _ _ _ _ _
