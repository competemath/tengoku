import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_IsGaloisGroup_isIntegrallyClosed_of_isIntegrallyClosed

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IsGaloisGroup_isIntegrallyClosed_of_isIntegrallyClosed.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

/--
@isnad1 id=isintegr.0h3v.s6.5a4735b1b35f from=translated src=- shape=a377edc3 vocab=b3070424
-/
theorem IsGaloisGroup.isIntegrallyClosed_of_isIntegrallyClosed
    (G : Type*) [Group G] {A B : Type*} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Algebra A B] [FaithfulSMul A B] [MulSemiringAction G B] [IsGaloisGroup G A B]
    [IsIntegrallyClosed B] : IsIntegrallyClosed A := by exact @_root_.P2MW.S_IsGaloisGroup_isIntegrallyClosed_of_isIntegrallyClosed.solution G _ A B _ _ _ _ _ _ _ _ _
