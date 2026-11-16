import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Algebra_Smooth_of_isIntegrallyClosed_of_krullDimLE_one_of_perfectField

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Algebra_Smooth_of_isIntegrallyClosed_of_krullDimLE_one_of_perfectField.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u v

theorem Algebra.Smooth.of_isIntegrallyClosed_of_krullDimLE_one_of_perfectField
    (k : Type u) [Field k] [PerfectField k] (B : Type v) [CommRing B] [IsDomain B] [Algebra k B]
    [Algebra.FiniteType k B] [IsIntegrallyClosed B] [Ring.KrullDimLE 1 B] :
    Algebra.Smooth k B := by exact @_root_.P2MW.S_Algebra_Smooth_of_isIntegrallyClosed_of_krullDimLE_one_of_perfectField.solution k _ _ B _ _ _ _ _ _
