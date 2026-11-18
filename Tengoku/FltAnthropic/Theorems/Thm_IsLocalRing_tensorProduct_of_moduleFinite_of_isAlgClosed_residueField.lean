import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_IsLocalRing_tensorProduct_of_moduleFinite_of_isAlgClosed_residueField

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IsLocalRing_tensorProduct_of_moduleFinite_of_isAlgClosed_residueField.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped TensorProduct

universe u

/--
@isnad1 id=islocalr.0h3v.s7.30897b72eb4f from=translated src=- shape=054c1ea0 vocab=cf9137b0
-/
theorem IsLocalRing.tensorProduct_of_moduleFinite_of_isAlgClosed_residueField
    (R : Type u) [CommRing R] [IsLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)]
    (A : Type u) [CommRing A] [Algebra R A] [Module.Finite R A] [IsLocalRing A]
    (B : Type u) [CommRing B] [Algebra R B] [Module.Finite R B] [IsLocalRing B] :
    IsLocalRing (A ⊗[R] B) := by exact @_root_.P2MW.S_IsLocalRing_tensorProduct_of_moduleFinite_of_isAlgClosed_residueField.solution R _ _ _ A _ _ _ _ B _ _ _ _
