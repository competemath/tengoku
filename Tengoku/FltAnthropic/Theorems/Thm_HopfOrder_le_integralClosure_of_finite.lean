import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_HopfOrder_le_integralClosure_of_finite

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HopfOrder_le_integralClosure_of_finite.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

universe u w
/--
@isnad1 id=le.0h3v.s7.ce3701b654d5 from=translated src=- shape=cdc3b500 vocab=ba532c6e
-/
theorem HopfOrder.le_integralClosure_of_finite
    {R : Type u} [CommRing R] {A : Type w} [CommRing A] [Algebra R A]
    (S : Subalgebra R A) [Module.Finite R S] : S ≤ integralClosure R A := by exact @_root_.P2MW.S_HopfOrder_le_integralClosure_of_finite.solution R _ A _ _ S _
