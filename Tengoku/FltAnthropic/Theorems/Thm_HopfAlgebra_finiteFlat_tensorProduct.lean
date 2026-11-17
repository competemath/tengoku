import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_HopfAlgebra_finiteFlat_tensorProduct

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HopfAlgebra_finiteFlat_tensorProduct.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open scoped TensorProduct
/--
@isnad1 id=and.0h3v.s9.3cb0f4e200e2 from=translated src=- shape=347310d6 vocab=8b16279a
-/
theorem HopfAlgebra.finiteFlat_tensorProduct {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [HopfAlgebra R A] [HopfAlgebra R B]
    [Module.Finite R A] [Module.Flat R A] [Module.Finite R B] [Module.Flat R B] :
    Module.Finite R (A ⊗[R] B) ∧ Module.Flat R (A ⊗[R] B) := by exact @_root_.P2MW.S_HopfAlgebra_finiteFlat_tensorProduct.solution R A B _ _ _ _ _ _ _ _ _
