import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_HopfAlgebra_map_antipode_comul_of_isCocomm

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HopfAlgebra_map_antipode_comul_of_isCocomm.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open scoped TensorProduct in
theorem HopfAlgebra.map_antipode_comul_of_isCocomm {R : Type*} [CommSemiring R]
    {A : Type*} [Semiring A] [HopfAlgebra R A] (hcocomm : Coalgebra.IsCocomm R A) (a : A) :
    TensorProduct.map (HopfAlgebra.antipode R) (HopfAlgebra.antipode R) (Coalgebra.comul a)
      = Coalgebra.comul (HopfAlgebra.antipode R a) := by exact @_root_.P2MW.S_HopfAlgebra_map_antipode_comul_of_isCocomm.solution R _ A _ _ hcocomm a
