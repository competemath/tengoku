import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Algebra_TensorProduct_isField_of_isSeparable_of_forall_isAlgebraic_mem_range

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Algebra_TensorProduct_isField_of_isSeparable_of_forall_isAlgebraic_mem_range.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped TensorProduct

/--
@isnad1 id=isfield.1h3v.s7.18b132b2d8db from=translated src=- shape=d597839f vocab=278b10fc
-/
theorem Algebra.TensorProduct.isField_of_isSeparable_of_forall_isAlgebraic_mem_range
    (k F K : Type*) [Field k] [Field F] [Field K] [Algebra k F] [Algebra k K]
    [Algebra.IsSeparable k K]
    (hconst : ∀ y : F, IsAlgebraic k y → y ∈ (algebraMap k F).range) :
    IsField (F ⊗[k] K) := by exact @_root_.P2MW.S_Algebra_TensorProduct_isField_of_isSeparable_of_forall_isAlgebraic_mem_range.solution k F K _ _ _ _ _ _ hconst
