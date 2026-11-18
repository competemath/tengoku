import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Matrix_exists_det_eq_one_unipotent_forall_mul_mem_of_ne_bot_of_ne_top

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Matrix_exists_det_eq_one_unipotent_forall_mul_mem_of_ne_bot_of_ne_top.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

theorem Matrix.exists_det_eq_one_unipotent_forall_mul_mem_of_ne_bot_of_ne_top
    {F : Type*} [Field F] (I I' : Submodule (Matrix (Fin 2) (Fin 2) F) (Matrix (Fin 2) (Fin 2) F))
    (hI0 : I ≠ ⊥) (hI1 : I ≠ ⊤) (hI'0 : I' ≠ ⊥) (hI'1 : I' ≠ ⊤) :
    ∃ g : Matrix (Fin 2) (Fin 2) F, g.det = 1 ∧ (g - 1) * (g - 1) = 0 ∧ g ≠ 1 ∧ ∀ A ∈ I, A * g ∈ I' := by exact @_root_.P2MW.S_Matrix_exists_det_eq_one_unipotent_forall_mul_mem_of_ne_bot_of_ne_top.solution F _ I I' hI0 hI1 hI'0 hI'1
