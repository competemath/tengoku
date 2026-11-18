import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Matrix_exists_ne_zero_forall_mulVec_eq_zero_of_forall_map_mulVec_eq_zero

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Matrix_exists_ne_zero_forall_mulVec_eq_zero_of_forall_map_mulVec_eq_zero.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

/--
@isnad1 id=ex.2h6v.s8.25ab3cc5bc16 from=translated src=- shape=ca955834 vocab=29ec7782
-/
theorem Matrix.exists_ne_zero_forall_mulVec_eq_zero_of_forall_map_mulVec_eq_zero
    {k K : Type*} [Field k] [Field K] [Algebra k K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {J : Type*} (A : J → Matrix ι ι k) (v : ι → K) (hv : v ≠ 0)
    (hAv : ∀ j, ((A j).map (algebraMap k K)).mulVec v = 0) :
    ∃ w : ι → k, w ≠ 0 ∧ ∀ j, (A j).mulVec w = 0 := by exact @_root_.P2MW.S_Matrix_exists_ne_zero_forall_mulVec_eq_zero_of_forall_map_mulVec_eq_zero.solution k K _ _ _ ι _ _ J A v hv hAv
