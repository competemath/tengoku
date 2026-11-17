import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Matrix_isUnit_det_padicInt_of_norm_sub_one_lt_one

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Matrix_isUnit_det_padicInt_of_norm_sub_one_lt_one.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/--
@isnad1 id=isunit.1h3v.s7.ec5d4016d9a1 from=translated src=- shape=88e00d0f vocab=bcad3576
-/
theorem Matrix.isUnit_det_padicInt_of_norm_sub_one_lt_one
    (p : ℕ) [Fact p.Prime] (n : ℕ) (P : Matrix (Fin n) (Fin n) ℤ_[p])
    (h : ∀ i j, ‖P i j - (1 : Matrix (Fin n) (Fin n) ℤ_[p]) i j‖ < 1) :
    IsUnit P.det := by exact @_root_.P2MW.S_Matrix_isUnit_det_padicInt_of_norm_sub_one_lt_one.solution p _ n P h
