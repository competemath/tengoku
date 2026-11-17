import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Matrix_exists_rat_mul_eq_map_padicInt_of_isUnit_det

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Matrix_exists_rat_mul_eq_map_padicInt_of_isUnit_det.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/--
@isnad1 id=ex.1h3v.s8.5f451fbcf5d5 from=translated src=- shape=744e20e1 vocab=d15f5876
-/
theorem Matrix.exists_rat_mul_eq_map_padicInt_of_isUnit_det
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℚ_[p]) (hM : IsUnit M.det) :
    ∃ (Q : Matrix (Fin n) (Fin n) ℚ) (P : Matrix (Fin n) (Fin n) ℤ_[p]),
      IsUnit Q.det ∧ IsUnit P.det ∧
      M * Q.map (algebraMap ℚ ℚ_[p]) = P.map (algebraMap ℤ_[p] ℚ_[p]) := by exact @_root_.P2MW.S_Matrix_exists_rat_mul_eq_map_padicInt_of_isUnit_det.solution p _ n M hM
