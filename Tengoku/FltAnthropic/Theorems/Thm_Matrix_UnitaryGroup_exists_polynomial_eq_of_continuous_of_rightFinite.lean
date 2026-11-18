import Tengoku.Seed.LinearAlgebra.UnitaryGroup
import Tengoku.Seed.Topology.Instances.Matrix
import Tengoku.Seed.Analysis.Complex.Basic
import Tengoku.FltAnthropic.P2M.Sol.S_Matrix_UnitaryGroup_exists_polynomial_eq_of_continuous_of_rightFinite

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Matrix_UnitaryGroup_exists_polynomial_eq_of_continuous_of_rightFinite.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

theorem Matrix.UnitaryGroup.exists_polynomial_eq_of_continuous_of_rightFinite
    (Φ : ↥(Matrix.unitaryGroup (Fin 2) ℂ) → ℂ) (hc : Continuous Φ)
    (hfin : ∃ s : Finset (↥(Matrix.unitaryGroup (Fin 2) ℂ) → ℂ),
      ∀ k : ↥(Matrix.unitaryGroup (Fin 2) ℂ),
        (fun x => Φ (x * k)) ∈ Submodule.span ℂ (s : Set (↥(Matrix.unitaryGroup (Fin 2) ℂ) → ℂ))) :
    ∃ F ∈ Submodule.span ℂ
        {F : Matrix (Fin 2) (Fin 2) ℂ → ℂ |
          ∃ l : List (Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] ℂ), F = fun m => (l.map (fun φ => φ m)).prod},
      ∀ k : ↥(Matrix.unitaryGroup (Fin 2) ℂ), Φ k = F (k : Matrix (Fin 2) (Fin 2) ℂ) := by exact @_root_.P2MW.S_Matrix_UnitaryGroup_exists_polynomial_eq_of_continuous_of_rightFinite.solution Φ hc hfin
