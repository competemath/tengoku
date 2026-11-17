import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_ComplexIwasawa
import Tengoku.Seed.Analysis.Calculus.ContDiff.Defs
import Tengoku.Seed.Analysis.Complex.Basic
import Tengoku.Seed.LinearAlgebra.Matrix.Determinant.Basic
import Tengoku.Seed.Topology.Instances.Matrix
import Tengoku.FltAnthropic.P2M.Sol.S_AutomorphicForm_ComplexIwasawa_exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AutomorphicForm_ComplexIwasawa_exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped ContDiff

/--
@isnad1 id=ex.2h2v.s8.c1406a222f70 from=translated src=- shape=cc625ebe vocab=9a9104c7
-/
theorem AutomorphicForm.ComplexIwasawa.exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact
    (𝒢 : Set (Matrix (Fin 2) (Fin 2) ℂ)) (h𝒢 : IsCompact 𝒢) (hdet : ∀ g ∈ 𝒢, g.det ≠ 0) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ g ∈ 𝒢, ∀ (i j : Fin 2) (z : ℂ),
      ‖iteratedFDeriv ℝ n (fun w => kC g w i j) z‖ ≤ C := by exact @_root_.P2MW.S_AutomorphicForm_ComplexIwasawa_exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact.solution 𝒢 h𝒢 hdet n
