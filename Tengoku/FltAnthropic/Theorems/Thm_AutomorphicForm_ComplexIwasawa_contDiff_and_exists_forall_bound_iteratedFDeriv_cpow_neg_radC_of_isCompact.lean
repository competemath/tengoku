import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_ComplexIwasawa
import Tengoku.Seed.Analysis.Fourier.FourierTransformDeriv
import Tengoku.Seed.Topology.Compactness.Compact
import Tengoku.FltAnthropic.P2M.Sol.S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_forall_bound_iteratedFDeriv_cpow_neg_radC_of_isCompact

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_forall_bound_iteratedFDeriv_cpow_neg_radC_of_isCompact.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open _root_.MeasureTheory open _root_.AutomorphicForm.ComplexIwasawa hiding exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact
open scoped ContDiff

theorem AutomorphicForm.ComplexIwasawa.contDiff_and_exists_forall_bound_iteratedFDeriv_cpow_neg_radC_of_isCompact
    (𝒢 : Set (Matrix (Fin 2) (Fin 2) ℂ)) (_h𝒢 : IsCompact 𝒢) (_hdet : ∀ g ∈ 𝒢, g.det ≠ 0)
    (U : Set ℂ) (_hU : IsCompact U) (n : ℕ) :
    (∀ g ∈ 𝒢, ∀ u : ℂ, ContDiff ℝ ∞ (fun z : ℂ => ((radC g z : ℂ) ^ (-u)))) ∧
    ∃ K : ℝ, 0 < K ∧ ∀ g ∈ 𝒢, ∀ u ∈ U, ∀ z : ℂ,
      ‖iteratedFDeriv ℝ n (fun z : ℂ => ((radC g z : ℂ) ^ (-u))) z‖ ≤ K * radC g z ^ (-u.re) := by exact @_root_.P2MW.S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_forall_bound_iteratedFDeriv_cpow_neg_radC_of_isCompact.solution 𝒢 _h𝒢 _hdet U _hU n
