import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_ComplexIwasawa
import Tengoku.Seed.Analysis.Fourier.FourierTransformDeriv
import Tengoku.Seed.Topology.Compactness.Compact
import Tengoku.FltAnthropic.P2M.Sol.S_AutomorphicForm_ComplexIwasawa_exists_forall_integrable_integral_rpow_neg_radC_le_of_isCompact

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AutomorphicForm_ComplexIwasawa_exists_forall_integrable_integral_rpow_neg_radC_le_of_isCompact.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MeasureTheory AutomorphicForm.ComplexIwasawa
open scoped ContDiff

theorem AutomorphicForm.ComplexIwasawa.exists_forall_integrable_integral_rpow_neg_radC_le_of_isCompact
    (𝒢 : Set (Matrix (Fin 2) (Fin 2) ℂ)) (_h𝒢 : IsCompact 𝒢) (_hdet : ∀ g ∈ 𝒢, g.det ≠ 0)
    (κ₀ κ₁ : ℝ) (_hκ₀ : 2 < κ₀) :
    ∃ M : ℝ, 0 < M ∧ ∀ g ∈ 𝒢, ∀ κ : ℝ, κ₀ ≤ κ → κ ≤ κ₁ →
      Integrable (fun z : ℂ => radC g z ^ (-κ)) ∧ ∫ z : ℂ, radC g z ^ (-κ) ≤ M := by exact @_root_.P2MW.S_AutomorphicForm_ComplexIwasawa_exists_forall_integrable_integral_rpow_neg_radC_le_of_isCompact.solution 𝒢 _h𝒢 _hdet κ₀ κ₁ _hκ₀
