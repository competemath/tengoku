import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_ComplexIwasawa
import Tengoku.Seed.Analysis.Fourier.FourierTransformDeriv
import Tengoku.Seed.Topology.Compactness.Compact
import Tengoku.FltAnthropic.P2M.Sol.S_AutomorphicForm_ComplexIwasawa_exists_forall_norm_fourierIntegral_cpow_radC_mul_le_polyDecay_of_isCompact

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AutomorphicForm_ComplexIwasawa_exists_forall_norm_fourierIntegral_cpow_radC_mul_le_polyDecay_of_isCompact.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MeasureTheory AutomorphicForm.ComplexIwasawa
open scoped ContDiff FourierTransform

/--
@isnad1 id=ex.8h6v.s12.a72a66059a66 from=translated src=- shape=fc581bf1 vocab=e1e50e60
-/
theorem AutomorphicForm.ComplexIwasawa.exists_forall_norm_fourierIntegral_cpow_radC_mul_le_polyDecay_of_isCompact
    (𝒢 : Set (Matrix (Fin 2) (Fin 2) ℂ)) (h𝒢 : IsCompact 𝒢) (hdet : ∀ g ∈ 𝒢, g.det ≠ 0)
    (U : Set ℂ) (hU : IsCompact U) (hU2 : ∀ u ∈ U, 2 < u.re)
    (P : Matrix (Fin 2) (Fin 2) ℂ → ℂ → ℂ) (hPC : ∀ g ∈ 𝒢, ContDiff ℝ ∞ (P g))
    (hPB : ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ g ∈ 𝒢, ∀ z : ℂ, ‖iteratedFDeriv ℝ n (P g) z‖ ≤ C)
    (L : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) {c : ℝ} (hc : 0 < c)
    (hL : ∀ ξ : ℂ, ∃ v : ℂ, ‖v‖ ≤ 1 ∧ c * ‖ξ‖ ≤ ‖L v ξ‖)
    (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ g ∈ 𝒢, ∀ u ∈ U, ∀ ξ : ℂ,
      ‖VectorFourier.fourierIntegral 𝐞 volume L.toLinearMap₁₂
          (fun z => ((radC g z : ℂ) ^ (-u)) * P g z) ξ‖
        ≤ C * (1 + ‖ξ‖) ^ (-(N : ℝ)) := by exact @_root_.P2MW.S_AutomorphicForm_ComplexIwasawa_exists_forall_norm_fourierIntegral_cpow_radC_mul_le_polyDecay_of_isCompact.solution 𝒢 h𝒢 hdet U hU hU2 P hPC hPB L c hc hL N
