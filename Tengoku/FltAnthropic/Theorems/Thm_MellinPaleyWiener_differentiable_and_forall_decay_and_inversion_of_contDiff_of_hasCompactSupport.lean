import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_MellinPaleyWiener_differentiable_and_forall_decay_and_inversion_of_contDiff_of_hasCompactSupport

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MellinPaleyWiener_differentiable_and_forall_decay_and_inversion_of_contDiff_of_hasCompactSupport.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MeasureTheory

/--
@isnad1 id=and.2h1v.s8.b4d66d1aeac4 from=translated src=- shape=c1e75e1b vocab=2a85af8e
-/
theorem MellinPaleyWiener.differentiable_and_forall_decay_and_inversion_of_contDiff_of_hasCompactSupport
    (h : ℝ → ℂ) (_hh : ContDiff ℝ (⊤ : ℕ∞) h) (_hhc : HasCompactSupport h) :
    Differentiable ℂ (fun s : ℂ => ∫ u : ℝ, h u * Complex.exp (s * (u : ℂ))) ∧
    (∀ (n : ℕ) (σ₀ : ℝ), ∃ C : ℝ, 0 ≤ C ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ → ∀ t : ℝ,
      (1 + |t|) ^ n * ‖∫ u : ℝ, h u * Complex.exp (((σ' : ℂ) + (t : ℂ) * Complex.I) * (u : ℂ))‖ ≤ C) ∧
    (∀ (σ' u : ℝ), h u = (((2 * Real.pi)⁻¹ : ℝ) : ℂ) *
      ∫ t : ℝ, (∫ v : ℝ, h v * Complex.exp (((σ' : ℂ) + (t : ℂ) * Complex.I) * (v : ℂ))) *
        Complex.exp (-(((σ' : ℂ) + (t : ℂ) * Complex.I) * (u : ℂ)))) := by exact @_root_.P2MW.S_MellinPaleyWiener_differentiable_and_forall_decay_and_inversion_of_contDiff_of_hasCompactSupport.solution h _hh _hhc
