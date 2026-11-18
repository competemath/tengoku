import Tengoku.FltAnthropic.Definitions.Def_LanglandsTunnell_HonestLDatum
import Tengoku.FltAnthropic.P2M.Sol.S_LanglandsTunnell_Converse_MellinUniqueness_eq_of_laplace_eq_of_boundedOnStrips

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LanglandsTunnell_Converse_MellinUniqueness_eq_of_laplace_eq_of_boundedOnStrips.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false
open MeasureTheory

theorem LanglandsTunnell.Converse.MellinUniqueness.eq_of_laplace_eq_of_boundedOnStrips
    (g₁ g₂ : ℝ → ℂ) (hg₁ : Continuous g₁) (hg₂ : Continuous g₂)
    (c : ℝ) (Λ : ℂ → ℂ) (hΛ : Differentiable ℂ Λ) (hb : LDatum.BoundedOnStrips Λ)
    (h₁ : ∀ s : ℂ, c < s.re →
      Integrable (fun t : ℝ => g₁ t * Complex.exp (s * (t : ℂ))) ∧ ∫ t : ℝ, g₁ t * Complex.exp (s * (t : ℂ)) = Λ s)
    (h₂ : ∀ s : ℂ, s.re < -c →
      Integrable (fun t : ℝ => g₂ t * Complex.exp (s * (t : ℂ))) ∧ ∫ t : ℝ, g₂ t * Complex.exp (s * (t : ℂ)) = Λ s) :
    g₁ = g₂ := by exact @_root_.P2MW.S_LanglandsTunnell_Converse_MellinUniqueness_eq_of_laplace_eq_of_boundedOnStrips.solution g₁ g₂ hg₁ hg₂ c Λ hΛ hb h₁ h₂
