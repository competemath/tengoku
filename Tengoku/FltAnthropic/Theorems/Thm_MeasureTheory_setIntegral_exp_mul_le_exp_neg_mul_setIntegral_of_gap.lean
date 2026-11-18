import Tengoku.Seed.MeasureTheory.Integral.Bochner.Set
import Tengoku.Seed.MeasureTheory.Measure.Lebesgue.Basic
import Tengoku.Seed.Analysis.SpecialFunctions.Log.Basic
import Tengoku.Seed.Topology.Algebra.Order.Field
import Tengoku.FltAnthropic.P2M.Sol.S_MeasureTheory_setIntegral_exp_mul_le_exp_neg_mul_setIntegral_of_gap

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MeasureTheory_setIntegral_exp_mul_le_exp_neg_mul_setIntegral_of_gap.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MeasureTheory Set

theorem MeasureTheory.setIntegral_exp_mul_le_exp_neg_mul_setIntegral_of_gap
    (φ : ℝ → ℝ) (hφm : Measurable φ) (hφmax : ∀ v, φ v ≤ φ 0)
    (γ δ ρ : ℝ) (hγ : 0 < γ) (hρ : 0 < ρ) (hρδ : ρ ≤ δ)
    (hout : ∀ v, δ < |v| → φ v ≤ φ 0 - γ) (hin : ∀ v, |v| ≤ ρ → φ 0 - γ / 2 ≤ φ v)
    (H : ℝ → ℝ) (Λ₀ : ℝ) (hΛ₀ : 0 ≤ Λ₀)
    (hHint : Integrable (fun v => Real.exp (Λ₀ * (φ v - φ 0 + γ)) * H v))
    (hHloc : IntegrableOn H {v | |v| ≤ δ})
    (h : ℝ → ℝ) (hhm : Measurable h) (hh0 : ∀ v, 0 ≤ h v) (hhH : ∀ v, h v ≤ H v)
    (cm : ℝ) (hhin : ∀ v, |v| ≤ ρ → Real.exp cm ≤ h v)
    (Λ : ℝ) (hΛ : Λ₀ ≤ Λ) :
    IntegrableOn (fun v => Real.exp (Λ * φ v) * h v) {v | δ < |v|} ∧
    IntegrableOn (fun v => Real.exp (Λ * φ v) * h v) {v | |v| ≤ δ} ∧
    ∫ v in {v | δ < |v|}, Real.exp (Λ * φ v) * h v ≤
      ((∫ v, Real.exp (Λ₀ * (φ v - φ 0 + γ)) * H v) * Real.exp (-cm) / (2 * ρ)) * Real.exp (-(Λ * γ / 2)) *
        ∫ v in {v | |v| ≤ δ}, Real.exp (Λ * φ v) * h v := by exact @_root_.P2MW.S_MeasureTheory_setIntegral_exp_mul_le_exp_neg_mul_setIntegral_of_gap.solution φ hφm hφmax γ δ ρ hγ hρ hρδ hout hin H Λ₀ hΛ₀ hHint hHloc h hhm hh0 hhH cm hhin Λ hΛ
