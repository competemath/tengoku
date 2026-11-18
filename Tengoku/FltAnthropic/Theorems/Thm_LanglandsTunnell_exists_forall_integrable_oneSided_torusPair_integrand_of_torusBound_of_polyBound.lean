import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Complex
import Tengoku.Seed.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Tengoku.Seed.MeasureTheory.Integral.Prod
import Tengoku.FltAnthropic.P2M.Sol.S_LanglandsTunnell_exists_forall_integrable_oneSided_torusPair_integrand_of_torusBound_of_polyBound

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LanglandsTunnell_exists_forall_integrable_oneSided_torusPair_integrand_of_torusBound_of_polyBound.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MeasureTheory Set

theorem LanglandsTunnell.exists_forall_integrable_oneSided_torusPair_integrand_of_torusBound_of_polyBound
    (β : ℂ) (g : ℝ → ℂ) (hg : Measurable g) (Cg σg : ℝ) (hσg : 0 ≤ σg)
    (hgb : ∀ τ : ℝ, τ ≠ 0 → ‖g τ‖ ≤ Cg * (1 + |τ| ^ (-σg)))
    (B : ℝ → ℝ → ℝ → ℝ → ℂ) (hB : Measurable fun x : ℝ × ℝ × ℝ × ℝ => B x.1 x.2.1 x.2.2.1 x.2.2.2)
    (CB : ℝ) (N : ℕ)
    (hBb : ∀ p q r z : ℝ, ‖B p q r z‖ ≤ CB * (1 + |p|) ^ N * (1 + |q|) ^ N * (1 + |r|) ^ N * (1 + |z|) ^ N) :
    ∃ σ₀ : ℝ, ∀ α γ : ℂ, σ₀ < α.re → γ.re < -σ₀ →
      Integrable (fun x : ℝ × ℝ × ℝ × ℝ =>
        ((x.1 : ℝ) : ℂ) ^ α * (Real.exp (-(2 * Real.pi * x.1)) : ℂ) *
          ((|x.2.1| : ℝ) : ℂ) ^ β * ((x.2.2.1 : ℝ) : ℂ) ^ γ *
          (Real.exp (-(Real.pi * ((x.2.1 ^ 2)⁻¹ + x.1 ^ 2 * x.2.1 ^ 2 + (x.2.2.1 ^ 2)⁻¹))) : ℂ) *
          g (x.1 * |x.2.1| / x.2.2.1) *
          (B (x.2.1⁻¹) (x.2.2.1⁻¹) (x.1 * x.2.1) x.2.2.2 * (Real.exp (-(Real.pi * x.2.2.2 ^ 2)) : ℂ)))
        ((volume.restrict (Ioi (0 : ℝ))).prod ((volume.restrict (Iio (0 : ℝ))).prod
          ((volume.restrict (Ioi (0 : ℝ))).prod volume))) := by exact @_root_.P2MW.S_LanglandsTunnell_exists_forall_integrable_oneSided_torusPair_integrand_of_torusBound_of_polyBound.solution β g hg Cg σg hσg hgb B hB CB N hBb
