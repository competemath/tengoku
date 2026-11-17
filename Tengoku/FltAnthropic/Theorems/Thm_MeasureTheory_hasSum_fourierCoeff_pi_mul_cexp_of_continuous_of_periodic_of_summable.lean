import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_MeasureTheory_hasSum_fourierCoeff_pi_mul_cexp_of_continuous_of_periodic_of_summable

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MeasureTheory_hasSum_fourierCoeff_pi_mul_cexp_of_continuous_of_periodic_of_summable.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.hasSum_fourierCoeff_pi_mul_cexp_of_continuous_of_periodic_of_summable
    {c : ℕ} (F : (Fin c → ℝ) → ℂ) (hF : Continuous F)
    (hper : ∀ (θ : Fin c → ℝ) (j : Fin c), F (θ + Pi.single j 1) = F θ)
    (hsum : Summable fun m : Fin c → ℤ =>
      ‖∫ θ in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1),
          F θ * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ)))‖)
    (θ : Fin c → ℝ) :
    HasSum (fun m : Fin c → ℤ =>
      (∫ θ' in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1),
          F θ' * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ' j : ℝ) : ℂ)))) *
        Complex.exp (2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ))) (F θ) := by exact @_root_.P2MW.S_MeasureTheory_hasSum_fourierCoeff_pi_mul_cexp_of_continuous_of_periodic_of_summable.solution c F hF hper hsum θ
