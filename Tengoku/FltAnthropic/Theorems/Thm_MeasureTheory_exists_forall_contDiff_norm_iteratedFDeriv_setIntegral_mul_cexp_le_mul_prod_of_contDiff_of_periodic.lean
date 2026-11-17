import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_MeasureTheory_exists_forall_contDiff_norm_iteratedFDeriv_setIntegral_mul_cexp_le_mul_prod_of_contDiff_of_periodic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MeasureTheory_exists_forall_contDiff_norm_iteratedFDeriv_setIntegral_mul_cexp_le_mul_prod_of_contDiff_of_periodic.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MeasureTheory

/--
@isnad1 id=ex.4h4v.s10.772d835acc2d from=translated src=- shape=89e7380f vocab=80f57ab0
-/
theorem MeasureTheory.exists_forall_contDiff_norm_iteratedFDeriv_setIntegral_mul_cexp_le_mul_prod_of_contDiff_of_periodic
    {r c : ℕ} (W : (Fin r → ℝ) × (Fin c → ℝ) → ℂ) (hW : ContDiff ℝ (⊤ : ℕ∞) W)
    (R : ℝ) (hR : 0 ≤ R) (hsupp : ∀ p : (Fin r → ℝ) × (Fin c → ℝ), (∃ k, R < |p.1 k|) → W p = 0)
    (hper : ∀ (p : (Fin r → ℝ) × (Fin c → ℝ)) (j : Fin c), W (p.1, p.2 + Pi.single j 1) = W p) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ m : Fin c → ℤ,
      ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin r → ℝ =>
        ∫ θ in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1),
          W (x, θ) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ)))) ∧
      (∀ x : Fin r → ℝ, (∃ k, R < |x k|) →
        (∫ θ in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1),
          W (x, θ) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ)))) = 0) ∧
      ∀ n : ℕ, n ≤ 2 * r → ∀ x : Fin r → ℝ,
        ‖iteratedFDeriv ℝ n (fun x : Fin r → ℝ =>
            ∫ θ in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1),
              W (x, θ) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * θ j : ℝ) : ℂ)))) x‖ ≤
          M * ∏ j, (1 + |(m j : ℝ)|)⁻¹ ^ 2 := by exact @_root_.P2MW.S_MeasureTheory_exists_forall_contDiff_norm_iteratedFDeriv_setIntegral_mul_cexp_le_mul_prod_of_contDiff_of_periodic.solution r c W hW R hR hsupp hper
