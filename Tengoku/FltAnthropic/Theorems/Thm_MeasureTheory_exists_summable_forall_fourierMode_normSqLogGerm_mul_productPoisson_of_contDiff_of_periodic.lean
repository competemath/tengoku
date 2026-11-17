import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_MeasureTheory_exists_summable_forall_fourierMode_normSqLogGerm_mul_productPoisson_of_contDiff_of_periodic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MeasureTheory_exists_summable_forall_fourierMode_normSqLogGerm_mul_productPoisson_of_contDiff_of_periodic.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MeasureTheory

/--
@isnad1 id=other.4h6v.s10.241c9455bf5a from=translated src=- shape=257f6412 vocab=22ffe753
-/
theorem MeasureTheory.exists_summable_forall_fourierMode_normSqLogGerm_mul_productPoisson_of_contDiff_of_periodic
    {r c : ℕ} (W : (Fin r → ℝ) × (Fin c → ℝ) → ℂ) (hW : ContDiff ℝ (⊤ : ℕ∞) W)
    (R : ℝ) (hR : 0 ≤ R) (hsupp : ∀ p : (Fin r → ℝ) × (Fin c → ℝ), (∃ k, R < |p.1 k|) → W p = 0)
    (hper : ∀ (p : (Fin r → ℝ) × (Fin c → ℝ)) (j : Fin c), W (p.1, p.2 + Pi.single j 1) = W p)
    (k : Fin r) (j : Fin c) :
    let Ψ : (Fin c → ℤ) → (Fin r → ℝ) → ℂ := fun m x =>
      ∫ θ in Set.pi Set.univ (fun _ : Fin c => Set.Ico (0 : ℝ) 1),
        ((‖(1 : ℂ) - Complex.exp ((x k / 2 : ℝ) + 2 * Real.pi * Complex.I * (θ j : ℝ))‖ ^ 2 *
              Real.log ‖(1 : ℂ) - Complex.exp ((x k / 2 : ℝ) + 2 * Real.pi * Complex.I * (θ j : ℝ))‖ : ℝ) : ℂ) *
            W (x, θ) * Complex.exp (-(2 * Real.pi * Complex.I * ((∑ j', (m j' : ℝ) * θ j' : ℝ) : ℂ)))
    ∃ C : (Fin c → ℤ) → ℝ, (∀ m, 0 ≤ C m) ∧ Summable C ∧
      ∀ m : Fin c → ℤ, Continuous (Ψ m) ∧ Integrable (Ψ m) ∧
        (∀ x : Fin r → ℝ, ‖Ψ m x‖ ≤ C m * ∏ i, (1 + |x i|)⁻¹ ^ 2) ∧
        (∀ ξ : Fin r → ℝ,
          ‖∫ x : Fin r → ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ((∑ i, ξ i * x i : ℝ) : ℂ))) * Ψ m x‖ ≤
            C m * ∏ i, (1 + |ξ i|)⁻¹ ^ 2) := by exact @_root_.P2MW.S_MeasureTheory_exists_summable_forall_fourierMode_normSqLogGerm_mul_productPoisson_of_contDiff_of_periodic.solution r c W hW R hR hsupp hper k j
