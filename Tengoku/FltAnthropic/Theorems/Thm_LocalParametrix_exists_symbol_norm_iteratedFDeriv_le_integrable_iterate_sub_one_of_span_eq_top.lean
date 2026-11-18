import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_LocalParametrix_exists_symbol_norm_iteratedFDeriv_le_integrable_iterate_sub_one_of_span_eq_top

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LocalParametrix_exists_symbol_norm_iteratedFDeriv_le_integrable_iterate_sub_one_of_span_eq_top.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MeasureTheory
open scoped InnerProductSpace

theorem LocalParametrix.exists_symbol_norm_iteratedFDeriv_le_integrable_iterate_sub_one_of_span_eq_top
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    {ι : Type*} [Fintype ι] (B : ι → V →L[ℝ] V) (v : ι → V)
    (hv : Submodule.span ℝ (Set.range v) = ⊤)
    (m : ℕ) (hm : Module.finrank ℝ V < 2 * m) :
    ∃ r : V → ℂ, ContDiff ℝ (⊤ : ℕ∞) r ∧
      (∀ n : ℕ, ∃ C : ℝ, ∀ ξ : V, ‖iteratedFDeriv ℝ n r ξ‖ ≤ C * (1 + ‖ξ‖) ^ (-(2 * m + n : ℝ))) ∧
      Integrable (fun ξ : V => ((fun (g : V → ℂ) (η : V) => ∑ i,
          (iteratedFDeriv ℝ 2 g η (fun _ => ContinuousLinearMap.adjoint (B i) η) +
            (4 * Real.pi * Complex.I) * ((⟪η, v i⟫_ℝ : ℝ) : ℂ) *
              fderiv ℝ g η (ContinuousLinearMap.adjoint (B i) η) -
            (4 * Real.pi ^ 2 : ℂ) * ((⟪η, v i⟫_ℝ : ℝ) : ℂ) ^ 2 * g η))^[m] r) ξ - 1) := by exact @_root_.P2MW.S_LocalParametrix_exists_symbol_norm_iteratedFDeriv_le_integrable_iterate_sub_one_of_span_eq_top.solution V _ _ _ _ _ ι _ B v hv m hm
