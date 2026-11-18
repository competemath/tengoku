import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_LocalParametrix_exists_continuous_contDiffOn_apply_eq_integral_iterate_sum_iteratedFDeriv_add_integral_of_span_eq_top

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LocalParametrix_exists_continuous_contDiffOn_apply_eq_integral_iterate_sum_iteratedFDeriv_add_integral_of_span_eq_top.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MeasureTheory Topology

theorem LocalParametrix.exists_continuous_contDiffOn_apply_eq_integral_iterate_sum_iteratedFDeriv_add_integral_of_span_eq_top
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    {ι : Type*} [Fintype ι] (A : ι → V →L[ℝ] V) (x₀ : V)
    (hA : Submodule.span ℝ (Set.range fun i => A i x₀) = ⊤)
    (m : ℕ) (hm : Module.finrank ℝ V < 2 * m) :
    ∃ u w : V → ℂ, Continuous u ∧ Continuous w ∧ ContDiffOn ℝ (⊤ : ℕ∞) u {x₀}ᶜ ∧
      ∀ F : V → ℂ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
        F x₀ = (∫ x, ((fun (G : V → ℂ) (y : V) =>
                  ∑ i, iteratedFDeriv ℝ 2 G y (fun _ => A i y))^[m] F) x * u x) +
          ∫ x, F x * w x := by exact @_root_.P2MW.S_LocalParametrix_exists_continuous_contDiffOn_apply_eq_integral_iterate_sum_iteratedFDeriv_add_integral_of_span_eq_top.solution V _ _ _ _ _ ι _ A x₀ hA m hm
