import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_DrinfeldCurve_LocalChart
import Tengoku.FltAnthropic.P2M.Sol.S_DrinfeldCurve_LocalChart_coeff_mem_span_of_eq_add_rel_mul_of_forall_coeff_eq_zero

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_DrinfeldCurve_LocalChart_coeff_mem_span_of_eq_add_rel_mul_of_forall_coeff_eq_zero.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open IsLocalRing

theorem DrinfeldCurve.LocalChart.coeff_mem_span_of_eq_add_rel_mul_of_forall_coeff_eq_zero
    (W : Type) [CommRing W] [IsDomain W] (π : W) (hπ : π ≠ 0)
    (f u v : MvPowerSeries (Fin 2) W) (hv : IsUnit v) (hf : MvPowerSeries.coeff (0 : Fin 2 →₀ ℕ) f = 0)
    (e : ℕ) (g g₁ r : MvPowerSeries (Fin 2) W)
    (hg : ∀ n : Fin 2 →₀ ℕ, n 0 + n 1 < e → MvPowerSeries.coeff n g = 0)
    (hg₁ : ∀ n : Fin 2 →₀ ℕ, n 0 + n 1 < e + 1 → MvPowerSeries.coeff n g₁ = 0)
    (hrel : g = g₁ + (MvPowerSeries.C π * v - f * u) * r)
    (n : Fin 2 →₀ ℕ) (hn : n 0 + n 1 = e) :
    MvPowerSeries.coeff n g ∈ Ideal.span {π} := by exact @_root_.P2MW.S_DrinfeldCurve_LocalChart_coeff_mem_span_of_eq_add_rel_mul_of_forall_coeff_eq_zero.solution W _ _ π hπ f u v hv hf e g g₁ r hg hg₁ hrel n hn
