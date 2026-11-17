import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_DrinfeldCurve_LocalChart
import Tengoku.FltAnthropic.P2M.Sol.S_MvPowerSeries_mem_span_X_pow_iff_forall_coeff_eq_zero_of_degree_lt

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MvPowerSeries_mem_span_X_pow_iff_forall_coeff_eq_zero_of_degree_lt.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open IsLocalRing

/--
@isnad1 id=iff.0h3v.s9.373296bd5b8d from=translated src=- shape=5b464554 vocab=ba08a040
-/
theorem MvPowerSeries.mem_span_X_pow_iff_forall_coeff_eq_zero_of_degree_lt
    (W : Type) [CommRing W] (e : ℕ) (g : MvPowerSeries (Fin 2) W) :
    g ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ e ↔
      ∀ n : Fin 2 →₀ ℕ, n 0 + n 1 < e → MvPowerSeries.coeff n g = 0 := by exact @_root_.P2MW.S_MvPowerSeries_mem_span_X_pow_iff_forall_coeff_eq_zero_of_degree_lt.solution W _ e g
