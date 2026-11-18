import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_MvPowerSeries_exists_powerSeries_subst_eq_zero_of_sub_drinfeld_mem_pow

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MvPowerSeries_exists_powerSeries_subst_eq_zero_of_sub_drinfeld_mem_pow.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MvPowerSeries

theorem MvPowerSeries.exists_powerSeries_subst_eq_zero_of_sub_drinfeld_mem_pow
    (q : ℕ) [Fact q.Prime] (k : Type*) [Field k] (hq : (q : k) = 0)
    (f : MvPowerSeries (Fin 2) k)
    (hf : f - (X 0 * X 1 ^ q - X 0 ^ q * X 1) ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) k), X 1}) ^ (q + 2))
    (a : k) (ha : a ^ q = a) :
    ∃ φ : PowerSeries k,
      PowerSeries.constantCoeff φ = 0 ∧ PowerSeries.coeff 1 φ = a ∧
      MvPowerSeries.subst ![(PowerSeries.X : PowerSeries k), φ] f = 0 := by exact @_root_.P2MW.S_MvPowerSeries_exists_powerSeries_subst_eq_zero_of_sub_drinfeld_mem_pow.solution q _ k _ hq f hf a ha
