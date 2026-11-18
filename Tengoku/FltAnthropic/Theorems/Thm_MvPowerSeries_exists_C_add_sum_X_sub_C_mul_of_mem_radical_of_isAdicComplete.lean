import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_MvPowerSeries_exists_C_add_sum_X_sub_C_mul_of_mem_radical_of_isAdicComplete

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MvPowerSeries_exists_C_add_sum_X_sub_C_mul_of_mem_radical_of_isAdicComplete.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open MvPowerSeries

universe u

theorem MvPowerSeries.exists_C_add_sum_X_sub_C_mul_of_mem_radical_of_isAdicComplete
    {E : Type u} [CommRing E] (J : Ideal E) [IsAdicComplete J E]
    {d : ℕ} (b : Fin d → E) (hb : ∀ i, b i ∈ J.radical) (c : MvPowerSeries (Fin d) E) :
    ∃ (r : E) (q : Fin d → MvPowerSeries (Fin d) E),
      c = MvPowerSeries.C r + ∑ i, (MvPowerSeries.X i - MvPowerSeries.C (b i)) * q i := by exact @_root_.P2MW.S_MvPowerSeries_exists_C_add_sum_X_sub_C_mul_of_mem_radical_of_isAdicComplete.solution E _ J _ d b hb c
