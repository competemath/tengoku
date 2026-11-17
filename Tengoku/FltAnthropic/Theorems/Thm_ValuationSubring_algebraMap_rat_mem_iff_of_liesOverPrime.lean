import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_Ramification
import Tengoku.FltAnthropic.P2M.Sol.S_ValuationSubring_algebraMap_rat_mem_iff_of_liesOverPrime

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ValuationSubring_algebraMap_rat_mem_iff_of_liesOverPrime.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

theorem ValuationSubring.algebraMap_rat_mem_iff_of_liesOverPrime
    (A : ValuationSubring (AlgebraicClosure ℚ)) {q : ℕ} [Fact q.Prime] (hA : A.LiesOverPrime q) (x : ℚ) :
    algebraMap ℚ (AlgebraicClosure ℚ) x ∈ A ↔ x ∈ (Rat.padicValuation q).valuationSubring := by exact @_root_.P2MW.S_ValuationSubring_algebraMap_rat_mem_iff_of_liesOverPrime.solution A q _ hA x
