import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_Ramification
import Tengoku.FltAnthropic.P2M.Sol.S_ValuationSubring_valuation_sub_lt_one_of_mem_inertiaSubgroupIn

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ValuationSubring_valuation_sub_lt_one_of_mem_inertiaSubgroupIn.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

theorem ValuationSubring.valuation_sub_lt_one_of_mem_inertiaSubgroupIn {K L : Type*} [Field K]
    [Field L] [Algebra K L] (A : ValuationSubring L) {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ A.inertiaSubgroupIn K) {a : L} (ha : a ∈ A) :
    σ a ∈ A ∧ A.valuation (σ a - a) < 1 := by exact @_root_.P2MW.S_ValuationSubring_valuation_sub_lt_one_of_mem_inertiaSubgroupIn.solution K L _ _ _ A σ hσ a ha
