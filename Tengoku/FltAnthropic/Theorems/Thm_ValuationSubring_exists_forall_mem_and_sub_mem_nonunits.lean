import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_ValuationSubring_exists_forall_mem_and_sub_mem_nonunits

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ValuationSubring_exists_forall_mem_and_sub_mem_nonunits.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

theorem ValuationSubring.exists_forall_mem_and_sub_mem_nonunits
    {K : Type*} [Field K] {ι : Type*} [Finite ι] (R : ι → ValuationSubring K)
    (hR : ∀ i j, R i ≤ R j → i = j) (a : ι → K) (ha : ∀ i, a i ∈ R i) :
    ∃ z : K, ∀ i, z ∈ R i ∧ z - a i ∈ (R i).nonunits := by exact @_root_.P2MW.S_ValuationSubring_exists_forall_mem_and_sub_mem_nonunits.solution K _ ι _ R hR a ha
