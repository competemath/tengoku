import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Valued_v_tprod_eq_finsetProd_of_forall_not_mem_v_eq_one

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Valued_v_tprod_eq_finsetProd_of_forall_not_mem_v_eq_one.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped Topology

theorem Valued.v_tprod_eq_finsetProd_of_forall_not_mem_v_eq_one
    {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    {ι : Type*} (f : ι → K) (hf : Multipliable f)
    (S : Finset ι) (hS : ∀ i, i ∉ S → Valued.v (f i) = 1) :
    Valued.v (∏' i, f i) = ∏ i ∈ S, Valued.v (f i) := by exact @_root_.P2MW.S_Valued_v_tprod_eq_finsetProd_of_forall_not_mem_v_eq_one.solution K _ Γ₀ _ _ ι f hf S hS
