import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Valued_multipliable_one_add_of_tendsto_cofinite_zero

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Valued_multipliable_one_add_of_tendsto_cofinite_zero.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open Filter Topology

/--
@isnad1 id=multipli.1h4v.s7.796fa828040c from=translated src=- shape=5d10ffd4 vocab=86db749d
-/
theorem Valued.multipliable_one_add_of_tendsto_cofinite_zero
    {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K]
    {ι : Type*} (f : ι → K) (hf : Tendsto f cofinite (𝓝 0)) :
    Multipliable (fun i => 1 + f i) := by exact @_root_.P2MW.S_Valued_multipliable_one_add_of_tendsto_cofinite_zero.solution K _ Γ₀ _ _ _ ι f hf
