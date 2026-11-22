import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_AbsoluteValue_exists_forall_sub_lt_of_pairwise_not_isEquiv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AbsoluteValue_exists_forall_sub_lt_of_pairwise_not_isEquiv.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false
/--
@isnad1 id=ex.3h5v.s7.cb2e5a555c11 from=translated src=- shape=895ff791 vocab=6349aefa
-/
theorem AbsoluteValue.exists_forall_sub_lt_of_pairwise_not_isEquiv {K : Type*} [Field K] {ι : Type*} [Finite ι]
    {v : ι → AbsoluteValue K ℝ} (hv : ∀ i, (v i).IsNontrivial) (hne : Pairwise fun i j => ¬(v i).IsEquiv (v j))
    (a : ι → K) {ε : ℝ} (hε : 0 < ε) : ∃ x : K, ∀ i, v i (x - a i) < ε := by exact @_root_.P2MW.S_AbsoluteValue_exists_forall_sub_lt_of_pairwise_not_isEquiv.solution K _ ι _ v hv hne a ε hε
