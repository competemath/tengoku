import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_MvPowerSeries_smul_eq_smul_of_forall_coeff_sub_mem_of_forall_mul_eq_zero

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MvPowerSeries_smul_eq_smul_of_forall_coeff_sub_mem_of_forall_mul_eq_zero.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u w
/--
@isnad1 id=eq.2h6v.s9.36b50534142f from=translated src=- shape=8cfe8781 vocab=76db39d1
-/
theorem MvPowerSeries.smul_eq_smul_of_forall_coeff_sub_mem_of_forall_mul_eq_zero
    {R : Type u} [CommRing R] {τ : Type w} (M : Ideal R) (j : R) (hj : ∀ m ∈ M, m * j = 0)
    (g g' : MvPowerSeries τ R) (h : ∀ n, MvPowerSeries.coeff n g - MvPowerSeries.coeff n g' ∈ M) :
    j • g = j • g' := by exact @_root_.P2MW.S_MvPowerSeries_smul_eq_smul_of_forall_coeff_sub_mem_of_forall_mul_eq_zero.solution R _ τ M j hj g g' h
