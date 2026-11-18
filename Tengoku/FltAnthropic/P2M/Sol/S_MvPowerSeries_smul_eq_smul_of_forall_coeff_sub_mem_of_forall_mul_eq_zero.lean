import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_MvPowerSeries_smul_eq_smul_of_forall_coeff_sub_mem_of_forall_mul_eq_zero.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_MvPowerSeries_smul_eq_smul_of_forall_coeff_sub_mem_of_forall_mul_eq_zero

set_option autoImplicit false

universe u w

/--
@isnad1 id=eq.2h6v.s9.36b50534142f from=translated src=- shape=8cfe8781 vocab=76db39d1
-/
theorem solution
    {R : Type u} [CommRing R] {τ : Type w} (M : Ideal R) (j : R) (hj : ∀ m ∈ M, m * j = 0)
    (g g' : MvPowerSeries τ R) (h : ∀ n, MvPowerSeries.coeff n g - MvPowerSeries.coeff n g' ∈ M) :
    j • g = j • g' := by
  refine MvPowerSeries.ext fun n => ?_
  rw [MvPowerSeries.coeff_smul, MvPowerSeries.coeff_smul]
  have h0 : (MvPowerSeries.coeff n g - MvPowerSeries.coeff n g') * j = 0 := hj _ (h n)
  rw [sub_mul, sub_eq_zero] at h0
  rw [mul_comm, h0, mul_comm]
