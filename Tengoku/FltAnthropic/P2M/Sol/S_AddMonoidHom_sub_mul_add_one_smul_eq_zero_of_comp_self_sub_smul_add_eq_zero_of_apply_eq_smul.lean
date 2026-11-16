import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AddMonoidHom_sub_mul_add_one_smul_eq_zero_of_comp_self_sub_smul_add_eq_zero_of_apply_eq_smul.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AddMonoidHom_sub_mul_add_one_smul_eq_zero_of_comp_self_sub_smul_add_eq_zero_of_apply_eq_smul

set_option autoImplicit false

theorem solution
    {V : Type*} [AddCommGroup V] (m : V →+ V) (t : ℤ) (hm : ∀ T, m (m T) - t • m T + T = 0)
    (P : V) (c : ℤ) (hP : m P = c • P) :
    (c ^ 2 - t * c + 1) • P = 0 := by
  have h := hm P
  rw [hP, map_zsmul, hP, smul_smul] at h
  rw [add_smul, sub_smul, one_smul, mul_comm t c, sq, mul_smul, mul_smul] at *
  simpa [smul_smul, mul_comm] using h
