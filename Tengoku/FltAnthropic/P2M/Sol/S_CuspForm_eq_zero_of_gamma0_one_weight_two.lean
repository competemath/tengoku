import Tengoku.Seed.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Tengoku.Seed.NumberTheory.ModularForms.CongruenceSubgroups

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_CuspForm_eq_zero_of_gamma0_one_weight_two.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_CuspForm_eq_zero_of_gamma0_one_weight_two

set_option autoImplicit false

open scoped MatrixGroups
open CongruenceSubgroup

/--
@isnad1 id=eq.0h0v.s7.00e8e41872cb from=translated src=- shape=5c97c7a6 vocab=4e17ca46
-/
theorem Gamma0_one_eq_top : Gamma0 1 = ⊤ := by
  ext A
  simp only [Gamma0_mem, Subgroup.mem_top, iff_true]
  exact Subsingleton.elim _ _

/--
@isnad1 id=eq.0h0v.s8.b9860d4bdb15 from=translated src=- shape=516c33d9 vocab=bdfa8f94
-/
theorem Gamma0_one_coe_eq_SL : (↑(Gamma0 1) : Subgroup (GL (Fin 2) ℝ)) = 𝒮ℒ := by
  rw [Gamma0_one_eq_top]
  simp [MonoidHom.range_eq_map]

/--
@isnad1 id=eq.2h3v.s8.881e6de5b411 from=translated src=- shape=498d73dd vocab=d985e2c8
-/
theorem cuspForm_eq_zero_of_eq_SL {Γ : Subgroup (GL (Fin 2) ℝ)} (hΓ : Γ = 𝒮ℒ) {k : ℤ} (hk : k < 12)
    (f : CuspForm Γ k) : f = 0 := by
  subst hΓ
  exact rank_zero_iff_forall_zero.mp (CuspForm.rank_eq_zero_of_weight_lt_twelve hk) f

/--
@isnad1 id=eq.0h1v.s9.0e0acc66cca1 from=translated src=- shape=571d3fe5 vocab=856228bc
-/
theorem solution (f : CuspForm (CongruenceSubgroup.Gamma0 1) 2) : f = 0 :=
  cuspForm_eq_zero_of_eq_SL Gamma0_one_coe_eq_SL (by norm_num) f
