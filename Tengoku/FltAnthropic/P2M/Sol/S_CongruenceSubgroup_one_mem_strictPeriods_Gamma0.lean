import Tengoku.Seed.NumberTheory.ModularForms.CongruenceSubgroups
import Tengoku.Seed.NumberTheory.ModularForms.Cusps
import Tengoku.Seed.Algebra.Lie.OfAssociative
import Tengoku.Seed.Algebra.Algebra.Rat

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_CongruenceSubgroup_one_mem_strictPeriods_Gamma0.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_CongruenceSubgroup_one_mem_strictPeriods_Gamma0

set_option autoImplicit false

open scoped MatrixGroups

theorem solution (N : ℕ) : (1 : ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma0 N)).strictPeriods := by
  have hT : ModularGroup.T ∈ CongruenceSubgroup.Gamma0 N := by
    rw [CongruenceSubgroup.Gamma0_mem]
    simp [ModularGroup.T]
  have h := Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT
  rw [h]
  exact AddSubgroup.mem_zmultiples (1 : ℝ)
