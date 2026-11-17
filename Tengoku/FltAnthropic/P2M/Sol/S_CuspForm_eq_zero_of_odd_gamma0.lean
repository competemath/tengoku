import Tengoku.Seed.NumberTheory.ModularForms.Basic
import Tengoku.Seed.NumberTheory.ModularForms.CongruenceSubgroups

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_CuspForm_eq_zero_of_odd_gamma0.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_CuspForm_eq_zero_of_odd_gamma0

set_option autoImplicit false

/--
@isnad1 id=eq.1h3v.s9.fd819ef495d7 from=translated src=- shape=7d4e36f4 vocab=57d95e34
-/
theorem solution (N : ℕ) (k : ℤ) (hk : Odd k)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) : f = 0 := by
  have hΓ : (-1 : GL (Fin 2) ℝ) ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) := by
    refine ⟨-1, ?_, ?_⟩
    · simp [CongruenceSubgroup.Gamma0_mem]
    · ext i j
      simp [Matrix.SpecialLinearGroup.coe_int_neg]
  ext z
  have hf := SlashInvariantForm.slash_action_eqn'' f hΓ z
  rw [UpperHalfPlane.neg_smul, one_smul, UpperHalfPlane.denom_neg, UpperHalfPlane.denom_one,
    Odd.neg_one_zpow hk] at hf
  have h2 : (2 : ℂ) * f z = 0 := by linear_combination hf
  rw [zero_apply]
  exact (mul_eq_zero.mp h2).resolve_left two_ne_zero
