import Tengoku.Seed.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Tengoku.Seed.NumberTheory.Bernoulli

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_qExpansion_E6_eq_map_mk.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_qExpansion_E6_eq_map_mk

open UpperHalfPlane ModularForm Finset

private lemma bernoulli'_five_s18 : bernoulli' 5 = 0 :=
  bernoulli'_eq_zero_of_odd (by decide) (by norm_num)

private lemma bernoulli'_six_s18 : bernoulli' 6 = 1 / 42 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_zero, bernoulli'_one, bernoulli'_two,
    bernoulli'_three, bernoulli'_four, bernoulli'_five_s18, Nat.choose]

private lemma bernoulli_six_s18 : bernoulli 6 = 1 / 42 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_six_s18]

/--
@isnad1 id=eq.0h0v.s8.77dbe2622a79 from=translated src=- shape=865795b1 vocab=5a482b13
-/
theorem solution :
    UpperHalfPlane.qExpansion 1 ⇑ModularForm.E₆ =
      PowerSeries.map (Int.castRingHom ℂ)
        (PowerSeries.mk fun n => if n = 0 then 1 else -504 * ∑ d ∈ n.divisors, (d : ℤ) ^ 5) := by
  ext m
  rw [show (ModularForm.E₆ : ModularForm _ 6) = E (by norm_num : 3 ≤ 6) from rfl]
  rw [EisensteinSeries.E_qExpansion_coeff (by norm_num : 3 ≤ 6) (by decide) m]
  simp only [PowerSeries.coeff_map, PowerSeries.coeff_mk]
  split_ifs with hm
  · simp
  · have hB : (bernoulli 6 : ℂ) = 1 / 42 := by
      rw [bernoulli_six_s18]; push_cast; ring
    rw [ArithmeticFunction.sigma_apply]
    push_cast
    rw [hB]
    norm_num
