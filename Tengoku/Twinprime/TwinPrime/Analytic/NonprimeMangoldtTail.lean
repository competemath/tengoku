import Tengoku.Twinprime.TwinPrime.Analytic.BilinearExceptional
import Tengoku.Twinprime.TwinPrime.Analytic.PowerDirichletTail

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Reciprocal tails of the proper-prime-power Mangoldt weight

The actual nonprime Mangoldt sum is `psi - theta`. Its proved square-root
bound and nonnegativity give a uniform reciprocal tail by finite Abel
summation. No distribution estimate is supplied as a hypothesis.
-/

noncomputable section

open Finset

namespace TwinPrime.Analytic

theorem exists_nonprimeMangoldt_sqrt_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℕ,
      (∑ n ∈ Ioc 0 T, nonprimeMangoldt n) ≤ C * Real.sqrt T := by
  obtain ⟨K, hK⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨|K| + 1, by positivity, ?_⟩
  intro T
  rw [sum_nonprimeMangoldt_eq]
  exact (hK T).trans (mul_le_mul_of_nonneg_right
    (by linarith [le_abs_self K]) (Real.sqrt_nonneg _))

/-- The finite tail bound with its explicit factor three. Nonnegativity
allows the anchored partial sums to use the same square-root constant.-/
theorem sum_nonprimeMangoldt_div_le_of_sqrt_bound (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ T : ℕ, (∑ n ∈ Ioc 0 T, nonprimeMangoldt n) ≤ C * Real.sqrt T)
    (V T : ℕ) (hV : 1 ≤ V) :
    (∑ n ∈ Ioc V T, nonprimeMangoldt n / n) ≤
      (3 * C) * (V : ℝ) ^ (-1 / 2 : ℝ) := by
  by_cases hVT : V ≤ T
  · have hsum0 (t : ℕ) : 0 ≤ ∑ n ∈ Ioc V t, nonprimeMangoldt n :=
      sum_nonneg fun n _ => nonprimeMangoldt_nonneg n
    have hanchor : ∀ t ∈ Icc V T,
        ‖∑ n ∈ Ioc V t, (nonprimeMangoldt n : ℂ)‖ ≤ C * (t : ℝ) ^ (1 / 2 : ℝ) := by
      intro t _
      rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hsum0 t)]
      calc
        _ ≤ ∑ n ∈ Ioc 0 t, nonprimeMangoldt n := by
          apply sum_le_sum_of_subset_of_nonneg
          · intro n hn
            obtain ⟨hVn, hnt⟩ := mem_Ioc.mp hn
            exact mem_Ioc.mpr ⟨by omega, hnt⟩
          · exact fun n _ _ => nonprimeMangoldt_nonneg n
        _ ≤ C * Real.sqrt t := hA t
        _ = _ := by rw [Real.sqrt_eq_rpow]
    have hb := norm_sum_Ioc_cpow_mul_le_of_anchored_power_sums V T hV hVT
      (1 / 2 : ℝ) (by norm_num) (1 : ℂ) (by norm_num)
      (fun n => (nonprimeMangoldt n : ℂ)) C hC hanchor
    have hcast : (∑ n ∈ Ioc V T, (n : ℂ) ^ (-(1 : ℂ)) * (nonprimeMangoldt n : ℂ)) =
        ((∑ n ∈ Ioc V T, nonprimeMangoldt n / n : ℝ) : ℂ) := by
      push_cast
      apply sum_congr rfl
      intro n _
      rw [Complex.cpow_neg_one, div_eq_mul_inv, mul_comm]
    rw [hcast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sum_nonneg fun n _ => div_nonneg
        (nonprimeMangoldt_nonneg n) (Nat.cast_nonneg n))] at hb
    norm_num at hb
    nlinarith only [hb]
  · rw [Ioc_eq_empty_of_le (Nat.le_of_not_ge hVT), sum_empty]
    positivity

/-- One positive constant controls every finite proper-prime-power
reciprocal tail, including an empty interval when `T < V`.-/
theorem exists_nonprimeMangoldt_reciprocal_tail_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ V : ℕ, 1 ≤ V → ∀ T : ℕ,
      (∑ n ∈ Ioc V T, nonprimeMangoldt n / n) ≤
        C * (V : ℝ) ^ (-1 / 2 : ℝ) := by
  obtain ⟨C, hC, hA⟩ := exists_nonprimeMangoldt_sqrt_bound
  exact ⟨3 * C, by positivity, fun V hV T =>
    sum_nonprimeMangoldt_div_le_of_sqrt_bound C hC.le hA V T hV⟩

end TwinPrime.Analytic
