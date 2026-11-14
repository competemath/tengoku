import Tengoku.Twinprime.TwinPrime.Analytic.CharacterSums

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The mass excluded by the principal character

The prime terms excluded by a modulus are bounded by the divisor identity
`sum Λ(d) = log q`. The proper prime powers are bounded by the elementary
Chebyshev estimate for `ψ - θ`. The resulting bound is uniform in the
summation endpoint and uses no distribution theorem.
-/

noncomputable section

open Finset ArithmeticFunction

namespace TwinPrime.Analytic

theorem noncoprimeMangoldtMass_mono (q : ℕ) :
    Monotone (fun t => noncoprimeMangoldtMass t q) := by
  intro t T ht
  apply sum_le_sum_of_subset_of_nonneg
  · intro n hn
    obtain ⟨hnI, hnq⟩ := mem_filter.mp hn
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨(mem_Ioc.mp hnI).1,
      (mem_Ioc.mp hnI).2.trans ht⟩, hnq⟩
  · exact fun _ _ _ => vonMangoldt_nonneg

theorem noncoprimeMangoldtMass_le_log_add_psi_sub_theta (t q : ℕ)
    (hq : 0 < q) :
    noncoprimeMangoldtMass t q ≤ Real.log q +
      (Chebyshev.psi (t : ℝ) - Chebyshev.theta (t : ℝ)) := by
  let s := (Ioc 0 t).filter (fun n => ¬ Nat.Coprime n q)
  have hprime : s.filter Nat.Prime ⊆ q.divisors := by
    intro n hn
    obtain ⟨hns, hnp⟩ := mem_filter.mp hn
    have hbad := (mem_filter.mp hns).2
    have hd : n ∣ q := by
      simpa only [hnp.coprime_iff_not_dvd, not_not] using hbad
    exact Nat.mem_divisors.mpr ⟨hd, hq.ne'⟩
  have hnonprime : s.filter (fun n => ¬ n.Prime) ⊆
      (Ioc 0 t).filter (fun n => ¬ n.Prime) := by
    intro n hn
    obtain ⟨hns, hnp⟩ := mem_filter.mp hn
    exact mem_filter.mpr ⟨(mem_filter.mp hns).1, hnp⟩
  have hp : (∑ n ∈ s.filter Nat.Prime, vonMangoldt n) ≤ Real.log q := by
    rw [← vonMangoldt_sum (n := q)]
    exact sum_le_sum_of_subset_of_nonneg hprime (fun _ _ _ => vonMangoldt_nonneg)
  have hn : (∑ n ∈ s.filter (fun n => ¬ n.Prime), vonMangoldt n) ≤
      Chebyshev.psi (t : ℝ) - Chebyshev.theta (t : ℝ) := by
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast]
    exact sum_le_sum_of_subset_of_nonneg hnonprime (fun _ _ _ => vonMangoldt_nonneg)
  calc
    noncoprimeMangoldtMass t q =
        (∑ n ∈ s.filter Nat.Prime, vonMangoldt n) +
        ∑ n ∈ s.filter (fun n => ¬ n.Prime), vonMangoldt n :=
      (sum_filter_add_sum_filter_not s Nat.Prime vonMangoldt).symm
    _ ≤ _ := add_le_add hp hn

theorem noncoprimeMangoldtMass_le (t q : ℕ) (ht : 1 ≤ t) (hq : 1 ≤ q) :
    noncoprimeMangoldtMass t q ≤
      Real.log q + 2 * Real.sqrt t * Real.log t := by
  exact (noncoprimeMangoldtMass_le_log_add_psi_sub_theta t q hq).trans
    (add_le_add le_rfl (Chebyshev.psi_sub_theta_le (x := (t : ℝ))
      (by exact_mod_cast ht)))

theorem noncoprimeMangoldtMass_le_uniform (T q : ℕ) (hT : 1 ≤ T) (hq : 1 ≤ q)
    {t : ℕ} (ht : t ≤ T) :
    noncoprimeMangoldtMass t q ≤
      Real.log q + 2 * Real.sqrt T * Real.log T :=
  (noncoprimeMangoldtMass_mono q ht).trans (noncoprimeMangoldtMass_le T q hT hq)

/-- The endpoint may vary with the modulus, as in a maximal progression error.-/
theorem sum_noncoprimeMangoldtMass_le_uniform (T Q : ℕ) (hT : 1 ≤ T)
    (t : ℕ → ℕ) (ht : ∀ q ∈ Ioc 0 Q, t q ≤ T) :
    (∑ q ∈ Ioc 0 Q, noncoprimeMangoldtMass (t q) q) ≤
      Q * (Real.log Q + 2 * Real.sqrt T * Real.log T) := by
  calc
    _ ≤ ∑ _q ∈ Ioc 0 Q, (Real.log Q + 2 * Real.sqrt T * Real.log T) := by
      apply sum_le_sum
      intro q hq
      obtain ⟨hq0, hqQ⟩ := mem_Ioc.mp hq
      exact (noncoprimeMangoldtMass_le_uniform T q hT hq0 (ht q hq)).trans
        (add_le_add (Real.log_le_log (x := (q : ℝ)) (y := (Q : ℝ))
          (by exact_mod_cast hq0)
          (by exact_mod_cast hqQ)) le_rfl)
    _ = _ := by simp; ring

/-- Passing to the inducing primitive character costs only the excluded mass.-/
theorem norm_characterPsi_sub_primitive_le {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t : ℕ) :
    ‖characterPsi t χ - characterPsi t χ.primitiveCharacter‖ ≤
      noncoprimeMangoldtMass t q := by
  unfold characterPsi noncoprimeMangoldtMass
  rw [← sum_sub_distrib, sum_filter]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro n _
  by_cases hn : Nat.Coprime n q
  · have heq : χ.primitiveCharacter (n : ZMod χ.conductor) = χ (n : ZMod q) := by
      simpa only [Int.cast_natCast] using
        χ.primitiveCharacter_apply_of_isCoprime hn.isCoprime
    simp [heq, hn]
  · have hχ : χ (n : ZMod q) = 0 :=
      MulChar.map_nonunit χ (fun h => hn ((ZMod.isUnit_iff_coprime n q).mp h))
    simp only [hn, not_false_eq_true, ite_true, hχ, mul_zero, zero_sub, norm_neg,
      norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
    exact mul_le_of_le_one_right vonMangoldt_nonneg (χ.primitiveCharacter.norm_le_one _)

end TwinPrime.Analytic
