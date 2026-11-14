import Tengoku.Piirrationalitymeasure.Formalization.HataBounds
import Tengoku.Piirrationalitymeasure.Formalization.Statements

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Assembly of the two index-selection branches of Lemma 5.1. -/

namespace PiIrrationality

open Filter
open scoped Topology

/--
@isnad1 id=ne.2h3v.s4.473f06694e25 from=translated src=- shape=badd0dda vocab=fab9f5b5
-/
theorem hataDelta_ne_zero {theta : ℝ} (hθ : Irrational theta) (p : ℤ) (q : ℕ)
    (hq : 0 < q) : hataDelta theta p q ≠ 0 := by
  rw [hata_delta_factorization theta p q hq]
  apply mul_ne_zero (by exact_mod_cast hq.ne')
  apply sub_ne_zero.mpr
  simpa only [Int.cast_natCast] using hθ.ne_rational p (q : ℤ)

/--
@isnad1 id=ex.8h6v.s8.5dfcef059785 from=translated src=- shape=d40adc40 vocab=17c7c884
-/
theorem hata_uniform_bound_of_exp_bounds {theta a b d : ℝ} {U V : ℕ → ℤ}
    (hθ : Irrational theta) (ha : 0 < a) (hb : 0 < b) (hbd : b ≤ d)
    (hgap : d < b + a)
    (hVlower : ∀ᶠ n : ℕ in atTop, Real.exp (b * (n : ℝ)) ≤ |(V n : ℝ)|)
    (hVupper : ∀ᶠ n : ℕ in atTop, |(V n : ℝ)| ≤ Real.exp (d * (n : ℝ)))
    (hLupper : ∀ᶠ n : ℕ in atTop,
      |linearForm theta (U n) (V n)| ≤ Real.exp (-a * (n : ℝ))) :
    ∃ c : ℝ, 0 < c ∧ ∃ q0 : ℕ, ∀ p : ℤ, ∀ q : ℕ, q0 ≤ q → 0 < q →
      |theta - (p : ℝ) / (q : ℝ)| > c * (q : ℝ) ^ (-1 - d / (b + a - d)) := by
  let c1 : ℝ := (1 : ℝ) / 2 * Real.exp (-d) * (2 : ℝ) ^ (-d / a)
  let c2 : ℝ := (2 * Real.exp d) ^ (-(b + a) / (b + a - d))
  have hc1 : 0 < c1 := by dsimp [c1]; positivity
  have hc2 : 0 < c2 := by dsimp [c2]; positivity
  have hd : 0 ≤ d := hb.le.trans hbd
  have hgap0 : 0 < b + a - d := by linarith
  have hk : d / a ≤ d / (b + a - d) := by
    apply (div_le_div_iff₀ ha hgap0).mpr
    nlinarith
  obtain ⟨n0, hn0⟩ := eventually_atTop.mp ((hVlower.and hVupper).and hLupper)
  obtain ⟨q0, hq0⟩ := exists_nat_gt (Real.exp (a * ((n0 - 1 : ℕ) : ℝ)))
  refine ⟨min c1 c2, lt_min hc1 hc2, q0, ?_⟩
  intro p q hqge hq
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqgeR : (q0 : ℝ) ≤ q := by exact_mod_cast hqge
  have hN : n0 ≤ hataScale q a ha :=
    hataScale_ge_of_threshold q n0 ha (by linarith)
  have hVne : ∀ n : ℕ, n0 ≤ n → V n ≠ 0 := by
    intro n hn hz
    have hv := (hn0 n hn).1.1
    simp only [hz, Int.cast_zero, abs_zero] at hv
    exact (not_le_of_gt (Real.exp_pos _)) hv
  have hsmall : ∀ n : ℕ, hataScale q a ha ≤ n →
      |(q : ℝ) * linearForm theta (U n) (V n)| < (1 : ℝ) / 2 := by
    intro n hn
    exact hata_scale_linear_form_small theta (U n) (V n) q n a ha hn
      (hn0 n (hN.trans hn)).2
  have hD : |hataDelta theta p q| > min c1 c2 * (q : ℝ) ^ (-d / (b + a - d)) := by
    by_cases hA : hataInteger (U (hataScale q a ha)) (V (hataScale q a ha)) p q ≠ 0
    · have hfirst := hata_nonzero_q_power_bound theta (U (hataScale q a ha))
        (V (hataScale q a ha)) p q a d ha hd (hVne _ hN) hq hA
        (hsmall _ le_rfl) (hn0 _ hN).1.2
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hqR.le] at hfirst
      have hfirst' : c1 * (q : ℝ) ^ (-(d / a)) < |hataDelta theta p q| := by
        dsimp [c1]
        convert hfirst using 1 <;> ring
      have hpow : (q : ℝ) ^ (-(d / (b + a - d))) ≤ (q : ℝ) ^ (-(d / a)) :=
        Real.rpow_le_rpow_of_exponent_le hq1 (neg_le_neg hk)
      calc
        min c1 c2 * (q : ℝ) ^ (-d / (b + a - d)) =
            min c1 c2 * (q : ℝ) ^ (-(d / (b + a - d))) := by rw [neg_div]
        _ ≤ c1 * (q : ℝ) ^ (-(d / (b + a - d))) :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.rpow_nonneg hqR.le _)
        _ ≤ c1 * (q : ℝ) ^ (-(d / a)) := mul_le_mul_of_nonneg_left hpow hc1.le
        _ < _ := hfirst'
    · obtain ⟨m, hm, hmA, hmP⟩ := hata_exists_first_nonzero_after hb ha
        hVlower hLupper (hataDelta_ne_zero hθ p q hq) (not_ne_iff.mp hA)
      have hm0 : n0 ≤ m := hN.trans hm.le
      have hp0 : n0 ≤ m - 1 := by omega
      have hm1 : 1 ≤ m := by omega
      have hz := hata_zero_index_upper_bound hmP (hn0 _ hp0).1.1 (hn0 _ hp0).2
      rw [Nat.cast_sub hm1, Nat.cast_one] at hz
      have hDpos := abs_pos.mpr (hataDelta_ne_zero hθ p q hq)
      have he := hata_zero_predecessor_exp_bound hqR hDpos (add_pos hb ha) hz
      have hn := hata_nonzero_index_bound theta (U m) (V m) p q d (m : ℝ)
        (hVne m hm0) hq hmA (hsmall m hm.le) (hn0 m hm0).1.2
      have hi := hata_second_branch_intermediate hDpos hqR hd he hn
      have hp := hata_second_branch_power_bound hDpos hqR hd hgap hi
      calc
        min c1 c2 * (q : ℝ) ^ (-d / (b + a - d)) ≤
            c2 * (q : ℝ) ^ (-d / (b + a - d)) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.rpow_nonneg hqR.le _)
        _ < _ := hp
  have he : (q : ℝ) * (min c1 c2 * (q : ℝ) ^ (-1 - d / (b + a - d))) =
      min c1 c2 * (q : ℝ) ^ (-d / (b + a - d)) := by
    calc
      _ = min c1 c2 * ((q : ℝ) ^ (1 : ℝ) *
          (q : ℝ) ^ (-1 - d / (b + a - d))) := by rw [Real.rpow_one]; ring
      _ = _ := by rw [← Real.rpow_add hqR]; congr 2 <;> ring
  rw [hata_delta_abs_factorization theta p q hq, ← he] at hD
  exact (mul_lt_mul_iff_right₀ hqR).mp hD

end PiIrrationality
