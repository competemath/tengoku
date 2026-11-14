import Tengoku.Twinprime.TwinPrime.Analytic.IntervalFamilyLargeSieve
import Tengoku.Twinprime.TwinPrime.Analytic.DyadicStaircaseGeometry
import Tengoku.Twinprime.TwinPrime.Analytic.DyadicStaircaseLevels
import Tengoku.Twinprime.TwinPrime.Analytic.WeightedBilinear

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A first moment for independently chosen staircase boundaries

The two fixed-interval large sieves imply a bilinear first moment for every
choice of antitone boundary in each member of the weighted family. The
loss is twice the product of the two dyadic depths plus one.
-/

noncomputable section

open Finset Classical

namespace TwinPrime.Analytic

/--
@isnad1 id=le.8h13v.s9.603893f03b6b from=translated src=- shape=f4ab70b9 vocab=b3151c7e
-/
theorem sum_weighted_dyadic_staircase_le {ι : Type*}
    (s : Finset ι) (w : ι → ℝ) (hw : ∀ x ∈ s, 0 ≤ w x)
    (a b : ι → ℕ → ℂ) (ea eb : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hea : ∀ n, 0 ≤ ea n) (heb : ∀ n, 0 ≤ eb n)
    (hLSa : ∀ u v : ℕ, (∑ x ∈ s, w x * ‖∑ n ∈ Ico u v, a x n‖ ^ 2) ≤
      (((v - u : ℕ) : ℝ) + C) * ∑ n ∈ Ico u v, ea n)
    (hLSb : ∀ u v : ℕ, (∑ x ∈ s, w x * ‖∑ n ∈ Ico u v, b x n‖ ^ 2) ≤
      (((v - u : ℕ) : ℝ) + C) * ∑ n ∈ Ico u v, eb n)
    (M N k j : ℕ) (F : ι → ℕ → ℕ)
    (hF : ∀ x ∈ s, AntitoneOn (F x) (Set.Ico M (M + 2 ^ k)))
    (hbound : ∀ x ∈ s, ∀ m ∈ Ico M (M + 2 ^ k),
      N ≤ F x m ∧ F x m ≤ N + 2 ^ j) :
    (∑ x ∈ s, w x *
      ‖∑ m ∈ Ico M (M + 2 ^ k), a x m * (∑ n ∈ Ico N (F x m), b x n)‖) ≤
      (2 * ((k : ℝ) + 1) * ((j : ℝ) + 1)) *
        Real.sqrt (((2 : ℝ) ^ k + C) * ∑ m ∈ Ico M (M + 2 ^ k), ea m) *
          Real.sqrt (((2 : ℝ) ^ j + C) * ∑ n ∈ Ico N (N + 2 ^ j), eb n) := by
  let EA := ((2 : ℝ) ^ k + C) * ∑ m ∈ Ico M (M + 2 ^ k), ea m
  let EB := ((2 : ℝ) ^ j + C) * ∑ n ∈ Ico N (N + 2 ^ j), eb n
  have hEA : 0 ≤ EA := mul_nonneg (by positivity) (sum_nonneg fun n _ => hea n)
  have hEB : 0 ≤ EB := mul_nonneg (by positivity) (sum_nonneg fun n _ => heb n)
  have hlast : M + 2 ^ k - 1 ∈ Ico M (M + 2 ^ k) := by
    have hp : 0 < (2 : ℕ) ^ k := by positivity
    exact mem_Ico.mpr ⟨by omega, by omega⟩
  have hA0 : (∑ x ∈ s, w x * ‖∑ m ∈ Ico M (M + 2 ^ k), a x m‖ ^ 2) ≤ EA := by
    simpa only [EA, Nat.add_sub_cancel_left, Nat.cast_pow, Nat.cast_ofNat] using hLSa M (M + 2 ^ k)
  have hB0 : (∑ x ∈ s, w x *
      ‖∑ n ∈ Ico N (F x (M + 2 ^ k - 1)), b x n‖ ^ 2) ≤ ((j : ℝ) + 1) ^ 2 * EB := by
    simpa only [EB, mul_assoc] using sum_weighted_prefix_sq_le s w hw b eb C heb hLSb
      N j (fun x => F x (M + 2 ^ k - 1)) (fun x hx => hbound x hx _ hlast)
  have hbase : (∑ x ∈ s, w x *
      (‖∑ m ∈ Ico M (M + 2 ^ k), a x m‖ *
        ‖∑ n ∈ Ico N (F x (M + 2 ^ k - 1)), b x n‖)) ≤
      Real.sqrt EA * Real.sqrt (((j : ℝ) + 1) ^ 2 * EB) := by
    have h := weighted_sum_mul_le_sqrt_mul_sqrt s w
      (fun x => ‖∑ m ∈ Ico M (M + 2 ^ k), a x m‖)
      (fun x => ‖∑ n ∈ Ico N (F x (M + 2 ^ k - 1)), b x n‖) hw
    have h' := h.trans (mul_le_mul (Real.sqrt_le_sqrt hA0) (Real.sqrt_le_sqrt hB0)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    simpa only [mul_assoc] using h'
  have hlevel (ℓ : ℕ) : (∑ x ∈ s, w x *
      ∑ p ∈ dyadicStaircaseLevel M k ℓ,
        ‖∑ m ∈ Ico p.1 (p.1 + 2 ^ (p.2 - 1)), a x m‖ *
          ‖∑ n ∈ Ico (F x (p.1 + 2 ^ p.2 - 1))
            (F x (p.1 + 2 ^ (p.2 - 1) - 1)), b x n‖) ≤
      Real.sqrt EA * Real.sqrt ((2 * ((j : ℝ) + 1) ^ 2) * EB) := by
    have hA := sum_weighted_fixed_disjoint_intervals_sq_le s (dyadicStaircaseLevel M k ℓ)
      (fun p => p.1) (fun p => p.1 + 2 ^ (p.2 - 1)) w a ea C hea hC hLSa
      M (M + 2 ^ k) (dyadicStaircaseLevel_left_valid M k ℓ)
      (dyadicStaircaseLevel_left_disjoint M k ℓ)
    have hB := sum_weighted_disjoint_intervals_sq_le s (fun _ => dyadicStaircaseLevel M k ℓ)
      (fun x p => F x (p.1 + 2 ^ p.2 - 1))
      (fun x p => F x (p.1 + 2 ^ (p.2 - 1) - 1)) w hw b eb C heb hLSb N j
      (fun x hx => dyadicStaircaseLevel_correction_valid M k ℓ N j (F x)
        (hF x hx) (hbound x hx))
      (fun x hx => dyadicStaircaseLevel_correction_disjoint M k ℓ (F x) (hF x hx))
    have h := weighted_sum_sum_norm_mul_le s (fun _ => dyadicStaircaseLevel M k ℓ) w
      (fun x p => ∑ m ∈ Ico p.1 (p.1 + 2 ^ (p.2 - 1)), a x m)
      (fun x p => ∑ n ∈ Ico (F x (p.1 + 2 ^ p.2 - 1))
        (F x (p.1 + 2 ^ (p.2 - 1) - 1)), b x n) hw EA
      ((2 * ((j : ℝ) + 1) ^ 2) * EB)
      (by simpa only [EA, Nat.add_sub_cancel_left, Nat.cast_pow, Nat.cast_ofNat] using hA)
      (by simpa only [EB, mul_assoc] using hB)
    simpa only [norm_mul] using h
  calc
    _ ≤ ∑ x ∈ s, w x *
        (‖∑ m ∈ Ico M (M + 2 ^ k), a x m‖ *
          ‖∑ n ∈ Ico N (F x (M + 2 ^ k - 1)), b x n‖ +
          ∑ ℓ ∈ range k, ∑ p ∈ dyadicStaircaseLevel M k ℓ,
            ‖∑ m ∈ Ico p.1 (p.1 + 2 ^ (p.2 - 1)), a x m‖ *
              ‖∑ n ∈ Ico (F x (p.1 + 2 ^ p.2 - 1))
                (F x (p.1 + 2 ^ (p.2 - 1) - 1)), b x n‖) := by
      apply sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_left
        (norm_sum_dyadic_staircase_le_levels (a x) (b x) (F x) M N k
          (fun m hm => (hbound x hx m hm).1) (hF x hx)) (hw x hx)
    _ = (∑ x ∈ s, w x *
        (‖∑ m ∈ Ico M (M + 2 ^ k), a x m‖ *
          ‖∑ n ∈ Ico N (F x (M + 2 ^ k - 1)), b x n‖)) +
        ∑ ℓ ∈ range k, ∑ x ∈ s, w x * ∑ p ∈ dyadicStaircaseLevel M k ℓ,
          ‖∑ m ∈ Ico p.1 (p.1 + 2 ^ (p.2 - 1)), a x m‖ *
            ‖∑ n ∈ Ico (F x (p.1 + 2 ^ p.2 - 1))
              (F x (p.1 + 2 ^ (p.2 - 1) - 1)), b x n‖ := by
      simp only [mul_add, sum_add_distrib, mul_sum]
      rw [sum_comm (s := s) (t := range k)]
    _ ≤ Real.sqrt EA * Real.sqrt (((j : ℝ) + 1) ^ 2 * EB) +
        (k : ℝ) * (Real.sqrt EA * Real.sqrt ((2 * ((j : ℝ) + 1) ^ 2) * EB)) := by
      have hl := sum_le_sum (s := range k) (fun ℓ _ => hlevel ℓ)
      simp only [sum_const, card_range, nsmul_eq_mul] at hl
      exact add_le_add hbase hl
    _ ≤ _ := sqrt_baseline_add_levels_le EA EB hEA hEB k j

end TwinPrime.Analytic
