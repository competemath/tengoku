import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A finite dyadic maximal inequality

The energy of the binary interval tree records the squared norm of every
dyadic block. A prefix uses at most one block per depth. This yields a
logarithmic pointwise loss and a squared logarithmic loss when a fixed
interval second-moment bound is available uniformly over the tree.
-/

noncomputable section

open Finset

namespace TwinPrime.Analytic

/-- Squared block sums over the complete binary tree on `[M,M+2^k)`.-/
def dyadicEnergy (f : ℕ → ℂ) (M : ℕ) : ℕ → ℝ
  | 0 => ‖f M‖ ^ 2
  | k + 1 => ‖∑ n ∈ Ico M (M + 2 ^ (k + 1)), f n‖ ^ 2 +
      dyadicEnergy f M k + dyadicEnergy f (M + 2 ^ k) k

/--
@isnad1 id=le.0h3v.s4.09732f5a5067 from=translated src=- shape=def86511 vocab=189ca5fe
-/
theorem dyadicEnergy_nonneg (f : ℕ → ℂ) (M k : ℕ) : 0 ≤ dyadicEnergy f M k := by
  induction k generalizing M with
  | zero => exact sq_nonneg _
  | succ k ih =>
      rw [dyadicEnergy]
      exact add_nonneg (add_nonneg (sq_nonneg _) (ih M)) (ih _)

/--
@isnad1 id=le.0h3v.s6.720b356408a3 from=translated src=- shape=ab446430 vocab=4aefa2b8
-/
theorem norm_dyadicBlock_sq_le_energy (f : ℕ → ℂ) (M k : ℕ) :
    ‖∑ n ∈ Ico M (M + 2 ^ k), f n‖ ^ 2 ≤ dyadicEnergy f M k := by
  cases k with
  | zero => simp [dyadicEnergy]
  | succ k =>
      rw [dyadicEnergy]
      linarith [dyadicEnergy_nonneg f M k, dyadicEnergy_nonneg f (M + 2 ^ k) k]

private theorem add_sq_le_of_sq_le (a b c d : ℝ) (hc : 0 < c) (h : a ^ 2 ≤ c * d) :
    (a + b) ^ 2 ≤ (c + 1) * (b ^ 2 + d) := by
  have hquad : c * (a + b) ^ 2 ≤ (c + 1) * (c * b ^ 2 + a ^ 2) := by
    nlinarith [sq_nonneg (c * b - a)]
  calc
    _ ≤ (c + 1) * (b ^ 2 + a ^ 2 / c) := by
      apply (mul_le_mul_iff_left₀ hc).mp
      have heq : ((c + 1) * (b ^ 2 + a ^ 2 / c)) * c =
          (c + 1) * (c * b ^ 2 + a ^ 2) := by field_simp
      rw [heq]
      simpa only [mul_comm] using hquad
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add le_rfl ((div_le_iff₀ hc).mpr (by simpa only [mul_comm] using h))) (by linarith)

/-- Every prefix of a dyadic interval has its squared norm controlled by
the complete tree energy, with one factor for the number of depths.
@isnad1 id=le.2h4v.s6.a57c00ffabff from=translated src=- shape=179803f3 vocab=149352a6
-/
theorem norm_prefix_sq_le_dyadicEnergy (f : ℕ → ℂ) (M k t : ℕ)
    (hMt : M ≤ t) (ht : t ≤ M + 2 ^ k) :
    ‖∑ n ∈ Ico M t, f n‖ ^ 2 ≤ ((k : ℝ) + 1) * dyadicEnergy f M k := by
  induction k generalizing M t with
  | zero =>
      have ht' : t = M ∨ t = M + 1 := by norm_num at ht; omega
      rcases ht' with rfl | rfl <;> simp [dyadicEnergy]
  | succ k ih =>
      have hpow : (2 : ℕ) ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; omega
      have hroot : 0 ≤ ‖∑ n ∈ Ico M (M + 2 ^ (k + 1)), f n‖ ^ 2 := sq_nonneg _
      have hleft := dyadicEnergy_nonneg f M k
      have hright := dyadicEnergy_nonneg f (M + 2 ^ k) k
      by_cases htleft : t ≤ M + 2 ^ k
      · apply (ih M t hMt htleft).trans
        have henergy : dyadicEnergy f M k ≤ dyadicEnergy f M (k + 1) := by
          rw [dyadicEnergy]
          linarith
        calc
          _ ≤ ((k : ℝ) + 1) * dyadicEnergy f M (k + 1) :=
            mul_le_mul_of_nonneg_left henergy (by positivity)
          _ ≤ _ := mul_le_mul_of_nonneg_right (by push_cast; linarith)
            (dyadicEnergy_nonneg f M (k + 1))
      · have htmid : M + 2 ^ k ≤ t := by omega
        have htend : t ≤ (M + 2 ^ k) + 2 ^ k := by omega
        have hir := ih (M + 2 ^ k) t htmid htend
        have hsplit := sum_Ico_consecutive f (Nat.le_add_right M (2 ^ k)) htmid
        rw [← hsplit]
        have hnorm := norm_add_le (∑ n ∈ Ico M (M + 2 ^ k), f n)
          (∑ n ∈ Ico (M + 2 ^ k) t, f n)
        calc
          _ ≤ (‖∑ n ∈ Ico (M + 2 ^ k) t, f n‖ +
              ‖∑ n ∈ Ico M (M + 2 ^ k), f n‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (by simpa only [add_comm] using hnorm) 2
          _ ≤ (((k : ℝ) + 1) + 1) *
              (‖∑ n ∈ Ico M (M + 2 ^ k), f n‖ ^ 2 + dyadicEnergy f (M + 2 ^ k) k) :=
            add_sq_le_of_sq_le _ _ _ _ (by positivity) hir
          _ ≤ _ := by
            have hl := norm_dyadicBlock_sq_le_energy f M k
            have he : ‖∑ n ∈ Ico M (M + 2 ^ k), f n‖ ^ 2 + dyadicEnergy f (M + 2 ^ k) k ≤
                dyadicEnergy f M (k + 1) := by
              rw [dyadicEnergy]
              linarith
            simpa only [Nat.cast_add, Nat.cast_one] using
              mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ ((k : ℝ) + 1) + 1)

/-- Fixed-interval second moments control the entire dyadic tree with one
factor for its depth. The bound is uniform in the interval's starting point.
@isnad1 id=le.2h8v.s8.d0f3b86636ae from=translated src=- shape=19db6b31 vocab=b6df14da
-/
theorem sum_weighted_dyadicEnergy_le {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (f : ι → ℕ → ℂ) (e : ℕ → ℝ) (A : ℝ)
    (he : ∀ n, 0 ≤ e n)
    (hLS : ∀ u v : ℕ, (∑ i ∈ s, w i * ‖∑ n ∈ Ico u v, f i n‖ ^ 2) ≤
      (((v - u : ℕ) : ℝ) + A) * ∑ n ∈ Ico u v, e n) (M k : ℕ) :
    (∑ i ∈ s, w i * dyadicEnergy (f i) M k) ≤
      ((k : ℝ) + 1) * ((2 : ℝ) ^ k + A) * ∑ n ∈ Ico M (M + 2 ^ k), e n := by
  induction k generalizing M with
  | zero => simpa [dyadicEnergy] using hLS M (M + 1)
  | succ k ih =>
      have hpow : (2 : ℕ) ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; omega
      have hwhole := hLS M (M + 2 ^ (k + 1))
      simp only [Nat.add_sub_cancel_left, Nat.cast_pow, Nat.cast_ofNat] at hwhole
      have hleft := ih M
      have hright := ih (M + 2 ^ k)
      have hend : (M + 2 ^ k) + 2 ^ k = M + 2 ^ (k + 1) := by omega
      rw [hend] at hright
      have hhalf : (2 : ℕ) ^ k ≤ 2 ^ (k + 1) := by
        rw [hpow]
        exact Nat.le_add_right _ _
      have hsplit := sum_Ico_consecutive e (Nat.le_add_right M (2 ^ k))
        (Nat.add_le_add_left hhalf M)
      have hE : 0 ≤ ∑ n ∈ Ico M (M + 2 ^ (k + 1)), e n :=
        sum_nonneg fun n _ => he n
      calc
        _ = (∑ i ∈ s, w i * ‖∑ n ∈ Ico M (M + 2 ^ (k + 1)), f i n‖ ^ 2) +
            (∑ i ∈ s, w i * dyadicEnergy (f i) M k) +
              ∑ i ∈ s, w i * dyadicEnergy (f i) (M + 2 ^ k) k := by
          simp only [dyadicEnergy, mul_add, sum_add_distrib]
        _ ≤ ((2 : ℝ) ^ (k + 1) + A) * (∑ n ∈ Ico M (M + 2 ^ (k + 1)), e n) +
            ((k : ℝ) + 1) * ((2 : ℝ) ^ k + A) *
              ((∑ n ∈ Ico M (M + 2 ^ k), e n) +
                ∑ n ∈ Ico (M + 2 ^ k) (M + 2 ^ (k + 1)), e n) := by
          convert add_le_add (add_le_add hwhole hleft) hright using 1 <;> first | rfl | ring
        _ = (((2 : ℝ) ^ (k + 1) + A) + ((k : ℝ) + 1) * ((2 : ℝ) ^ k + A)) *
            ∑ n ∈ Ico M (M + 2 ^ (k + 1)), e n := by rw [hsplit]; ring
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ hE
          push_cast
          rw [pow_succ]
          nlinarith [mul_nonneg (show 0 ≤ (k : ℝ) + 1 by positivity)
            (show 0 ≤ (2 : ℝ) ^ k by positivity)]

/-- Independently selected prefix endpoints for every member of a finite
family cost only the square of the dyadic depth in a second moment.
@isnad1 id=le.4h9v.s8.556d75a18b6e from=translated src=- shape=942b1197 vocab=f6aadc7a
-/
theorem sum_weighted_prefix_sq_le {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) (f : ι → ℕ → ℂ)
    (e : ℕ → ℝ) (A : ℝ) (he : ∀ n, 0 ≤ e n)
    (hLS : ∀ u v : ℕ, (∑ i ∈ s, w i * ‖∑ n ∈ Ico u v, f i n‖ ^ 2) ≤
      (((v - u : ℕ) : ℝ) + A) * ∑ n ∈ Ico u v, e n)
    (M k : ℕ) (t : ι → ℕ) (ht : ∀ i ∈ s, M ≤ t i ∧ t i ≤ M + 2 ^ k) :
    (∑ i ∈ s, w i * ‖∑ n ∈ Ico M (t i), f i n‖ ^ 2) ≤
      ((k : ℝ) + 1) ^ 2 * ((2 : ℝ) ^ k + A) *
        ∑ n ∈ Ico M (M + 2 ^ k), e n := by
  calc
    _ ≤ ∑ i ∈ s, w i * (((k : ℝ) + 1) * dyadicEnergy (f i) M k) :=
      sum_le_sum fun i hi => mul_le_mul_of_nonneg_left
        (norm_prefix_sq_le_dyadicEnergy (f i) M k (t i) (ht i hi).1 (ht i hi).2) (hw i hi)
    _ = ((k : ℝ) + 1) * ∑ i ∈ s, w i * dyadicEnergy (f i) M k := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i _
      ring
    _ ≤ ((k : ℝ) + 1) * (((k : ℝ) + 1) * ((2 : ℝ) ^ k + A) *
        ∑ n ∈ Ico M (M + 2 ^ k), e n) :=
      mul_le_mul_of_nonneg_left (sum_weighted_dyadicEnergy_le s w f e A he hLS M k) (by positivity)
    _ = _ := by ring

end TwinPrime.Analytic
