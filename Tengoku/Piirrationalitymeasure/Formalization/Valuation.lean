import Tengoku
import Tengoku.Piirrationalitymeasure.Formalization.Denominator

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Exact elementary valuation identities used by the denominator argument.
-/

namespace PiIrrationality

theorem padic_two_pow (k : ℕ) : padicValNat 2 (2 ^ k) = k := by
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  simpa using (padicValNat.prime_pow k : padicValNat 2 (2 ^ k) = k)

theorem padic_five_pow (k : ℕ) : padicValNat 5 (5 ^ k) = k := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  simpa using (padicValNat.prime_pow k : padicValNat 5 (5 ^ k) = k)

theorem padic_two_ten_pow (k : ℕ) : padicValNat 2 (10 ^ k) = k := by
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  rw [show (10 : ℕ) = 2 * 5 by norm_num, mul_pow]
  rw [padicValNat.mul]
  · simp [padic_two_pow]
  · positivity
  · positivity

theorem padic_five_ten_pow (k : ℕ) : padicValNat 5 (10 ^ k) = k := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [show (10 : ℕ) = 2 * 5 by norm_num, mul_pow]
  rw [padicValNat.mul]
  · simp [padic_five_pow]
  · positivity
  · positivity

theorem powers_nonzero (p k : ℕ) (hp : p ≠ 0) : p ^ k ≠ 0 := by
  exact pow_ne_zero k hp

theorem padicValNat_eq_one_of_prime_dvd_of_sq_gt
    {p j D : ℕ} [Fact p.Prime]
    (hpj : p ∣ j) (hj0 : j ≠ 0) (hjD : j ≤ D) (hDsquare : D < p ^ 2) :
    padicValNat p j = 1 := by
  have hone : 1 ≤ padicValNat p j :=
    one_le_padicValNat_of_dvd hj0 hpj
  have hlt : padicValNat p j < 2 := by
    by_contra h
    have htwo : 2 ≤ padicValNat p j := by omega
    have hp2dvd : p ^ 2 ∣ j :=
      (padicValNat_dvd_iff_le hj0).2 htwo
    have hp2le : p ^ 2 ≤ j :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero hj0) hp2dvd
    omega
  exact le_antisymm (Nat.le_of_lt_succ hlt) hone

theorem padicValRat_two_pow (k : ℕ) :
    padicValRat 2 ((2 : ℚ) ^ k) = k := by
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  rw [padicValRat.pow]
  have h22 : padicValRat 2 (2 : ℚ) = 1 := by
    norm_num [padicValRat, padicValInt]
  rw [h22]
  simp

theorem padicValRat_five_pow (k : ℕ) :
    padicValRat 5 ((5 : ℚ) ^ k) = k := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [padicValRat.pow]
  have h55 : padicValRat 5 (5 : ℚ) = 1 := by
    norm_num [padicValRat, padicValInt]
  rw [h55]
  simp

theorem padicValRat_ten_pow (k : ℕ) :
    padicValRat 2 ((10 : ℚ) ^ k) = k := by
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  rw [show (10 : ℚ) = 2 * 5 by norm_num, mul_pow, padicValRat.mul]
  · rw [padicValRat.pow, padicValRat.pow]
    have h22 : padicValRat 2 (2 : ℚ) = 1 := by
      norm_num [padicValRat, padicValInt]
    have h25 : padicValRat 2 (5 : ℚ) = 0 := by
      norm_num [padicValRat, padicValInt]
    rw [h22, h25]
    norm_num
  · norm_num
  · norm_num

theorem padicValRat_ten_pow_five (k : ℕ) :
    padicValRat 5 ((10 : ℚ) ^ k) = k := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [show (10 : ℚ) = 2 * 5 by norm_num, mul_pow, padicValRat.mul]
  · rw [padicValRat.pow, padicValRat.pow]
    have h52 : padicValRat 5 (2 : ℚ) = 0 := by
      norm_num [padicValRat, padicValInt]
    have h55 : padicValRat 5 (5 : ℚ) = 1 := by
      norm_num [padicValRat, padicValInt]
    rw [h52, h55]
    norm_num
  · norm_num
  · norm_num

theorem padicValRat_ten_neg_pow (k : ℕ) :
    padicValRat 2 ((10 : ℚ) ^ (-(k : ℤ))) = -(k : ℤ) := by
  rw [zpow_neg, zpow_natCast]
  rw [padicValRat.inv]
  rw [padicValRat_ten_pow]

theorem padicValRat_ten_neg_pow_five (k : ℕ) :
    padicValRat 5 ((10 : ℚ) ^ (-(k : ℤ))) = -(k : ℤ) := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [zpow_neg, zpow_natCast]
  rw [padicValRat.inv]
  rw [padicValRat_ten_pow_five]

noncomputable def padicValRatTop (p : ℕ) (q : ℚ) : WithTop ℤ :=
  if q = 0 then ⊤ else (padicValRat p q : WithTop ℤ)

theorem padicValRatTop_add {p : ℕ} [Fact p.Prime] {q r : ℚ} {K : ℤ}
    (hq : (K : WithTop ℤ) ≤ padicValRatTop p q)
    (hr : (K : WithTop ℤ) ≤ padicValRatTop p r) :
    (K : WithTop ℤ) ≤ padicValRatTop p (q + r) := by
  by_cases hqr : q + r = 0
  · simp [padicValRatTop, hqr]
  by_cases hq0 : q = 0
  · simp [padicValRatTop, hq0] at hq
    simpa [padicValRatTop, hq0, hqr] using hr
  by_cases hr0 : r = 0
  · simp [padicValRatTop, hr0] at hr
    simpa [padicValRatTop, hr0, hqr] using hq
  have hq' : K ≤ padicValRat p q := by
    simpa [padicValRatTop, hq0] using hq
  have hr' : K ≤ padicValRat p r := by
    simpa [padicValRatTop, hr0] using hr
  have hadd : min (padicValRat p q) (padicValRat p r) ≤
      padicValRat p (q + r) := padicValRat.min_le_padicValRat_add hqr
  have hmin : K ≤ min (padicValRat p q) (padicValRat p r) := le_min hq' hr'
  have htotal : K ≤ padicValRat p (q + r) := hmin.trans hadd
  simpa [padicValRatTop, hq0, hr0, hqr] using htotal

theorem padicValRatTop_list_sum_ge {p : ℕ} [Fact p.Prime]
    (K : ℤ) (l : List ℚ)
    (h : ∀ q ∈ l, (K : WithTop ℤ) ≤ padicValRatTop p q) :
    (K : WithTop ℤ) ≤ padicValRatTop p l.sum := by
  induction l with
  | nil => simp [padicValRatTop]
  | cons a l ih =>
      rw [List.sum_cons]
      apply padicValRatTop_add
      · exact h a (by simp)
      · apply ih
        intro q hq
        exact h q (by simp [hq])

end PiIrrationality
