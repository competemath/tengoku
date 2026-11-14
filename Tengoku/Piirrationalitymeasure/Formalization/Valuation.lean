import Tengoku
import Tengoku.Piirrationalitymeasure.Formalization.Denominator

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Exact elementary valuation identities used by the denominator argument.
-/

namespace PiIrrationality

/--
@isnad1 id=eq.0h1v.s4.56e2bd9f8844 from=translated src=- shape=483a9353 vocab=8cf9237d
-/
theorem padic_two_pow (k : ℕ) : padicValNat 2 (2 ^ k) = k := by
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  simpa using (padicValNat.prime_pow k : padicValNat 2 (2 ^ k) = k)

/--
@isnad1 id=eq.0h1v.s4.6abe3a64656e from=translated src=- shape=483a9353 vocab=8cf9237d
-/
theorem padic_five_pow (k : ℕ) : padicValNat 5 (5 ^ k) = k := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  simpa using (padicValNat.prime_pow k : padicValNat 5 (5 ^ k) = k)

/--
@isnad1 id=eq.0h1v.s4.7b68ae490094 from=translated src=- shape=483a9353 vocab=8cf9237d
-/
theorem padic_two_ten_pow (k : ℕ) : padicValNat 2 (10 ^ k) = k := by
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  rw [show (10 : ℕ) = 2 * 5 by norm_num, mul_pow]
  rw [padicValNat.mul]
  · simp [padic_two_pow]
  · positivity
  · positivity

/--
@isnad1 id=eq.0h1v.s4.2d6d874e99e5 from=translated src=- shape=483a9353 vocab=8cf9237d
-/
theorem padic_five_ten_pow (k : ℕ) : padicValNat 5 (10 ^ k) = k := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [show (10 : ℕ) = 2 * 5 by norm_num, mul_pow]
  rw [padicValNat.mul]
  · simp [padic_five_pow]
  · positivity
  · positivity

/--
@isnad1 id=ne.1h2v.s5.8f99d8b93eb8 from=translated src=- shape=e4f3c5c0 vocab=4e91a72a
-/
theorem powers_nonzero (p k : ℕ) (hp : p ≠ 0) : p ^ k ≠ 0 := by
  exact pow_ne_zero k hp

/--
@isnad1 id=eq.4h3v.s6.935cb29cf209 from=translated src=- shape=fb66b823 vocab=18f50b17
-/
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

/--
@isnad1 id=eq.0h1v.s4.0abab871dc77 from=translated src=- shape=4181b9f5 vocab=4c541edf
-/
theorem padicValRat_two_pow (k : ℕ) :
    padicValRat 2 ((2 : ℚ) ^ k) = k := by
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  rw [padicValRat.pow]
  have h22 : padicValRat 2 (2 : ℚ) = 1 := by
    norm_num [padicValRat, padicValInt]
  rw [h22]
  simp

/--
@isnad1 id=eq.0h1v.s4.6a727c23e862 from=translated src=- shape=4181b9f5 vocab=4c541edf
-/
theorem padicValRat_five_pow (k : ℕ) :
    padicValRat 5 ((5 : ℚ) ^ k) = k := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [padicValRat.pow]
  have h55 : padicValRat 5 (5 : ℚ) = 1 := by
    norm_num [padicValRat, padicValInt]
  rw [h55]
  simp

/--
@isnad1 id=eq.0h1v.s4.bc03ac086d84 from=translated src=- shape=4181b9f5 vocab=4c541edf
-/
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

/--
@isnad1 id=eq.0h1v.s4.d19e2aa0f05d from=translated src=- shape=4181b9f5 vocab=4c541edf
-/
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

/--
@isnad1 id=eq.0h1v.s5.5fe46811390c from=translated src=- shape=51c8de82 vocab=477b1dbd
-/
theorem padicValRat_ten_neg_pow (k : ℕ) :
    padicValRat 2 ((10 : ℚ) ^ (-(k : ℤ))) = -(k : ℤ) := by
  rw [zpow_neg, zpow_natCast]
  rw [padicValRat.inv]
  rw [padicValRat_ten_pow]

/--
@isnad1 id=eq.0h1v.s5.b82d2d28ca44 from=translated src=- shape=51c8de82 vocab=477b1dbd
-/
theorem padicValRat_ten_neg_pow_five (k : ℕ) :
    padicValRat 5 ((10 : ℚ) ^ (-(k : ℤ))) = -(k : ℤ) := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [zpow_neg, zpow_natCast]
  rw [padicValRat.inv]
  rw [padicValRat_ten_pow_five]

noncomputable def padicValRatTop (p : ℕ) (q : ℚ) : WithTop ℤ :=
  if q = 0 then ⊤ else (padicValRat p q : WithTop ℤ)

/--
@isnad1 id=le.2h4v.s6.f08f08d8bd6e from=translated src=- shape=2c4a328e vocab=74164fb0
-/
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

/--
@isnad1 id=le.1h3v.s6.e13c45879f36 from=translated src=- shape=d69ec244 vocab=2303fcbf
-/
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
