import Tengoku.Piirrationalitymeasure.Formalization.FiniteFieldScaledSeries

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
The stronger principal-part estimates of Lemma 2.1. The quadratic factor
`5*X^2-6*X+2` has coefficient weight one when degree two costs one factor
of two. Multiplication preserves this weight, giving the extra divisibility
in low-degree coefficients of the scaled numerator.
-/

namespace PiIrrationality

def HasTwoWeight (m : ℕ) (P : Polynomial ℤ) : Prop :=
  ∀ k : ℕ, (2 : ℤ) ^ (m - k / 2) ∣ P.coeff k

/--
@isnad1 id=hastwowe.0h1v.s3.d31a3ef3d5b9 from=translated src=- shape=4583a4a8 vocab=5b1e3674
-/
theorem hasTwoWeight_zero (P : Polynomial ℤ) : HasTwoWeight 0 P := by
  intro k
  simp

/--
@isnad1 id=hastwowe.2h4v.s5.3726419f5361 from=translated src=- shape=b943f6f1 vocab=5d34a7b1
-/
theorem HasTwoWeight.mul {m n : ℕ} {P Q : Polynomial ℤ}
    (hP : HasTwoWeight m P) (hQ : HasTwoWeight n Q) : HasTwoWeight (m + n) (P * Q) := by
  intro k
  rw [Polynomial.coeff_mul]
  apply Finset.dvd_sum
  intro ij hij
  have hij' : ij.1 + ij.2 = k := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  have he : m + n - k / 2 ≤ (m - ij.1 / 2) + (n - ij.2 / 2) := by omega
  have hd := mul_dvd_mul (hP ij.1) (hQ ij.2)
  rw [← pow_add] at hd
  exact (pow_dvd_pow 2 he).trans hd

/--
@isnad1 id=hastwowe.1h3v.s5.1aafc28812e8 from=translated src=- shape=9564f6b4 vocab=5f6489bd
-/
theorem HasTwoWeight.pow {m : ℕ} {P : Polynomial ℤ}
    (hP : HasTwoWeight m P) (N : ℕ) : HasTwoWeight (N * m) (P ^ N) := by
  induction N with
  | zero => simpa using hasTwoWeight_zero (1 : Polynomial ℤ)
  | succ N ih =>
      simpa only [Nat.succ_mul, pow_succ] using ih.mul hP

/--
@isnad1 id=hastwowe.0h0v.s7.03230a7e0162 from=translated src=- shape=a2f89075 vocab=ed802077
-/
theorem lastQuadratic_hasTwoWeight :
    HasTwoWeight 1 (5 * Polynomial.X ^ 2 - 6 * Polynomial.X + 2 : Polynomial ℤ) := by
  intro k
  by_cases hk0 : k = 0
  · subst k
    norm_num
  by_cases hk1 : k = 1
  · subst k
    norm_num
  have hk : 2 ≤ k := by omega
  have he : 1 - k / 2 = 0 := by omega
  simp [he]

/--
@isnad1 id=hastwowe.0h1v.s4.e664bb830d2d from=translated src=- shape=e8ae737b vocab=71167a8e
-/
theorem scaledNumerator_hasTwoWeight (n : ℕ) :
    HasTwoWeight (3714 * n) (scaledNumerator n) := by
  have h := (hasTwoWeight_zero
    ((2 * Polynomial.X - 1) ^ (2 * 1857 * n) *
      (5 * Polynomial.X ^ 2 - 4 * Polynomial.X + 1) ^ (3714 * n))).mul
      (lastQuadratic_hasTwoWeight.pow (3714 * n))
  simpa only [Nat.mul_one, zero_add, scaledNumerator] using h

/--
@isnad1 id=dvd.0h2v.s5.8ab6ad665bd8 from=translated src=- shape=6376267d vocab=3c233091
-/
theorem scaledCoreInt_two_dvd (n k : ℕ) :
    (2 : ℤ) ^ (3714 * n - k / 2) ∣ scaledCoreInt n k := by
  unfold scaledCoreInt
  apply Finset.dvd_sum
  intro i hi
  have hi' : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have he : 3714 * n - k / 2 ≤ 3714 * n - i / 2 := by omega
  have hd := (pow_dvd_pow (2 : ℤ) he).trans (scaledNumerator_hasTwoWeight n i)
  have hcoeff : (Polynomial.hasseDeriv i (scaledNumerator n)).eval 0 =
      (scaledNumerator n).coeff i := by
    rw [← Polynomial.coeff_zero_eq_eval_zero]
    simp [Polynomial.hasseDeriv_coeff]
  rw [hcoeff]
  exact dvd_mul_of_dvd_left hd _

/--
@isnad1 id=ex.2h2v.s7.9fc5cdc678fe from=translated src=- shape=b0897a85 vocab=b6d53c13
-/
theorem principal_laurentCoeffRat_integer_factors
    (n : ℕ) (hn : 1 ≤ n) (j : ℕ) (hj : j ≤ 5570 * n) :
    ∃ z : ℤ, laurentCoeffRat n (j : ℤ) =
      (2 : ℚ) ^ (4645 * n - 1 + (3 * j + 1) / 2) *
        5 ^ (2 * n + j) * (z : ℚ) := by
  let k := 5570 * n - j
  have hk : k + j = 5570 * n := Nat.sub_add_cancel hj
  have hkorder : (5570 * (n : ℤ) - (j : ℤ)).toNat = k := by omega
  have hj' : (j : ℤ) ≤ 5570 * (n : ℤ) := by exact_mod_cast hj
  obtain ⟨z, hz⟩ := scaledCoreInt_two_dvd n k
  refine ⟨z, ?_⟩
  have hscaled := scaledCoeffInt_eq_actual n hn (j : ℤ) hj'
  rw [hkorder] at hscaled
  have hc : laurentCoeffRat n (j : ℤ) = (10 : ℚ) ^ j * (scaledCoeffInt n k : ℚ) := by
    rw [hscaled, zpow_neg, zpow_natCast]
    field_simp
  rw [hc]
  unfold scaledCoeffInt
  rw [hz]
  push_cast
  rw [show (10 : ℚ) = 2 * 5 by norm_num, mul_pow]
  have he : j + (3716 * n - 1) + (3714 * n - k / 2) =
      4645 * n - 1 + (3 * j + 1) / 2 := by omega
  calc
    _ = (2 : ℚ) ^ (j + (3716 * n - 1) + (3714 * n - k / 2)) *
        5 ^ (2 * n + j) * (z : ℚ) := by simp only [pow_add]; ring
    _ = _ := by rw [he]

/--
@isnad1 id=and.2h2v.s7.1f327021e035 from=translated src=- shape=a1cdb9a0 vocab=0498485e
-/
theorem principal_laurentCoeffRat_valuations
    (n : ℕ) (hn : 1 ≤ n) (j : ℕ) (hj : j ≤ 5570 * n) :
    ((4645 * (n : ℤ) + (3 * (j : ℤ)) / 2 - 1 : ℤ) : WithTop ℤ) ≤
        padicValRatTop 2 (laurentCoeffRat n (j : ℤ)) ∧
      ((2 * (n : ℤ) + j : ℤ) : WithTop ℤ) ≤
        padicValRatTop 5 (laurentCoeffRat n (j : ℤ)) := by
  let : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨z, hz⟩ := principal_laurentCoeffRat_integer_factors n hn j hj
  have h2 := padicValRatTop_ge_of_integer_power_factor 2
    (4645 * n - 1 + (3 * j + 1) / 2) (laurentCoeffRat n (j : ℤ))
    ⟨(5 : ℤ) ^ (2 * n + j) * z, by push_cast; rw [hz]; ring⟩
  have h5 := padicValRatTop_ge_of_integer_power_factor 5
    (2 * n + j) (laurentCoeffRat n (j : ℤ))
    ⟨(2 : ℤ) ^ (4645 * n - 1 + (3 * j + 1) / 2) * z, by push_cast; rw [hz]; ring⟩
  have he : 4645 * (n : ℤ) + (3 * (j : ℤ)) / 2 - 1 ≤
      ((4645 * n - 1 + (3 * j + 1) / 2 : ℕ) : ℤ) := by omega
  exact ⟨(show ((4645 * (n : ℤ) + (3 * (j : ℤ)) / 2 - 1 : ℤ) : WithTop ℤ) ≤
    (((4645 * n - 1 + (3 * j + 1) / 2 : ℕ) : ℤ) : WithTop ℤ) from
      WithTop.coe_le_coe.mpr he).trans h2,
    by simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using h5⟩

/--
@isnad1 id=ex.2h2v.s7.2043b4fd0637 from=translated src=- shape=f50acde5 vocab=6cf3da06
-/
theorem principal_scaled_laurentCoeffRat_integer_factors
    (n : ℕ) (hn : 1 ≤ n) (j : ℕ) (hj : j ≤ 5570 * n) :
    ∃ z : ℤ, (10 : ℚ) ^ (-(j : ℤ)) * laurentCoeffRat n (j : ℤ) =
      (2 : ℚ) ^ (4645 * n - 1 + (j + 1) / 2) * 5 ^ (2 * n) * (z : ℚ) := by
  obtain ⟨z, hz⟩ := principal_laurentCoeffRat_integer_factors n hn j hj
  refine ⟨z, ?_⟩
  rw [hz, zpow_neg, zpow_natCast]
  have he : 4645 * n - 1 + (3 * j + 1) / 2 =
      (4645 * n - 1 + (j + 1) / 2) + j := by omega
  rw [he, pow_add, pow_add, show (10 : ℚ) = 2 * 5 by norm_num, mul_pow]
  field_simp
  rw [pow_add]
  ring

end PiIrrationality
