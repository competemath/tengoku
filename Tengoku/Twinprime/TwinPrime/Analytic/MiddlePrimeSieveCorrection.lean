import Tengoku.Twinprime.TwinPrime.Analytic.MiddlePrimeSieveDenominator

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A summable convolution correction for the middle-prime sieve denominator

The odd squarefree coefficient is a convolution of `1/n` with an explicitly
defined multiplicative correction. Its local support stops at prime squares.
These identities and absolute summability do not use prime distribution.
-/

noncomputable section

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace TwinPrime.Analytic

/-- The coefficient of the odd squarefree Selberg denominator. The factor
at the prime two is zero, so even integers are automatically excluded.-/
def middlePrimeSelbergCoefficient : ArithmeticFunction ℝ :=
  ((μ : ArithmeticFunction ℝ).pmul (μ : ArithmeticFunction ℝ)).pmul
    (.prodPrimeFactors fun p => (1 : ℝ) / ((p : ℝ) - 2))

/-- The correction removing the harmonic factor from the denominator.-/
def middlePrimeSelbergCorrection : ArithmeticFunction ℝ :=
  normalizedMoebius * middlePrimeSelbergCoefficient

/--
@isnad1 id=eq.0h1v.s6.261b95642f73 from=translated src=- shape=eaf5a60e vocab=690f1696
-/
theorem middlePrimeSelbergCoefficient_apply (n : ℕ) :
    middlePrimeSelbergCoefficient n = (μ n : ℝ) ^ 2 *
      ∏ p ∈ n.primeFactors, (1 : ℝ) / ((p : ℝ) - 2) := by
  by_cases hn : n = 0
  · subst n
    simp
  · simp [middlePrimeSelbergCoefficient, pmul_apply, prodPrimeFactors_apply hn, pow_two]

/--
@isnad1 id=ismultip.0h0v.s2.78b64515ba54 from=translated src=- shape=25b03439 vocab=ab34a2ab
-/
theorem isMultiplicative_middlePrimeSelbergCoefficient :
    middlePrimeSelbergCoefficient.IsMultiplicative := by
  unfold middlePrimeSelbergCoefficient
  exact (isMultiplicative_moebius.intCast.pmul isMultiplicative_moebius.intCast).pmul
    (IsMultiplicative.prodPrimeFactors _)

/--
@isnad1 id=ismultip.0h0v.s2.7551adf27321 from=translated src=- shape=25b03439 vocab=54bf28fd
-/
theorem isMultiplicative_middlePrimeSelbergCorrection :
    middlePrimeSelbergCorrection.IsMultiplicative :=
  isMultiplicative_normalizedMoebius.mul isMultiplicative_middlePrimeSelbergCoefficient

/--
@isnad1 id=eq.0h0v.s4.8307af8a791a from=translated src=- shape=ff26b9d8 vocab=09c731a1
-/
@[simp] theorem middlePrimeSelbergCoefficient_one : middlePrimeSelbergCoefficient 1 = 1 :=
  isMultiplicative_middlePrimeSelbergCoefficient.map_one

/--
@isnad1 id=eq.0h0v.s4.4c452126b616 from=translated src=- shape=ff26b9d8 vocab=bc44dfd8
-/
@[simp] theorem middlePrimeSelbergCorrection_one : middlePrimeSelbergCorrection 1 = 1 :=
  isMultiplicative_middlePrimeSelbergCorrection.map_one

/--
@isnad1 id=eq.1h1v.s5.0eb01459bf19 from=translated src=- shape=f8cc7707 vocab=ec1a877a
-/
theorem middlePrimeSelbergCoefficient_prime (p : ℕ) (hp : p.Prime) :
    middlePrimeSelbergCoefficient p = 1 / ((p : ℝ) - 2) := by
  simp [middlePrimeSelbergCoefficient_apply, moebius_apply_prime hp, hp.primeFactors]

/--
@isnad1 id=eq.1h2v.s5.a57971bfffe2 from=translated src=- shape=815f9e33 vocab=f7517d26
-/
theorem middlePrimeSelbergCoefficient_prime_pow_succ_succ (p k : ℕ) (hp : p.Prime) :
    middlePrimeSelbergCoefficient (p ^ (k + 2)) = 0 := by
  simp [middlePrimeSelbergCoefficient_apply,
    moebius_apply_prime_pow hp (show k + 2 ≠ 0 by omega), show k + 2 ≠ 1 by omega]

/--
@isnad1 id=eq.1h1v.s4.e702f9a34f96 from=translated src=- shape=b2686bd8 vocab=66704f56
-/
theorem middlePrimeSelbergCoefficient_eq_zero_of_even (n : ℕ) (hn : Even n) :
    middlePrimeSelbergCoefficient n = 0 := by
  by_cases hn0 : n = 0
  · subst n
    simp
  have htwo : 2 ∈ n.primeFactors := Nat.mem_primeFactors.mpr
    ⟨Nat.prime_two, hn.two_dvd, hn0⟩
  have hprod : (∏ p ∈ n.primeFactors, (1 : ℝ) / ((p : ℝ) - 2)) = 0 :=
    Finset.prod_eq_zero htwo (by norm_num)
  rw [middlePrimeSelbergCoefficient_apply, hprod, mul_zero]

/--
@isnad1 id=eq.0h1v.s6.f74f1d4019e1 from=translated src=- shape=224726a5 vocab=056ad5ac
-/
theorem middlePrimeSelbergCoefficient_eq_kernel (n : ℕ) :
    middlePrimeSelbergCoefficient n =
      if Odd n ∧ Squarefree n then
        ∏ p ∈ n.primeFactors, (1 : ℝ) / ((p : ℝ) - 2) else 0 := by
  by_cases hs : Squarefree n
  · by_cases ho : Odd n
    · rw [ite_eq_left ⟨ho, hs⟩, middlePrimeSelbergCoefficient_apply]
      have hm : (μ n : ℝ) ^ 2 = 1 := by
        exact_mod_cast moebius_sq_eq_one_of_squarefree hs
      rw [hm, one_mul]
    · rw [ite_eq_right (fun h => ho h.1),
        middlePrimeSelbergCoefficient_eq_zero_of_even n (Nat.not_odd_iff_even.mp ho)]
  · rw [ite_eq_right (fun h => hs h.2), middlePrimeSelbergCoefficient_apply,
      moebius_eq_zero_of_not_squarefree hs]
    simp

/-- Exact positive-endpoint summation of the arithmetic coefficient.
@isnad1 id=eq.0h1v.s5.5cd1914b8da1 from=translated src=- shape=0d03b97b vocab=02c300a4
-/
theorem sum_middlePrimeSelbergCoefficient_eq_denominator (z : ℕ) :
    (∑ n ∈ Ioc 0 z, middlePrimeSelbergCoefficient n) =
      middlePrimeSelbergDenominator z := by
  classical
  have hI : Icc 1 z = Ioc 0 z := by
    ext n
    simp only [mem_Icc, mem_Ioc]
    omega
  rw [middlePrimeSelbergDenominator, hI, sum_filter]
  exact sum_congr rfl fun n _ => middlePrimeSelbergCoefficient_eq_kernel n

/--
@isnad1 id=eq.0h0v.s4.b4c753b70fab from=translated src=- shape=26571668 vocab=55b817b2
-/
theorem middlePrimeSelbergCoefficient_eq_convolution :
    middlePrimeSelbergCoefficient = middlePrimeSelbergCorrection * reciprocalNat := by
  rw [middlePrimeSelbergCorrection, mul_comm normalizedMoebius, mul_assoc,
    mul_comm normalizedMoebius, reciprocalNat_mul_normalizedMoebius, mul_one]

/-- The exact harmonic convolution, with natural division retained.
@isnad1 id=eq.0h1v.s5.a40694e9eb46 from=translated src=- shape=8de08149 vocab=831e3205
-/
theorem middlePrimeSelbergDenominator_eq_harmonic_convolution (z : ℕ) :
    middlePrimeSelbergDenominator z =
      ∑ d ∈ Ioc 0 z, middlePrimeSelbergCorrection d * (harmonic (z / d) : ℝ) := by
  rw [← sum_middlePrimeSelbergCoefficient_eq_denominator,
    middlePrimeSelbergCoefficient_eq_convolution, sum_Ioc_mul_eq_sum_sum]
  simp only [reciprocalNat_apply, sum_one_div_Ioc_eq_harmonic]

/--
@isnad1 id=eq.1h2v.s7.9c52918dc6f1 from=translated src=- shape=28283fda vocab=945fb07d
-/
theorem middlePrimeSelbergCorrection_prime_pow_succ (p k : ℕ) (hp : p.Prime) :
    middlePrimeSelbergCorrection (p ^ (k + 1)) =
      middlePrimeSelbergCoefficient (p ^ (k + 1)) -
        middlePrimeSelbergCoefficient (p ^ k) / p := by
  rw [middlePrimeSelbergCorrection, mul_apply,
    Nat.sum_divisorsAntidiagonal (fun d m => normalizedMoebius d * middlePrimeSelbergCoefficient m),
    Nat.sum_divisors_prime_pow hp, sum_range_succ', sum_range_succ']
  have hzero : (∑ i ∈ range k,
      normalizedMoebius (p ^ (i + 1 + 1)) *
        middlePrimeSelbergCoefficient (p ^ (k + 1) / p ^ (i + 1 + 1))) = 0 := by
    apply sum_eq_zero
    intro i hi
    simp [normalizedMoebius_apply,
      moebius_apply_prime_pow hp (show i + 1 + 1 ≠ 0 by omega)]
  rw [hzero]
  simp only [pow_zero, normalizedMoebius_apply, moebius_apply_one, Int.cast_one,
    Nat.cast_one, div_self (one_ne_zero : (1 : ℝ) ≠ 0), one_mul, pow_one, zero_add,
    Nat.div_one, moebius_apply_prime hp, Int.cast_neg]
  rw [pow_succ, Nat.mul_div_cancel _ hp.pos]
  ring

/--
@isnad1 id=eq.0h0v.s5.bea5cea349a3 from=translated src=- shape=89f25cf5 vocab=abf8d4d7
-/
theorem middlePrimeSelbergCorrection_two : middlePrimeSelbergCorrection 2 = -1 / 2 := by
  have h := middlePrimeSelbergCorrection_prime_pow_succ 2 0 Nat.prime_two
  norm_num [middlePrimeSelbergCoefficient_prime 2 Nat.prime_two] at h
  simpa only [neg_div] using h

/--
@isnad1 id=eq.2h1v.s6.7f22fbcbefab from=translated src=- shape=5b77ea0b vocab=1a4de38e
-/
theorem middlePrimeSelbergCorrection_odd_prime (p : ℕ) (hp : p.Prime) (hpo : Odd p) :
    middlePrimeSelbergCorrection p = 2 / ((p : ℝ) * ((p : ℝ) - 2)) := by
  have h := middlePrimeSelbergCorrection_prime_pow_succ p 0 hp
  simp only [zero_add, pow_one, pow_zero, middlePrimeSelbergCoefficient_one,
    middlePrimeSelbergCoefficient_prime p hp] at h
  rw [h]
  have hp3 : (3 : ℝ) ≤ p := by
    have hp2 : p ≠ 2 := fun h => by subst p; norm_num at hpo
    exact_mod_cast (show 3 ≤ p by have := hp.two_le; omega)
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hp2 : (p : ℝ) - 2 ≠ 0 := by linarith
  field_simp
  ring

/--
@isnad1 id=eq.1h1v.s6.83290a0bd48b from=translated src=- shape=29b812ce vocab=691e9765
-/
theorem middlePrimeSelbergCorrection_prime_sq (p : ℕ) (hp : p.Prime) :
    middlePrimeSelbergCorrection (p ^ 2) = -1 / ((p : ℝ) * ((p : ℝ) - 2)) := by
  have h := middlePrimeSelbergCorrection_prime_pow_succ p 1 hp
  simp only [Nat.reduceAdd, pow_one, middlePrimeSelbergCoefficient_prime p hp,
    middlePrimeSelbergCoefficient_prime_pow_succ_succ p 0 hp] at h
  rw [h, zero_sub, div_div]
  simp only [neg_div, mul_comm]

/--
@isnad1 id=eq.1h2v.s5.5a2ff2a3b9c5 from=translated src=- shape=815f9e33 vocab=952df055
-/
theorem middlePrimeSelbergCorrection_prime_pow_succ_succ_succ
    (p k : ℕ) (hp : p.Prime) :
    middlePrimeSelbergCorrection (p ^ (k + 3)) = 0 := by
  rw [show k + 3 = (k + 2) + 1 by omega,
    middlePrimeSelbergCorrection_prime_pow_succ p (k + 2) hp,
    show k + 2 + 1 = (k + 1) + 2 by omega,
    middlePrimeSelbergCoefficient_prime_pow_succ_succ,
    middlePrimeSelbergCoefficient_prime_pow_succ_succ]
  · simp
  all_goals exact hp

/--
@isnad1 id=hassum.1h1v.s6.ee91ab382713 from=translated src=- shape=4fd56a40 vocab=9aa81def
-/
theorem hasSum_middlePrimeSelbergCorrection_prime_pow (p : ℕ) (hp : p.Prime) :
    HasSum (fun k : ℕ => middlePrimeSelbergCorrection (p ^ k))
      (1 + middlePrimeSelbergCorrection p + middlePrimeSelbergCorrection (p ^ 2)) := by
  have htail : HasSum (fun k : ℕ => middlePrimeSelbergCorrection (p ^ (k + 3))) 0 := by
    simpa only [middlePrimeSelbergCorrection_prime_pow_succ_succ_succ p _ hp]
      using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0)
  have h := (hasSum_nat_add_iff
    (f := fun k : ℕ => middlePrimeSelbergCorrection (p ^ k)) 3).mp htail
  simpa only [sum_range_succ, sum_range_zero, pow_zero, middlePrimeSelbergCorrection_one,
    zero_add, Nat.reduceAdd, pow_one] using h

/--
@isnad1 id=hassum.1h1v.s6.0f162131cf1a from=translated src=- shape=42aa0e6b vocab=8a24ac3a
-/
theorem hasSum_norm_middlePrimeSelbergCorrection_prime_pow (p : ℕ) (hp : p.Prime) :
    HasSum (fun k : ℕ => ‖middlePrimeSelbergCorrection (p ^ k)‖)
      (1 + ‖middlePrimeSelbergCorrection p‖ + ‖middlePrimeSelbergCorrection (p ^ 2)‖) := by
  have htail : HasSum (fun k : ℕ => ‖middlePrimeSelbergCorrection (p ^ (k + 3))‖) 0 := by
    simpa only [middlePrimeSelbergCorrection_prime_pow_succ_succ_succ p _ hp, norm_zero]
      using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0)
  have h := (hasSum_nat_add_iff
    (f := fun k : ℕ => ‖middlePrimeSelbergCorrection (p ^ k)‖) 3).mp htail
  simpa only [sum_range_succ, sum_range_zero, pow_zero, middlePrimeSelbergCorrection_one,
    norm_one, zero_add, Nat.reduceAdd, pow_one] using h

/--
@isnad1 id=hassum.0h0v.s6.9dd37eed557b from=translated src=- shape=1c16b63d vocab=e832ac4a
-/
theorem hasSum_middlePrimeSelbergCorrection_two_pow :
    HasSum (fun k : ℕ => middlePrimeSelbergCorrection (2 ^ k)) (1 / 2) := by
  have h := hasSum_middlePrimeSelbergCorrection_prime_pow 2 Nat.prime_two
  rw [middlePrimeSelbergCorrection_two,
    middlePrimeSelbergCorrection_prime_sq 2 Nat.prime_two] at h
  convert! h using 1
  norm_num

/--
@isnad1 id=hassum.0h0v.s6.1b40773de271 from=translated src=- shape=f99d0a40 vocab=d721aa06
-/
theorem hasSum_norm_middlePrimeSelbergCorrection_two_pow :
    HasSum (fun k : ℕ => ‖middlePrimeSelbergCorrection (2 ^ k)‖) (3 / 2) := by
  have h := hasSum_norm_middlePrimeSelbergCorrection_prime_pow 2 Nat.prime_two
  rw [middlePrimeSelbergCorrection_two,
    middlePrimeSelbergCorrection_prime_sq 2 Nat.prime_two] at h
  convert! h using 1
  norm_num

/--
@isnad1 id=hassum.2h1v.s6.62c5d19b5961 from=translated src=- shape=db55fd2f vocab=50be6224
-/
theorem hasSum_middlePrimeSelbergCorrection_odd_prime_pow (p : ℕ)
    (hp : p.Prime) (hpo : Odd p) :
    HasSum (fun k : ℕ => middlePrimeSelbergCorrection (p ^ k))
      (1 + 1 / ((p : ℝ) * ((p : ℝ) - 2))) := by
  have h := hasSum_middlePrimeSelbergCorrection_prime_pow p hp
  rw [middlePrimeSelbergCorrection_odd_prime p hp hpo,
    middlePrimeSelbergCorrection_prime_sq p hp] at h
  convert! h using 1
  ring

/--
@isnad1 id=hassum.2h1v.s6.13c420df2eae from=translated src=- shape=908240b1 vocab=c27ce8f9
-/
theorem hasSum_norm_middlePrimeSelbergCorrection_odd_prime_pow (p : ℕ)
    (hp : p.Prime) (hpo : Odd p) :
    HasSum (fun k : ℕ => ‖middlePrimeSelbergCorrection (p ^ k)‖)
      (1 + 3 / ((p : ℝ) * ((p : ℝ) - 2))) := by
  have h := hasSum_norm_middlePrimeSelbergCorrection_prime_pow p hp
  have hp3 : (3 : ℝ) ≤ p := by
    have hp2 : p ≠ 2 := fun h => by subst p; norm_num at hpo
    exact_mod_cast (show 3 ≤ p by have := hp.two_le; omega)
  have hden : 0 < (p : ℝ) * ((p : ℝ) - 2) := mul_pos (by linarith) (by linarith)
  rw [middlePrimeSelbergCorrection_odd_prime p hp hpo,
    middlePrimeSelbergCorrection_prime_sq p hp,
    Real.norm_of_nonneg (div_nonneg (by norm_num) hden.le),
    Real.norm_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by norm_num) hden.le)] at h
  convert! h using 1
  ring

/-- Absolute summability follows from the finite local Euler factors and
the ordinary convergent series `sum 9/n²`.
@isnad1 id=summable.0h0v.s4.fc56944b4fd8 from=translated src=- shape=b957a2d0 vocab=32b321af
-/
theorem summable_norm_middlePrimeSelbergCorrection :
    Summable (fun n : ℕ => ‖middlePrimeSelbergCorrection n‖) := by
  have hg : Summable (fun n : ℕ => 9 / (n : ℝ) ^ 2) := by
    simpa only [mul_one_div] using
      ((Real.summable_one_div_nat_pow (p := 2)).mpr one_lt_two).mul_left 9
  apply summable_norm_of_primePower_bound middlePrimeSelbergCorrection
    isMultiplicative_middlePrimeSelbergCorrection (fun n => 9 / (n : ℝ) ^ 2)
    (fun n => by positivity) hg
  intro p hp
  rcases hp.eq_two_or_odd with htwo | hodd
  · subst p
    refine ⟨hasSum_norm_middlePrimeSelbergCorrection_two_pow.summable, ?_⟩
    rw [hasSum_norm_middlePrimeSelbergCorrection_two_pow.tsum_eq]
    norm_num
  · have hpo : Odd p := Nat.odd_iff.mpr hodd
    refine ⟨(hasSum_norm_middlePrimeSelbergCorrection_odd_prime_pow p hp hpo).summable, ?_⟩
    rw [(hasSum_norm_middlePrimeSelbergCorrection_odd_prime_pow p hp hpo).tsum_eq]
    have hp3 : (3 : ℝ) ≤ p := by
      have hp2 : p ≠ 2 := fun h => by subst p; norm_num at hpo
      exact_mod_cast (show 3 ≤ p by have := hp.two_le; omega)
    have hp0 : (0 : ℝ) < p := by linarith
    have hden : 0 < (p : ℝ) * ((p : ℝ) - 2) := mul_pos hp0 (by linarith)
    apply add_le_add le_rfl
    rw [div_le_div_iff₀ hden (sq_pos_of_pos hp0)]
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ p by positivity) (show 0 ≤ (p : ℝ) - 3 by linarith)]

/--
@isnad1 id=summable.0h0v.s4.6c4588386832 from=translated src=- shape=ddcca31f vocab=b2cc6678
-/
theorem summable_middlePrimeSelbergCorrection : Summable middlePrimeSelbergCorrection :=
  summable_norm_middlePrimeSelbergCorrection.of_norm

end TwinPrime.Analytic
