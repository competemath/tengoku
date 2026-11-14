import Tengoku.Piirrationalitymeasure.Formalization.ScaledLaurent
import Tengoku.Piirrationalitymeasure.Formalization.FiniteFieldLaurent
import Tengoku.Piirrationalitymeasure.Formalization.FiniteFieldScaledSeries

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
The final algebraic step in Lemma 2.2. The finite-field local-series
argument and the proved coefficient comparison give integer divisibility
for the actual scaled coefficients, and hence Lemma 2.3.
-/

namespace PiIrrationality

/--
@isnad1 id=dvd.1h2v.s5.eab0e47917e7 from=translated src=- shape=b762c709 vocab=2bb0ecc3
-/
theorem int_dvd_of_zmod_cast_eq_zero {p : ℕ} {q : ℤ}
    (hq : (q : ZMod p) = 0) : (p : ℤ) ∣ q := by
  exact (CharP.intCast_eq_zero_iff (ZMod p) p q).mp hq

/--
@isnad1 id=dvd.2h3v.s7.125434413702 from=translated src=- shape=d1dfaec7 vocab=69c97fc2
-/
theorem int_dvd_of_zmod_mul_zpow_eq_zero
    {p : ℕ} [Fact p.Prime] (q : ℤ) (j : ℤ)
    (hpgt : 5 < p)
    (hq : (q : ZMod p) * (10 : ZMod p) ^ j = 0) :
    (p : ℤ) ∣ q := by
  have h10 : (10 : ZMod p) ≠ 0 := by
    intro h
    have : p ∣ 10 := (ZMod.natCast_eq_zero_iff 10 p).mp h
    have hcases : p ∣ 2 ∨ p ∣ 5 := by
      apply (Fact.out : Nat.Prime p).dvd_mul.mp
      simpa using this
    rcases hcases with h2 | h5
    · have : p ≤ 2 := Nat.le_of_dvd (by norm_num) h2
      omega
    · have : p ≤ 5 := Nat.le_of_dvd (by norm_num) h5
      omega
  have hpow : (10 : ZMod p) ^ j ≠ 0 := zpow_ne_zero _ h10
  have hq0 : (q : ZMod p) = 0 := by
    apply (mul_eq_zero.mp hq).resolve_right
    exact hpow
  exact int_dvd_of_zmod_cast_eq_zero hq0

/--
@isnad1 id=dvd.3h4v.s8.a6daf194ceb1 from=translated src=- shape=1b2ce466 vocab=3feab061
-/
theorem removablePrime_local_divisibility_transfer
    {n p : ℕ} [Fact p.Prime] (hp : removablePrime n p)
    (j : ℤ) (q : ℤ)
    (hj : (p : ℤ) ∣ j)
    (hcompat :
      (localLaurent (-5 : ZMod p) (finiteFieldRational n p)).coeff (-j - 1) =
        (q : ZMod p) * (10 : ZMod p) ^ j) :
    (p : ℤ) ∣ q := by
  have hzero := removablePrime_local_coeff_zero hp j hj
  rw [hzero] at hcompat
  have hmul : (q : ZMod p) * (10 : ZMod p) ^ j = 0 := hcompat.symm
  exact int_dvd_of_zmod_mul_zpow_eq_zero q j hp.2.1 hmul

/--
@isnad1 id=dvd.3h3v.s9.19cd494f1c43 from=translated src=- shape=a245f022 vocab=7b00b56b
-/
theorem local_divisibility_of_coefficient_compatibility
    (n : ℕ) (j : ℤ)
    (hcompat : ∀ p : ℕ, ∀ [Fact p.Prime], removablePrime n p → (p : ℤ) ∣ j →
      (localLaurent (-5 : ZMod p) (finiteFieldRational n p)).coeff (-j - 1) =
        (((10 : ℚ) ^ (-j) * laurentCoeffRat n j).num : ZMod p) *
          (10 : ZMod p) ^ j) :
    ∀ p : ℕ, removablePrime n p → (p : ℤ) ∣ j →
      (p : ℤ) ∣ ((10 : ℚ) ^ (-j) * laurentCoeffRat n j).num := by
  intro p hp hpj
  letI : Fact p.Prime := ⟨hp.1⟩
  apply removablePrime_local_divisibility_transfer hp j
    ((10 : ℚ) ^ (-j) * laurentCoeffRat n j).num hpj
  exact hcompat p hp hpj

/--
@isnad1 id=and.2h1v.s9.83911fc86849 from=translated src=- shape=08a03946 vocab=29f76b69
-/
theorem reducedLcm_actual_laurent_integrality_of_coefficient_compatibility
    (n : ℕ) (hn : 0 < n)
    (hcompat : ∀ j : ℤ, -(7430 * (n : ℤ)) + 1 ≤ j → j ≤ 5570 * (n : ℤ) →
      ∀ p : ℕ, ∀ [Fact p.Prime], removablePrime n p → (p : ℤ) ∣ j →
        (localLaurent (-5 : ZMod p) (finiteFieldRational n p)).coeff (-j - 1) =
          (((10 : ℚ) ^ (-j) * laurentCoeffRat n j).num : ZMod p) *
            (10 : ZMod p) ^ j) :
    (∃ L : ℤ, reducedLcm n = (L : ℚ)) ∧
      (∀ j : ℤ, -(7430 * (n : ℤ)) + 1 ≤ j → j ≤ 5570 * (n : ℤ) → j ≠ 0 →
        ∃ z : ℤ, reducedLcm n * ((10 : ℚ) ^ (-j) * laurentCoeffRat n j) /
          (j : ℚ) = (z : ℚ)) ∧
      (∃ z : ℤ, laurentCoeffRat n 0 / (Phi n : ℚ) = (z : ℚ)) := by
  apply reducedLcm_actual_laurent_integrality_of_local_divisibility n hn
  intro j hjlo hjhi p hp hpj
  exact local_divisibility_of_coefficient_compatibility n j
    (fun p hpinst hprem hpj => by
      letI : Fact p.Prime := hpinst
      exact @hcompat j hjlo hjhi p hpinst hprem hpj) p hp hpj

/--
@isnad1 id=dvd.4h3v.s6.729ab7605db8 from=translated src=- shape=5e1588f2 vocab=78a1d04f
-/
theorem removablePrime_dvd_scaled_laurentCoeff_num
    (n : ℕ) (hn : 1 ≤ n) (j : ℤ) (hj : j ≤ 5570 * (n : ℤ))
    (p : ℕ) (hp : removablePrime n p) (hpj : (p : ℤ) ∣ j) :
    (p : ℤ) ∣ ((10 : ℚ) ^ (-j) * laurentCoeffRat n j).num := by
  let : Fact p.Prime := ⟨hp.1⟩
  exact removablePrime_local_divisibility_transfer hp j _ hpj
    (finiteField_local_coeff_eq_scaled_num n p hn hp.2.1 j hj)

/--
@isnad1 id=ex.4h3v.s6.8bfb57c18f55 from=translated src=- shape=0adf6921 vocab=71156af1
-/
theorem removablePrime_scaled_laurentCoeff_integer_multiple
    (n : ℕ) (hn : 1 ≤ n) (j : ℤ) (hj : j ≤ 5570 * (n : ℤ))
    (p : ℕ) (hp : removablePrime n p) (hpj : (p : ℤ) ∣ j) :
    ∃ z : ℤ, (10 : ℚ) ^ (-j) * laurentCoeffRat n j = (p : ℚ) * (z : ℚ) := by
  obtain ⟨z, hz⟩ := removablePrime_dvd_scaled_laurentCoeff_num n hn j hj p hp hpj
  obtain ⟨q, hq⟩ := scaled_laurentCoeffRat_is_integer n hn j
  rw [hq, Rat.num_intCast] at hz
  refine ⟨z, ?_⟩
  rw [hq, hz]
  push_cast
  rfl

/--
@isnad1 id=and.1h1v.s7.ec4133fda99a from=translated src=- shape=7101b522 vocab=85447537
-/
theorem reducedLcm_actual_laurent_integrality (n : ℕ) (hn : 0 < n) :
    (∃ L : ℤ, reducedLcm n = (L : ℚ)) ∧
      (∀ j : ℤ, -(7430 * (n : ℤ)) + 1 ≤ j → j ≤ 5570 * (n : ℤ) → j ≠ 0 →
        ∃ z : ℤ, reducedLcm n * ((10 : ℚ) ^ (-j) * laurentCoeffRat n j) /
          (j : ℚ) = (z : ℚ)) ∧
      (∃ z : ℤ, laurentCoeffRat n 0 / (Phi n : ℚ) = (z : ℚ)) := by
  exact reducedLcm_actual_laurent_integrality_of_local_divisibility n hn
    (fun j _ hj p hp hpj => removablePrime_dvd_scaled_laurentCoeff_num n hn j hj p hp hpj)

end PiIrrationality
