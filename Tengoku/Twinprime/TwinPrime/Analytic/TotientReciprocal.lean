import Tengoku.Twinprime.TwinPrime.Analytic.SmoothingSummability
import Tengoku.Twinprime.TwinPrime.Analytic.SelbergCoefficientBounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Reciprocal totient sums and conductor weights

An absolutely summable convolution correction reduces reciprocal totient sums
to harmonic sums. This gives the logarithmic weight used when characters are
regrouped by their primitive conductor, without any prime-distribution input.
-/

noncomputable section

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace TwinPrime.Analytic

/-- Reciprocal Euler totient, with the arithmetic-function convention at zero.-/
def reciprocalTotient : ArithmeticFunction ℝ :=
  ⟨fun n => 1 / (Nat.totient n : ℝ), by simp⟩

/-- The absolutely summable correction in `reciprocalTotient = correction * (1/n)`.-/
def totientReciprocalCorrection : ArithmeticFunction ℝ :=
  normalizedMoebius * reciprocalTotient

@[simp] theorem reciprocalTotient_apply (n : ℕ) :
    reciprocalTotient n = 1 / (Nat.totient n : ℝ) := rfl

theorem isMultiplicative_normalizedMoebius : normalizedMoebius.IsMultiplicative := by
  refine ⟨by simp, fun {m n} hmn => ?_⟩
  simp only [normalizedMoebius_apply,
    isMultiplicative_moebius.map_mul_of_coprime hmn, Int.cast_mul, Nat.cast_mul]
  ring

theorem isMultiplicative_reciprocalTotient : reciprocalTotient.IsMultiplicative := by
  refine ⟨by simp, fun {m n} hmn => ?_⟩
  simp [Nat.totient_mul hmn, Nat.cast_mul, div_eq_mul_inv, mul_comm]

theorem isMultiplicative_totientReciprocalCorrection :
    totientReciprocalCorrection.IsMultiplicative :=
  isMultiplicative_normalizedMoebius.mul isMultiplicative_reciprocalTotient

@[simp] theorem totientReciprocalCorrection_one : totientReciprocalCorrection 1 = 1 :=
  isMultiplicative_totientReciprocalCorrection.map_one

theorem reciprocalTotient_eq_convolution :
    reciprocalTotient = totientReciprocalCorrection * reciprocalNat := by
  rw [totientReciprocalCorrection, mul_comm normalizedMoebius, mul_assoc,
    mul_comm normalizedMoebius, reciprocalNat_mul_normalizedMoebius, mul_one]

theorem totientReciprocalCorrection_prime_pow_succ (p k : ℕ) (hp : p.Prime) :
    totientReciprocalCorrection (p ^ (k + 1)) =
      reciprocalTotient (p ^ (k + 1)) - reciprocalTotient (p ^ k) / p := by
  rw [totientReciprocalCorrection, mul_apply,
    Nat.sum_divisorsAntidiagonal (fun d m => normalizedMoebius d * reciprocalTotient m),
    Nat.sum_divisors_prime_pow hp, sum_range_succ', sum_range_succ']
  have hzero : (∑ i ∈ range k,
      normalizedMoebius (p ^ (i + 1 + 1)) *
        reciprocalTotient (p ^ (k + 1) / p ^ (i + 1 + 1))) = 0 := by
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

theorem totientReciprocalCorrection_prime (p : ℕ) (hp : p.Prime) :
    totientReciprocalCorrection p = 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
  have h := totientReciprocalCorrection_prime_pow_succ p 0 hp
  simp only [zero_add, pow_one, pow_zero, reciprocalTotient_apply,
    Nat.totient_prime hp, Nat.totient_one, Nat.cast_one, div_one,
    Nat.cast_sub hp.one_le] at h
  rw [h]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    linarith
  field_simp
  ring

theorem totientReciprocalCorrection_prime_pow_succ_succ (p k : ℕ) (hp : p.Prime) :
    totientReciprocalCorrection (p ^ (k + 2)) = 0 := by
  rw [show k + 2 = (k + 1) + 1 by omega,
    totientReciprocalCorrection_prime_pow_succ p (k + 1) hp]
  simp only [reciprocalTotient_apply]
  rw [Nat.totient_prime_pow_succ hp (k + 1), Nat.totient_prime_pow_succ hp k]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hp.one_le, Nat.cast_one, pow_succ]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    linarith
  field_simp
  ring

theorem hasSum_norm_totientReciprocalCorrection_prime_pow (p : ℕ) (hp : p.Prime) :
    HasSum (fun k : ℕ => ‖totientReciprocalCorrection (p ^ k)‖)
      (1 + 1 / ((p : ℝ) * ((p : ℝ) - 1))) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have htail : HasSum (fun k : ℕ => ‖totientReciprocalCorrection (p ^ (k + 2))‖) 0 := by
    simpa only [totientReciprocalCorrection_prime_pow_succ_succ p _ hp, norm_zero]
      using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0)
  have h := (hasSum_nat_add_iff
    (f := fun k : ℕ => ‖totientReciprocalCorrection (p ^ k)‖) 2).mp htail
  simpa only [sum_range_succ, sum_range_zero, pow_zero, totientReciprocalCorrection_one,
    norm_one, zero_add, pow_one, totientReciprocalCorrection_prime p hp,
    Real.norm_of_nonneg (by positivity : 0 ≤ 1 / ((p : ℝ) * ((p : ℝ) - 1)))] using h

theorem summable_norm_totientReciprocalCorrection :
    Summable (fun n : ℕ => ‖totientReciprocalCorrection n‖) := by
  have hg : Summable (fun n : ℕ => 2 / (n : ℝ) ^ 2) := by
    simpa only [mul_one_div] using
      ((Real.summable_one_div_nat_pow (p := 2)).mpr one_lt_two).mul_left 2
  apply summable_norm_of_primePower_bound totientReciprocalCorrection
    isMultiplicative_totientReciprocalCorrection (fun n => 2 / (n : ℝ) ^ 2)
    (fun n => by positivity) hg
  intro p hp
  refine ⟨(hasSum_norm_totientReciprocalCorrection_prime_pow p hp).summable, ?_⟩
  rw [(hasSum_norm_totientReciprocalCorrection_prime_pow p hp).tsum_eq]
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp1 : 0 < (p : ℝ) - 1 := by linarith
  apply add_le_add le_rfl
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- A finite positive constant controlling all reciprocal totient sums.-/
def totientReciprocalConstant : ℝ := ∑' n : ℕ, ‖totientReciprocalCorrection n‖

theorem totientReciprocalConstant_nonneg : 0 ≤ totientReciprocalConstant :=
  tsum_nonneg fun _ => norm_nonneg _

theorem one_le_totientReciprocalConstant : 1 ≤ totientReciprocalConstant := by
  have h := summable_norm_totientReciprocalCorrection.sum_le_tsum {1}
    (fun n _ => norm_nonneg (totientReciprocalCorrection n))
  simpa only [sum_singleton, totientReciprocalCorrection_one, norm_one,
    totientReciprocalConstant] using h

/-- The reciprocal totient sum is a harmonic convolution, with integer cutoffs.-/
theorem sum_reciprocalTotient_eq_harmonic_convolution (N : ℕ) :
    (∑ n ∈ Ioc 0 N, (1 : ℝ) / Nat.totient n) =
      ∑ d ∈ Ioc 0 N, totientReciprocalCorrection d * (harmonic (N / d) : ℝ) := by
  change (∑ n ∈ Ioc 0 N, reciprocalTotient n) = _
  rw [reciprocalTotient_eq_convolution, sum_Ioc_mul_eq_sum_sum]
  simp only [reciprocalNat_apply, sum_one_div_Ioc_eq_harmonic]

/-- The elementary logarithmic bound needed for the conductor multiplicity.-/
theorem sum_reciprocalTotient_le_log (N : ℕ) :
    (∑ n ∈ Ioc 0 N, (1 : ℝ) / Nat.totient n) ≤
      totientReciprocalConstant * (1 + Real.log N) := by
  have hH (d : ℕ) : (harmonic (N / d) : ℝ) ≤ harmonic N := by
    rw [← sum_one_div_Ioc_eq_harmonic, ← sum_one_div_Ioc_eq_harmonic]
    apply sum_le_sum_of_subset_of_nonneg
    · intro n hn
      exact mem_Ioc.mpr ⟨(mem_Ioc.mp hn).1,
        (mem_Ioc.mp hn).2.trans (Nat.div_le_self N d)⟩
    · intro n _ _
      positivity
  have hH0 (d : ℕ) : (0 : ℝ) ≤ harmonic (N / d) := by
    rw [← sum_one_div_Ioc_eq_harmonic]
    exact sum_nonneg fun _ _ => by positivity
  have hlog0 : 0 ≤ 1 + Real.log (N : ℝ) := by
    by_cases hN : N = 0
    · simp [hN]
    · have : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN
      linarith [Real.log_nonneg this]
  rw [sum_reciprocalTotient_eq_harmonic_convolution]
  calc
    _ ≤ ∑ d ∈ Ioc 0 N, ‖totientReciprocalCorrection d‖ * (1 + Real.log N) := by
      apply sum_le_sum
      intro d _
      exact mul_le_mul (le_abs_self _) ((hH d).trans (harmonic_le_one_add_log N))
        (hH0 d) (norm_nonneg _)
    _ = (∑ d ∈ Ioc 0 N, ‖totientReciprocalCorrection d‖) * (1 + Real.log N) :=
      (sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (summable_norm_totientReciprocalCorrection.sum_le_tsum _ (fun _ _ => norm_nonneg _)) hlog0

/-- Multiples of a fixed conductor have a reciprocal-totient weight bounded
by the same absolute constant, with the necessary factor `1/φ(r)`.-/
theorem sum_reciprocalTotient_multiples_le_log (r Q : ℕ) (hr : 0 < r) :
    (∑ k ∈ Ioc 0 (Q / r), (1 : ℝ) / Nat.totient (r * k)) ≤
      totientReciprocalConstant * (1 + Real.log Q) / Nat.totient r := by
  have hφr : (0 : ℝ) < Nat.totient r := by exact_mod_cast Nat.totient_pos.mpr hr
  calc
    _ ≤ ∑ k ∈ Ioc 0 (Q / r), ((1 : ℝ) / Nat.totient k) / Nat.totient r := by
      apply sum_le_sum
      intro k hk
      have hφk : (0 : ℝ) < Nat.totient k := by
        exact_mod_cast Nat.totient_pos.mpr (mem_Ioc.mp hk).1
      have hφ : (Nat.totient r : ℝ) * Nat.totient k ≤ Nat.totient (r * k) := by
        exact_mod_cast Nat.totient_super_multiplicative r k
      calc
        _ ≤ 1 / ((Nat.totient r : ℝ) * Nat.totient k) :=
          one_div_le_one_div_of_le (mul_pos hφr hφk) hφ
        _ = _ := by ring
    _ = (∑ k ∈ Ioc 0 (Q / r), (1 : ℝ) / Nat.totient k) / Nat.totient r :=
      (sum_div _ _ _).symm
    _ ≤ (∑ k ∈ Ioc 0 Q, (1 : ℝ) / Nat.totient k) / Nat.totient r := by
      apply div_le_div_of_nonneg_right _ hφr.le
      apply sum_le_sum_of_subset_of_nonneg
      · intro k hk
        exact mem_Ioc.mpr ⟨(mem_Ioc.mp hk).1,
          (mem_Ioc.mp hk).2.trans (Nat.div_le_self Q r)⟩
      · intro k _ _
        positivity
    _ ≤ _ := div_le_div_of_nonneg_right (sum_reciprocalTotient_le_log Q) hφr.le

end TwinPrime.Analytic
