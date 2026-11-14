import Tengoku.Twinprime.TwinPrime.Analytic.MoebiusTotient
import Tengoku.Twinprime.TwinPrime.Analytic.MixedCorrelation
import Tengoku.Seed.Algebra.Order.Floor.Semifield

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# An exact convolution bridge for the odd Möbius/totient sums

The correction function `smoothingCorrection` removes the change from `μ(n)/n`
to the odd-supported coefficient `μ(n)/φ(n)`. Its definition and the finite
summation identities below are algebraic: they require no cancellation estimate.
The smoothed Möbius sum has a real argument, so division in its logarithm retains
the original endpoint even when the integer summation cutoff is rounded down.
-/

noncomputable section

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace TwinPrime.Analytic

/-- The arithmetic function `n ↦ 1/n`, with value zero at zero.-/
def reciprocalNat : ArithmeticFunction ℝ :=
  ⟨fun n => 1 / (n : ℝ), by simp⟩

/-- The usual Möbius coefficient divided by its argument.-/
def normalizedMoebius : ArithmeticFunction ℝ :=
  ⟨fun n => (μ n : ℝ) / n, by simp⟩

/-- The odd-supported Möbius/totient coefficient.-/
def oddMoebiusTotient : ArithmeticFunction ℝ :=
  ⟨fun n => if Odd n then (μ n : ℝ) / Nat.totient n else 0, by simp⟩

/-- The correction in `oddMoebiusTotient = smoothingCorrection * normalizedMoebius`.
Multiplication here is Dirichlet convolution.-/
def smoothingCorrection : ArithmeticFunction ℝ := oddMoebiusTotient * reciprocalNat

@[simp] theorem reciprocalNat_apply (n : ℕ) : reciprocalNat n = 1 / (n : ℝ) := rfl
@[simp] theorem normalizedMoebius_apply (n : ℕ) :
    normalizedMoebius n = (μ n : ℝ) / n := rfl
@[simp] theorem oddMoebiusTotient_apply (n : ℕ) :
    oddMoebiusTotient n = if Odd n then (μ n : ℝ) / Nat.totient n else 0 := rfl

theorem reciprocalNat_mul_normalizedMoebius :
    reciprocalNat * normalizedMoebius = 1 := by
  ext n
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun d m => reciprocalNat d * normalizedMoebius m)]
  have hterm : ∀ d ∈ n.divisors,
      reciprocalNat d * normalizedMoebius (n / d) = (μ (n / d) : ℝ) / n := by
    intro d hd
    have hmul : (d : ℝ) * (n / d : ℕ) = n := by
      exact_mod_cast (Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd))
    simp only [reciprocalNat_apply, normalizedMoebius_apply]
    rw [← hmul]
    ring
  simp_rw [sum_congr rfl hterm, ← sum_div]
  have hμ : (∑ d ∈ n.divisors, (μ (n / d) : ℝ)) = (1 : ArithmeticFunction ℝ) n := by
    rw [Nat.sum_div_divisors n (fun d => (μ d : ℝ))]
    have h := congrArg (fun f : ArithmeticFunction ℝ => f n)
      (coe_moebius_mul_coe_zeta (R := ℝ))
    simpa only [coe_mul_zeta_apply, intCoe_apply] using h
  rw [hμ]
  by_cases hn : n = 1
  · subst n; simp
  · simp [one_apply_ne hn]

theorem oddMoebiusTotient_eq_convolution :
    oddMoebiusTotient = smoothingCorrection * normalizedMoebius := by
  rw [smoothingCorrection, mul_assoc, reciprocalNat_mul_normalizedMoebius, mul_one]

theorem isMultiplicative_reciprocalNat : reciprocalNat.IsMultiplicative := by
  refine ⟨by simp, fun {m n} _ => ?_⟩
  simp [Nat.cast_mul, div_eq_mul_inv, mul_comm]

theorem isMultiplicative_oddMoebiusTotient : oddMoebiusTotient.IsMultiplicative := by
  refine ⟨by simp, fun {m n} hmn => ?_⟩
  have hμ := isMultiplicative_moebius.map_mul_of_coprime hmn
  simp only [oddMoebiusTotient_apply, Nat.odd_mul, Nat.totient_mul hmn, hμ,
    Nat.cast_mul, Int.cast_mul]
  split_ifs <;> simp_all
  ring

theorem isMultiplicative_smoothingCorrection : smoothingCorrection.IsMultiplicative :=
  isMultiplicative_oddMoebiusTotient.mul isMultiplicative_reciprocalNat

@[simp] theorem smoothingCorrection_one : smoothingCorrection 1 = 1 :=
  isMultiplicative_smoothingCorrection.map_one

theorem oddMoebiusTotient_prime_pow_succ_succ (p k : ℕ) (hp : p.Prime) :
    oddMoebiusTotient (p ^ (k + 2)) = 0 := by
  simp [oddMoebiusTotient_apply,
    moebius_apply_prime_pow hp (show k + 2 ≠ 0 by omega), show k + 2 ≠ 1 by omega]

theorem smoothingCorrection_prime_pow_succ (p k : ℕ) (hp : p.Prime) :
    smoothingCorrection (p ^ (k + 1)) =
      1 / (p : ℝ) ^ (k + 1) + oddMoebiusTotient p / (p : ℝ) ^ k := by
  rw [smoothingCorrection, mul_apply,
    Nat.sum_divisorsAntidiagonal (fun d m => oddMoebiusTotient d * reciprocalNat m),
    Nat.sum_divisors_prime_pow hp, sum_range_succ', sum_range_succ']
  have hzero : (∑ i ∈ range k,
      oddMoebiusTotient (p ^ (i + 1 + 1)) *
        reciprocalNat (p ^ (k + 1) / p ^ (i + 1 + 1))) = 0 := by
    apply sum_eq_zero
    intro i hi
    rw [show i + 1 + 1 = i + 2 by omega, oddMoebiusTotient_prime_pow_succ_succ p i hp,
      zero_mul]
  rw [hzero]
  simp only [pow_zero, oddMoebiusTotient_apply, show Odd 1 by decide,
    ite_true, moebius_apply_one, Int.cast_one, Nat.totient_one, Nat.cast_one,
    div_self (one_ne_zero : (1 : ℝ) ≠ 0), one_mul, reciprocalNat_apply,
    pow_one, zero_add]
  rw [pow_succ, Nat.mul_div_cancel _ hp.pos, Nat.cast_pow]
  simp only [Nat.div_one, Nat.cast_mul, Nat.cast_pow]
  ring

theorem smoothingCorrection_two_pow (k : ℕ) :
    smoothingCorrection (2 ^ k) = 1 / (2 : ℝ) ^ k := by
  cases k with
  | zero => simp
  | succ k =>
      rw [smoothingCorrection_prime_pow_succ 2 k Nat.prime_two]
      norm_num [oddMoebiusTotient_apply]

theorem smoothingCorrection_odd_prime_pow (p k : ℕ) (hp : p.Prime) (hpodd : Odd p) :
    smoothingCorrection (p ^ (k + 1)) =
      -1 / ((p : ℝ) ^ (k + 1) * ((p : ℝ) - 1)) := by
  rw [smoothingCorrection_prime_pow_succ p k hp, oddMoebiusTotient_apply,
    ite_eq_left hpodd, moebius_apply_prime hp, Nat.totient_prime hp]
  push_cast [Nat.cast_sub hp.one_le]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have h : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    linarith
  rw [pow_succ]
  field_simp
  ring

/-- The ordinary partial sum of `μ(n)/n`.-/
def normalizedMoebiusSum (U : ℕ) : ℝ := ∑ n ∈ Ioc 0 U, normalizedMoebius n

/-- A logarithmically smoothed ordinary Möbius sum with its real endpoint intact.-/
def smoothedMoebiusSum (x : ℝ) : ℝ :=
  ∑ n ∈ Ioc 0 ⌊x⌋₊, normalizedMoebius n * Real.log (x / n)

theorem oddMoebiusTotientSum_eq_sum (U : ℕ) :
    oddMoebiusTotientSum U = ∑ n ∈ Ioc 0 U, oddMoebiusTotient n := by
  unfold oddMoebiusTotientSum oddCutoff
  have hI : Icc 1 U = Ioc 0 U := by ext n; simp only [mem_Icc, mem_Ioc]; omega
  rw [hI, sum_filter]
  rfl

/-- The unsmoothed finite convolution bridge. The quotient in the cutoff is natural division.-/
theorem oddMoebiusTotientSum_eq_smoothingConvolution (U : ℕ) :
    oddMoebiusTotientSum U =
      ∑ d ∈ Ioc 0 U, smoothingCorrection d * normalizedMoebiusSum (U / d) := by
  rw [oddMoebiusTotientSum_eq_sum, oddMoebiusTotient_eq_convolution,
    sum_Ioc_mul_eq_sum_sum]
  rfl

/-- Finite weighted summation of a Dirichlet convolution.-/
theorem sum_Ioc_convolution_weight (f g : ArithmeticFunction ℝ) (w : ℕ → ℝ) (U : ℕ) :
    ∑ n ∈ Ioc 0 U, (f * g) n * w n =
      ∑ d ∈ Ioc 0 U, f d * ∑ m ∈ Ioc 0 (U / d), g m * w (d * m) := by
  have hprod : (∑ n ∈ Ioc 0 U, (f * g) n * w n) =
      ∑ x ∈ Ioc 0 U ×ˢ Ioc 0 U with x.1 * x.2 ≤ U,
        f x.1 * g x.2 * w (x.1 * x.2) := by
    simp only [mul_apply, sum_mul]
    trans ∑ n ∈ Ioc 0 U,
      ∑ x ∈ Ioc 0 U ×ˢ Ioc 0 U with x.1 * x.2 = n,
        f x.1 * g x.2 * w (x.1 * x.2)
    · refine sum_congr rfl fun n hn => ?_
      rw [Nat.divisorsAntidiagonal_eq_prod_filter_of_le
        (mem_Ioc.mp hn).1.ne' (mem_Ioc.mp hn).2]
      refine sum_congr rfl fun x hx => ?_
      rw [(mem_filter.mp hx).2]
    · simp_rw [sum_filter]
      rw [sum_comm]
      refine sum_congr rfl fun x hx => ?_
      have hpos : 0 < x.1 * x.2 :=
        Nat.mul_pos (mem_Ioc.mp (mem_product.mp hx).1).1
          (mem_Ioc.mp (mem_product.mp hx).2).1
      simp [hpos]
  rw [hprod, sum_filter, sum_product]
  refine sum_congr rfl fun d hd => ?_
  simp only [sum_ite, not_le, sum_const_zero, add_zero]
  have hset : {m ∈ Ioc 0 U | d * m ≤ U} = Ioc 0 (U / d) := by
    ext m
    have hdpos := (mem_Ioc.mp hd).1
    simp only [mem_filter, mem_Ioc]
    constructor
    · rintro ⟨⟨hm, hmU⟩, hdm⟩
      exact ⟨hm, (Nat.le_div_iff_mul_le hdpos).mpr (by simpa [mul_comm] using hdm)⟩
    · rintro ⟨hm, hmU⟩
      exact ⟨⟨hm, hmU.trans (Nat.div_le_self U d)⟩,
        by simpa [mul_comm] using (Nat.le_div_iff_mul_le hdpos).mp hmU⟩
  rw [hset, mul_sum]
  apply sum_congr rfl
  intro m hm
  ring

theorem smoothedTotientSum_eq_sum (U : ℕ) :
    smoothedTotientSum U =
      ∑ n ∈ Ioc 0 U, oddMoebiusTotient n * Real.log ((U : ℝ) / n) := by
  unfold smoothedTotientSum
  have hset : {n ∈ range (U + 1) | Odd n} = {n ∈ Ioc 0 U | Odd n} := by
    ext n
    simp only [mem_filter, mem_range, mem_Ioc]
    constructor
    · rintro ⟨hn, ho⟩
      exact ⟨⟨ho.pos, by omega⟩, ho⟩
    · rintro ⟨hn, ho⟩
      exact ⟨by omega, ho⟩
  rw [hset, sum_filter]
  apply sum_congr rfl
  intro n hn
  simp only [oddMoebiusTotient_apply, truncatedWeight]
  split_ifs <;> ring

/-- The smoothed finite convolution bridge. Its real quotient is essential:
only the summation cutoff inside `smoothedMoebiusSum` is rounded down.-/
theorem smoothedTotientSum_eq_smoothingConvolution (U : ℕ) :
    smoothedTotientSum U =
      ∑ d ∈ Ioc 0 U, smoothingCorrection d * smoothedMoebiusSum ((U : ℝ) / d) := by
  rw [smoothedTotientSum_eq_sum, oddMoebiusTotient_eq_convolution,
    sum_Ioc_convolution_weight]
  apply sum_congr rfl
  intro d hd
  unfold smoothedMoebiusSum
  rw [Nat.floor_div_natCast, Nat.floor_natCast]
  congr 1
  apply sum_congr rfl
  intro m hm
  rw [Nat.cast_mul, div_mul_eq_div_div]

end TwinPrime.Analytic
