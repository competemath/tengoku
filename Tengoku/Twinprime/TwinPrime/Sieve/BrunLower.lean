import Tengoku
import Tengoku.Twinprime.TwinPrime.Sieve.Legendre
import Tengoku.Twinprime.TwinPrime.Sieve.Bonferroni
import Tengoku.Twinprime.TwinPrime.Sieve.Rankin
import Tengoku.Twinprime.TwinPrime.Sieve.Mertens

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Brun's pure sieve for the twin sequence: the exact inequality

Combining

* the lower-bound sieve inequality with the truncated Möbius function (Bonferroni, odd `m`),
* Rankin's trick for the tail of the main term and for the remainder sum,
* the Mertens-type bound `∑_{p ≤ z} 1/p ≤ 8 (1 + log (log₂ z + 1))`,

we obtain, for the Legendre twin sieve `twinSieveL x z` (all primes `≤ z`), with

  `ℓ(z) = 16 (1 + log (log₂ z + 1))`,   `m(z) = 2 ⌈3 ℓ(z)⌉ + 1`,

the inequality (`brun_count_ge`)

  `#{n ≤ x : n(n+2) coprime to primorial z} ≥ (x+1) e^{-3ℓ(z)} / 2 − e⁴ z^{m(z)}`

valid for **every** `z ≥ 1`.  The choice `z = x^{1/(K log log x)}` is made in
`TwinPrime/BrunAlmostPrime.lean`.
-/

noncomputable section

open Finset Real Nat ArithmeticFunction BoundingSieve
open scoped ArithmeticFunction.Moebius ArithmeticFunction.omega

namespace TwinPrime.Sieve

/-- `ℓ(z) = 16 (1 + log (log₂ z + 1))`, an upper bound for `∑_{p ≤ z} ν p`.-/
def ell (z : ℕ) : ℝ := 16 * (1 + Real.log ((Nat.log 2 z : ℝ) + 1))

/-- The (odd) truncation level `m(z) = 2 ⌈3 ℓ(z)⌉ + 1`.-/
def mLevel (z : ℕ) : ℕ := 2 * ⌈3 * ell z⌉₊ + 1

/--
@isnad1 id=lt.0h1v.s3.f744fb538b0e from=translated src=- shape=b9369acb vocab=10d7b03f
-/
theorem ell_pos (z : ℕ) : 0 < ell z := by
  unfold ell
  have : 0 ≤ Real.log ((Nat.log 2 z : ℝ) + 1) := Real.log_nonneg (by
    have : (0 : ℝ) ≤ Nat.log 2 z := by positivity
    linarith)
  linarith

/--
@isnad1 id=odd.0h1v.s2.d0a81aa60390 from=translated src=- shape=6da4ece3 vocab=4c34c14a
-/
theorem mLevel_odd (z : ℕ) : Odd (mLevel z) := ⟨⌈3 * ell z⌉₊, rfl⟩

/--
@isnad1 id=le.0h1v.s5.97479a322f68 from=translated src=- shape=aa9bb20b vocab=c6a09366
-/
theorem six_ell_le_mLevel (z : ℕ) : 6 * ell z + 1 ≤ (mLevel z : ℝ) := by
  unfold mLevel
  push_cast
  have := Nat.le_ceil (3 * ell z)
  linarith

/-! ### Local densities -/

/--
@isnad1 id=le.1h1v.s5.22574550e1e0 from=translated src=- shape=9f6984ba vocab=84936a75
-/
theorem twinNu2_prime_le {p : ℕ} (hp : p.Prime) : twinNu2 p ≤ 2 / p := by
  rw [twinNu2_apply hp.ne_zero]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast twinRoots_prime_le_two hp

/--
@isnad1 id=le.1h1v.s5.b83ed5c12174 from=translated src=- shape=f50d0977 vocab=d0b4615f
-/
theorem twinNu2_prime_le_two_thirds {p : ℕ} (hp : p.Prime) : twinNu2 p ≤ 2 / 3 := by
  by_cases h2 : p = 2
  · subst h2
    rw [twinNu2_apply two_ne_zero, twinRoots_two]
    norm_num
  · refine le_trans (twinNu2_prime_le hp) ?_
    have : (3 : ℝ) ≤ p := by
      have := hp.two_le
      exact_mod_cast (by omega : 3 ≤ p)
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) this

/--
@isnad1 id=le.0h1v.s4.0306e9d82099 from=translated src=- shape=122adcd9 vocab=8d626fb8
-/
theorem twinNu2_nonneg (d : ℕ) : 0 ≤ twinNu2 d := by
  rw [twinNu2_apply']
  split_ifs <;> positivity

/-- `∑_{p ≤ z} ν p ≤ ℓ(z)`.
@isnad1 id=le.0h1v.s4.f1e0c2642114 from=translated src=- shape=e91ec5ec vocab=a4471dc6
-/
theorem sum_primesLE_twinNu2_le (z : ℕ) : ∑ p ∈ primesLE z, twinNu2 p ≤ ell z := by
  calc ∑ p ∈ primesLE z, twinNu2 p ≤ ∑ p ∈ primesLE z, 2 * (p : ℝ)⁻¹ := by
        apply sum_le_sum
        intro p hp
        rw [mul_comm, ← div_eq_inv_mul]
        exact twinNu2_prime_le (Nat.prime_of_mem_primesLE hp)
    _ = 2 * ∑ p ∈ primesLE z, (p : ℝ)⁻¹ := by rw [mul_sum]
    _ ≤ 2 * (8 * (1 + Real.log ((Nat.log 2 z : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left (sum_primesLE_inv_le z) (by norm_num)
    _ = ell z := by unfold ell; ring

/-- The main-term product is at least `e^{-3 ℓ(z)}`.
@isnad1 id=le.0h1v.s5.0165bfdf8d54 from=translated src=- shape=f4896d82 vocab=f3bbec79
-/
theorem prod_primesLE_one_sub_twinNu2_ge (z : ℕ) :
    Real.exp (-(3 * ell z)) ≤ ∏ p ∈ primesLE z, (1 - twinNu2 p) := by
  refine le_trans ?_ (prod_one_sub_ge_exp (primesLE z) (fun p => twinNu2 p)
    (fun p _ => twinNu2_nonneg p) (fun p hp => twinNu2_prime_le_two_thirds (Nat.prime_of_mem_primesLE hp)))
  apply Real.exp_le_exp.mpr
  have := sum_primesLE_twinNu2_le z
  linarith

/-- Tail of the main term: `∑_{d ∣ P, ω d ≥ m+1} ν d ≤ 8^{-(m+1)} e^{8 ℓ(z)}`.
@isnad1 id=le.0h2v.s7.50530a386c32 from=translated src=- shape=67dd96c9 vocab=d45f2d6a
-/
theorem sum_tail_twinNu2_le (z m : ℕ) :
    ∑ d ∈ (primorial z).divisors with m + 1 ≤ ω d, twinNu2 d ≤
      ((8 : ℝ) ^ (m + 1))⁻¹ * Real.exp (8 * ell z) := by
  refine le_trans (sum_divisors_filter_ge_le twinNu2 twinNu2_isMultiplicative
    (squarefree_primorial z) (fun d _ => twinNu2_nonneg d) (by norm_num : (1 : ℝ) ≤ 8) m) ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [primeFactors_primorial]
  refine le_trans (prod_one_add_le_exp_sum _ _ (fun p _ => by
    have := twinNu2_nonneg p; positivity)) ?_
  apply Real.exp_le_exp.mpr
  rw [← mul_sum]
  exact mul_le_mul_of_nonneg_left (sum_primesLE_twinNu2_le z) (by norm_num)

/-- Remainder sum: `∑_{d ∣ P, ω d ≤ m} ρ(d) ≤ z^m e⁴` for `z ≥ 1`.
@isnad1 id=le.1h2v.s6.df78233cceed from=translated src=- shape=f94370df vocab=98c09d0b
-/
theorem sum_head_twinRoots_le (z m : ℕ) (hz : 1 ≤ z) :
    ∑ d ∈ (primorial z).divisors with ω d ≤ m, (twinRoots d : ℝ) ≤ (z : ℝ) ^ m * Real.exp 4 := by
  have hz1 : (1 : ℝ) ≤ z := by exact_mod_cast hz
  have hzpos : (0 : ℝ) < z := by linarith
  have hconv : ∀ d ∈ (primorial z).divisors, (twinRoots d : ℝ) = twinRhoA d := fun d hd =>
    (twinRhoA_apply (Nat.pos_of_mem_divisors hd).ne').symm
  rw [sum_congr rfl (fun d hd => hconv d (mem_filter.mp hd).1)]
  refine le_trans (sum_divisors_filter_le_le twinRhoA twinRhoA_isMultiplicative
    (squarefree_primorial z) (fun d hd => by
      rw [twinRhoA_apply (Nat.pos_of_mem_divisors hd).ne']; positivity) hz1 m) ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [primeFactors_primorial]
  refine le_trans (prod_one_add_le_exp_sum _ _ (fun p hp => by
    rw [twinRhoA_apply (Nat.prime_of_mem_primesLE hp).ne_zero]; positivity)) ?_
  apply Real.exp_le_exp.mpr
  calc ∑ p ∈ primesLE z, twinRhoA p / (z : ℝ) ≤ ∑ _p ∈ primesLE z, 2 / (z : ℝ) := by
        apply sum_le_sum
        intro p hp
        have hpp := Nat.prime_of_mem_primesLE hp
        rw [twinRhoA_apply hpp.ne_zero]
        apply div_le_div_of_nonneg_right _ hzpos.le
        exact_mod_cast twinRoots_prime_le_two hpp
    _ = #(primesLE z) * (2 / (z : ℝ)) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ ((z : ℝ) + 1) * (2 / (z : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have : #(primesLE z) ≤ z + 1 := by
          calc #(primesLE z) ≤ #(range (z + 1)) := card_le_card (fun p hp => by
                rw [mem_primesLE] at hp; rw [mem_range]; omega)
            _ = z + 1 := card_range _
        exact_mod_cast this
    _ ≤ 4 := by
        rw [mul_div_assoc', div_le_iff₀ hzpos]
        nlinarith

/-! ### The exact Brun inequality -/

/-- `∑_{d ∣ P, ω d ≤ m} μ d ν d ≥ ∏_{p ≤ z} (1 - ν p) − ∑_{d ∣ P, ω d ≥ m+1} ν d`.
@isnad1 id=le.0h2v.s7.74afd7c40a27 from=translated src=- shape=1bc18a3b vocab=9da91c80
-/
theorem sum_truncMoebius_mul_nu_ge (z m : ℕ) :
    ∏ p ∈ primesLE z, (1 - twinNu2 p) -
        ∑ d ∈ (primorial z).divisors with m + 1 ≤ ω d, twinNu2 d ≤
      ∑ d ∈ (primorial z).divisors, truncMoebius m d * twinNu2 d := by
  have hid := IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree twinNu2
    twinNu2_isMultiplicative (squarefree_primorial z)
  rw [primeFactors_primorial] at hid
  rw [hid]
  -- split the full sum according to `ω d ≤ m`
  rw [← sum_filter_add_sum_filter_not (primorial z).divisors (fun d => ω d ≤ m)]
  have h1 : ∑ d ∈ (primorial z).divisors with ω d ≤ m, (μ d : ℝ) * twinNu2 d =
      ∑ d ∈ (primorial z).divisors, truncMoebius m d * twinNu2 d := by
    rw [sum_filter]
    apply sum_congr rfl
    intro d _
    unfold truncMoebius
    split_ifs <;> simp
  have h2 : ∑ d ∈ (primorial z).divisors with ¬ ω d ≤ m, (μ d : ℝ) * twinNu2 d ≤
      ∑ d ∈ (primorial z).divisors with m + 1 ≤ ω d, twinNu2 d := by
    have hset : ((primorial z).divisors.filter fun d => ¬ ω d ≤ m) =
        (primorial z).divisors.filter fun d => m + 1 ≤ ω d := by
      apply Finset.filter_congr
      intro d _
      omega
    rw [hset]
    apply sum_le_sum
    intro d _
    have hμ : (μ d : ℝ) ≤ 1 := by
      have h : |(μ d : ℝ)| ≤ 1 := by
        rw [← Int.cast_abs, abs_moebius]; split_ifs <;> norm_num
      linarith [le_abs_self ((μ d : ℝ))]
    have := twinNu2_nonneg d
    nlinarith
  linarith

end TwinPrime.Sieve
