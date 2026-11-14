import Tengoku
import Tengoku.Twinprime.TwinPrime.Sieve.BrunBlocks

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Brun's sieve for the twin sequence with bounded level: the exact inequality

We apply the general Brun–Hooley lower bound `siftedSum_ge_of_blocks` to the Legendre twin
sieve `twinSieveL x z` with the iterated-square-root blocks `brunBlocks z`, truncation parameters
`k_i = 120 + i` and `ε_i = e^{160} 2^{-(2k_i+1)}`.  The outcome (`brunHooley_twin_count_ge`):
for every `z ≥ 2`,

  `#{n ≤ x : n(n+2) coprime to primorial z} ≥ (x+1) e^{-96 r}/2 − (r+1) e^{4r} z^{972}`,

where `r = nBlocks z ≈ log₂ log₂ z`.  The point is that the level is `z^{972}`, a **fixed** power
of `z`, so `z` can be taken to be a fixed power of `x` (`TwinPrime/BrunBounded.lean`).
-/

noncomputable section

open Finset Real Nat ArithmeticFunction BoundingSieve
open scoped ArithmeticFunction.omega

namespace TwinPrime.Sieve

/-- Truncation parameters `k_i = 120 + i`.-/
def kB (z : ℕ) (i : Fin (nBlocks z)) : ℕ := 120 + i

/-- `ε_i = e^{160} / 2^{2 k_i + 1}`.-/
def epsB (z : ℕ) (i : Fin (nBlocks z)) : ℝ := Real.exp 160 / 2 ^ (2 * kB z i + 1)

/--
@isnad1 id=le.0h2v.s4.0dad2cbd23ce from=translated src=- shape=2c701dde vocab=5c7896e3
-/
theorem epsB_nonneg (z : ℕ) (i : Fin (nBlocks z)) : 0 ≤ epsB z i := by
  unfold epsB; positivity

/--
@isnad1 id=le.0h0v.s5.d0662f732757 from=translated src=- shape=3dc9892a vocab=7e715e50
-/
theorem exp_160_le : Real.exp 160 ≤ (2 : ℝ) ^ 231 := by
  rw [← Real.exp_log (by positivity : (0 : ℝ) < 2 ^ 231), Real.log_pow]
  apply Real.exp_le_exp.mpr
  have := Real.log_two_gt_d9
  push_cast
  linarith

/-- `∑_{i < r} (1/4)^i ≤ 4/3`.
@isnad1 id=le.0h1v.s6.b36086f07a6a from=translated src=- shape=1920d928 vocab=f9b94969
-/
theorem sum_quarter_pow_le (r : ℕ) : ∑ i ∈ range r, (1 / 4 : ℝ) ^ i ≤ 4 / 3 := by
  have := mul_neg_geom_sum (1 / 4 : ℝ) r
  have hpow : (0 : ℝ) ≤ (1 / 4) ^ r := by positivity
  nlinarith

/--
@isnad1 id=eq.0h2v.s6.c9c1de1347d3 from=translated src=- shape=740977a7 vocab=4800f0e4
-/
theorem epsB_eq (z : ℕ) (i : Fin (nBlocks z)) :
    epsB z i = Real.exp 160 / 2 ^ 241 * (1 / 4 : ℝ) ^ (i : ℕ) := by
  unfold epsB kB
  rw [show 2 * (120 + (i : ℕ)) + 1 = 241 + 2 * (i : ℕ) by ring, pow_add, pow_mul, one_div_pow]
  field_simp
  norm_num

/-- `∑ ε_i ≤ 1/8`.
@isnad1 id=le.0h1v.s5.23844bc74521 from=translated src=- shape=ee933215 vocab=7fabbc21
-/
theorem sum_epsB_le (z : ℕ) : ∑ i, epsB z i ≤ 1 / 8 := by
  simp_rw [epsB_eq]
  rw [← mul_sum, Fin.sum_univ_eq_sum_range (fun i => (1 / 4 : ℝ) ^ i)]
  have hgeom := sum_quarter_pow_le (nBlocks z)
  have hexp := exp_160_le
  have hsum0 : (0 : ℝ) ≤ ∑ i ∈ range (nBlocks z), (1 / 4 : ℝ) ^ i := sum_nonneg fun i _ => by positivity
  calc Real.exp 160 / 2 ^ 241 * ∑ i ∈ range (nBlocks z), (1 / 4 : ℝ) ^ i
      ≤ (2 : ℝ) ^ 231 / 2 ^ 241 * (4 / 3) :=
        mul_le_mul (div_le_div_of_nonneg_right hexp (by positivity)) hgeom hsum0 (by positivity)
    _ ≤ 1 / 8 := by norm_num

/-! ### Tails and the main-term products -/

/--
@isnad1 id=le.1h2v.s6.27bbea6a5ab4 from=translated src=- shape=60a64ffc vocab=71d8500b
-/
theorem prod_block_one_sub_ge {z : ℕ} (hz : 1 ≤ z) (i : Fin (nBlocks z)) :
    Real.exp (-96) ≤ ∏ p ∈ (brunBlock z i).primeFactors, (1 - twinNu2 p) := by
  rw [primeFactors_brunBlock]
  refine le_trans ?_ (prod_one_sub_ge_exp _ _ (fun p _ => twinNu2_nonneg p)
    (fun p hp => twinNu2_prime_le_two_thirds (prime_of_mem_blockPrimes hp)))
  apply Real.exp_le_exp.mpr
  have := sum_blockPrimes_twinNu2_le hz i
  linarith

/--
@isnad1 id=le.1h2v.s7.25c0a616a688 from=translated src=- shape=109ec528 vocab=a104ac20
-/
theorem tail_le {z : ℕ} (hz : 1 ≤ z) (i : Fin (nBlocks z)) :
    ∑ d ∈ (brunBlock z i).divisors with 2 * kB z i + 1 ≤ ω d, twinNu2 d ≤
      epsB z i * ∏ p ∈ (brunBlock z i).primeFactors, (1 - twinNu2 p) := by
  have hL := sum_blockPrimes_twinNu2_le hz i
  have hV := prod_block_one_sub_ge hz i
  have htail := sum_divisors_filter_ge_le twinNu2 twinNu2_isMultiplicative (brunBlock_squarefree z i)
    (fun d _ => twinNu2_nonneg d) (by norm_num : (1 : ℝ) ≤ 2) (2 * kB z i)
  rw [primeFactors_brunBlock] at htail
  have hprod : ∏ p ∈ blockPrimes z i, (1 + 2 * twinNu2 p) ≤ Real.exp 64 := by
    refine le_trans (prod_one_add_le_exp_sum _ _ (fun p _ => by
      have := twinNu2_nonneg p; positivity)) ?_
    apply Real.exp_le_exp.mpr
    rw [← mul_sum]
    linarith
  calc ∑ d ∈ (brunBlock z i).divisors with 2 * kB z i + 1 ≤ ω d, twinNu2 d
      ≤ ((2 : ℝ) ^ (2 * kB z i + 1))⁻¹ * ∏ p ∈ blockPrimes z i, (1 + 2 * twinNu2 p) := htail
    _ ≤ ((2 : ℝ) ^ (2 * kB z i + 1))⁻¹ * Real.exp 64 :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = epsB z i * Real.exp (-96) := by
        unfold epsB
        rw [div_mul_eq_mul_div, ← Real.exp_add]
        norm_num
        ring
    _ ≤ epsB z i * ∏ p ∈ (brunBlock z i).primeFactors, (1 - twinNu2 p) :=
        mul_le_mul_of_nonneg_left hV (epsB_nonneg z i)

/-! ### The remainder -/

/--
@isnad1 id=le.1h2v.s7.2eb51dcd1313 from=translated src=- shape=9cfa2668 vocab=a29fd298
-/
theorem rem_block_le {z : ℕ} (hz : 1 ≤ z) (i : Fin (nBlocks z)) :
    ∑ d ∈ (brunBlock z i).divisors with ω d ≤ 2 * kB z i + 1, twinRhoA d ≤
      (thr z i : ℝ) ^ (2 * kB z i + 1) * Real.exp 4 := by
  have ht1 : (1 : ℝ) ≤ thr z i := by exact_mod_cast one_le_thr hz i
  have htpos : (0 : ℝ) < thr z i := by linarith
  refine le_trans (sum_divisors_filter_le_le twinRhoA twinRhoA_isMultiplicative
    (brunBlock_squarefree z i) (fun d hd => by
      rw [twinRhoA_apply (Nat.pos_of_mem_divisors hd).ne']; positivity) ht1 _) ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [primeFactors_brunBlock]
  refine le_trans (prod_one_add_le_exp_sum _ _ (fun p hp => by
    rw [twinRhoA_apply (prime_of_mem_blockPrimes hp).ne_zero]; positivity)) ?_
  apply Real.exp_le_exp.mpr
  calc ∑ p ∈ blockPrimes z i, twinRhoA p / (thr z i : ℝ)
      ≤ ∑ _p ∈ blockPrimes z i, 2 / (thr z i : ℝ) := by
        apply sum_le_sum
        intro p hp
        have hpp := prime_of_mem_blockPrimes hp
        rw [twinRhoA_apply hpp.ne_zero]
        apply div_le_div_of_nonneg_right _ htpos.le
        exact_mod_cast twinRoots_prime_le_two hpp
    _ = #(blockPrimes z i) * (2 / (thr z i : ℝ)) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ ((thr z i : ℝ) + 1) * (2 / (thr z i : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast card_blockPrimes_le i
    _ ≤ 4 := by
        rw [mul_div_assoc', div_le_iff₀ htpos]
        nlinarith

/-- `∑_{i<r} (i+1)/2^i = 4 − (2r+4)/2^r ≤ 4`.
@isnad1 id=eq.0h1v.s7.1146ab8b2fa4 from=translated src=- shape=3b06b0ca vocab=113fc2fa
-/
theorem sum_succ_div_two_pow_eq (r : ℕ) :
    ∑ i ∈ range r, ((i : ℝ) + 1) / 2 ^ i = 4 - (2 * (r : ℝ) + 4) / 2 ^ r := by
  induction r with
  | zero => norm_num
  | succ r ih =>
    rw [sum_range_succ, ih, pow_succ]
    push_cast
    field_simp
    ring

/--
@isnad1 id=le.0h1v.s6.eaf329800e13 from=translated src=- shape=a93316e5 vocab=e139705d
-/
theorem sum_succ_div_two_pow_le (r : ℕ) : ∑ i ∈ range r, ((i : ℝ) + 1) / 2 ^ i ≤ 4 := by
  rw [sum_succ_div_two_pow_eq]
  have : (0 : ℝ) ≤ (2 * (r : ℝ) + 4) / 2 ^ r := by positivity
  linarith

/-- The exponent sum `∑_{i<r} (2 k_i + 1) / 2^i ≤ 972`.
@isnad1 id=le.0h1v.s6.6cb87a77c5f2 from=translated src=- shape=3f28ee01 vocab=53a2be45
-/
theorem sum_exponent_le (z : ℕ) :
    ∑ i : Fin (nBlocks z), (1 : ℝ) / 2 ^ (i : ℕ) * ((2 * kB z i + 1 : ℕ) : ℝ) ≤ 972 := by
  unfold kB
  calc ∑ i : Fin (nBlocks z), (1 : ℝ) / 2 ^ (i : ℕ) * ((2 * (120 + (i : ℕ)) + 1 : ℕ) : ℝ)
      ≤ ∑ i : Fin (nBlocks z), 243 * (((i : ℕ) : ℝ) + 1) / 2 ^ (i : ℕ) := by
        apply sum_le_sum
        intro i _
        push_cast
        have h2 : (0 : ℝ) < 2 ^ (i : ℕ) := by positivity
        rw [show (1 : ℝ) / 2 ^ (i : ℕ) * (2 * (120 + ((i : ℕ) : ℝ)) + 1) =
            (2 * (120 + ((i : ℕ) : ℝ)) + 1) / 2 ^ (i : ℕ) by ring]
        apply div_le_div_of_nonneg_right _ h2.le
        linarith
    _ = 243 * ∑ i ∈ range (nBlocks z), ((i : ℝ) + 1) / 2 ^ i := by
        rw [mul_sum, Fin.sum_univ_eq_sum_range (fun i => 243 * ((i : ℝ) + 1) / 2 ^ i)]
        apply sum_congr rfl
        intro i _
        ring
    _ ≤ 243 * 4 := mul_le_mul_of_nonneg_left (sum_succ_div_two_pow_le _) (by norm_num)
    _ = 972 := by norm_num

/--
@isnad1 id=le.1h1v.s7.88d8a58ada48 from=translated src=- shape=b515513b vocab=667902a6
-/
theorem prod_rem_le {z : ℕ} (hz : 1 ≤ z) :
    ∏ i : Fin (nBlocks z), ((thr z i : ℝ) ^ (2 * kB z i + 1) * Real.exp 4) ≤
      Real.exp (4 * nBlocks z) * (z : ℝ) ^ (972 : ℝ) := by
  have hzr : (1 : ℝ) ≤ z := by exact_mod_cast hz
  have hzpos : (0 : ℝ) < z := by linarith
  rw [prod_mul_distrib, prod_const, Finset.card_fin, ← Real.exp_nat_mul, mul_comm,
    show ((nBlocks z : ℕ) : ℝ) * 4 = 4 * nBlocks z by ring]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  calc ∏ i : Fin (nBlocks z), (thr z i : ℝ) ^ (2 * kB z i + 1)
      ≤ ∏ i : Fin (nBlocks z), (z : ℝ) ^ ((1 : ℝ) / 2 ^ (i : ℕ) * ((2 * kB z i + 1 : ℕ) : ℝ)) := by
        apply prod_le_prod
        · intro i _; positivity
        · intro i _
          rw [Real.rpow_mul hzpos.le, Real.rpow_natCast]
          exact pow_le_pow_left₀ (by positivity) (thr_le_rpow hz i) _
    _ = (z : ℝ) ^ (∑ i : Fin (nBlocks z), (1 : ℝ) / 2 ^ (i : ℕ) * ((2 * kB z i + 1 : ℕ) : ℝ)) := by
        rw [Real.rpow_sum_of_pos hzpos]
    _ ≤ (z : ℝ) ^ (972 : ℝ) := Real.rpow_le_rpow_of_exponent_le hzr (sum_exponent_le z)

/-! ### The exact inequality -/

/--
@isnad1 id=le.0h1v.s4.333065cede03 from=translated src=- shape=122adcd9 vocab=d8c76a03
-/
theorem twinRhoA_nonneg (d : ℕ) : 0 ≤ twinRhoA d := by
  by_cases hd : d = 0
  · subst hd; simp [twinRhoA]
  · rw [twinRhoA_apply hd]; positivity

/--
@isnad1 id=le.1h3v.s5.0c49b60814e5 from=translated src=- shape=35e36bc3 vocab=9d6c4c49
-/
theorem twinSieveL_abs_rem_le_rhoA (x z : ℕ) {d : ℕ} (hd : d ∣ primorial z) :
    |(twinSieveL x z).rem d| ≤ twinRhoA d := by
  have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero (primorial_pos z).ne' hd
  rw [twinRhoA_apply hd0]
  exact twinSieveL_abs_rem_le x z hd0

end TwinPrime.Sieve
