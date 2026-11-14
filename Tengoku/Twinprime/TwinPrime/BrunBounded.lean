import Tengoku
import Tengoku.Twinprime.TwinPrime.Sieve.BrunFinal
import Tengoku.Twinprime.TwinPrime.BrunAlmostPrime

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Brun's theorem: twin almost-primes with a bounded number of prime factors

With `z(x) = ⌊x^{1/2000}⌋` in `brunHooley_twin_count_ge`, the remainder is `≤ √x` and the main
term is `≥ x^{0.9}` for large `x`, so

  `#{n ≤ x : n(n+2) has no prime factor ≤ x^{1/2000}} ≥ x^{0.8}`   (`brunBounded_count_ge`).

Every such `n` has `Ω(n) + Ω(n+2) = Ω(n(n+2)) ≤ 2 log(x+2)/log(z+1) ≤ 4001`.  Hence
(`brun_bounded_infinite`): **there are infinitely many `n` such that `n` and `n + 2` together
have at most `4001` prime factors** (counted with multiplicity).  This is Brun's 1920 theorem in
kind (Brun: `9 + 9`); the constant `4001` reflects the crude Mertens bound and unoptimised
parameters, not the method.
-/

noncomputable section

open Finset Real Filter Topology
open TwinPrime.Sieve
open scoped ArithmeticFunction.Omega

namespace TwinPrime

/-- The sifting level `z(x) = ⌊x^{1/2000}⌋`.-/
def zC (x : ℕ) : ℕ := ⌊(x : ℝ) ^ (1 / 2000 : ℝ)⌋₊

theorem zC_le_rpow (x : ℕ) : (zC x : ℝ) ≤ (x : ℝ) ^ (1 / 2000 : ℝ) :=
  Nat.floor_le (by positivity)

theorem rpow_lt_zC_add_one (x : ℕ) : (x : ℝ) ^ (1 / 2000 : ℝ) < (zC x : ℝ) + 1 :=
  Nat.lt_floor_add_one _

theorem zC_le_self {x : ℕ} (hx : 1 ≤ x) : zC x ≤ x := by
  have h1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have : (x : ℝ) ^ (1 / 2000 : ℝ) ≤ x := by
    calc (x : ℝ) ^ (1 / 2000 : ℝ) ≤ (x : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
      _ = x := Real.rpow_one _
  exact_mod_cast le_trans (zC_le_rpow x) this

/-! ### The number of blocks is `O(log log x)` -/

/-- `Nat.log 2 y ≤ log y / log 2`.-/
theorem natLog_le_log_div {y : ℕ} (hy : 1 ≤ y) :
    (Nat.log 2 y : ℝ) ≤ Real.log y / Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hlog2]
  have h := Nat.pow_log_le_self 2 (by omega : y ≠ 0)
  have : Real.log ((2 : ℝ) ^ Nat.log 2 y) ≤ Real.log y :=
    Real.log_le_log (by positivity) (by exact_mod_cast h)
  rw [Real.log_pow] at this
  exact this

/-- `nBlocks (zC x) ≤ 2 log log x + 3` for `x ≥ 16`.-/
theorem nBlocks_zC_le {x : ℕ} (hx : 16 ≤ x) :
    (nBlocks (zC x) : ℝ) ≤ 2 * Real.log (Real.log x) + 3 := by
  have hlog2 : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  have hlog2' : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hx1 : (1 : ℝ) < x := by exact_mod_cast (by omega : 1 < x)
  have hLpos : 0 < Real.log x := Real.log_pos hx1
  -- `y := Nat.log 2 x ≥ 4`
  set y := Nat.log 2 x with hy
  have hy4 : 4 ≤ y := by
    rw [hy]
    exact (Nat.le_log_iff_pow_le (by norm_num) (by omega)).mpr (by norm_num; omega)
  have hy1 : (1 : ℝ) ≤ y := by exact_mod_cast (by omega : 1 ≤ y)
  -- `nBlocks (zC x) ≤ Nat.log 2 y + 1`
  have hmono : nBlocks (zC x) ≤ Nat.log 2 y + 1 := by
    unfold nBlocks
    have := Nat.log_mono_right (b := 2) (Nat.log_mono_right (b := 2) (zC_le_self (by omega : 1 ≤ x)))
    rw [← hy] at this
    omega
  have hmono' : (nBlocks (zC x) : ℝ) ≤ (Nat.log 2 y : ℝ) + 1 := by exact_mod_cast hmono
  -- `Nat.log 2 y ≤ log y / log 2 ≤ (log log x + log 2) / log 2`
  have h1 := natLog_le_log_div (by omega : 1 ≤ y)
  have hy_le : (y : ℝ) ≤ Real.log x / Real.log 2 := natLog_le_log_div (by omega : 1 ≤ x)
  have h2 : Real.log y ≤ Real.log (Real.log x / Real.log 2) :=
    Real.log_le_log (by positivity) hy_le
  rw [Real.log_div hLpos.ne' (by positivity)] at h2
  have h3 : Real.log (Real.log 2) ≥ -1 := by
    have : Real.log (1 / 2 : ℝ) ≤ Real.log (Real.log 2) := Real.log_le_log (by norm_num) (by linarith)
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one] at this
    linarith
  have hℓ0 : 0 ≤ Real.log (Real.log x) := Real.log_nonneg (by
    have : Real.log 16 ≤ Real.log x := Real.log_le_log (by norm_num) (by exact_mod_cast hx)
    have : Real.log 16 = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
    linarith)
  have h4 : (Nat.log 2 y : ℝ) ≤ 2 * Real.log (Real.log x) + 2 := by
    calc (Nat.log 2 y : ℝ) ≤ Real.log y / Real.log 2 := h1
      _ ≤ (Real.log (Real.log x) + 1) / Real.log 2 := by
          apply div_le_div_of_nonneg_right _ (by linarith)
          linarith
      _ ≤ (Real.log (Real.log x) + 1) / (1 / 2) := by
          apply div_le_div_of_nonneg_left (by linarith) (by norm_num) (by linarith)
      _ = 2 * Real.log (Real.log x) + 2 := by ring
  linarith

/-! ### Main and remainder terms -/

theorem log_le_2000_rpow {x : ℝ} (hx : 0 ≤ x) : Real.log x ≤ 2000 * x ^ (1 / 2000 : ℝ) := by
  calc Real.log x ≤ x ^ (1 / 2000 : ℝ) / (1 / 2000) := Real.log_le_rpow_div hx (by norm_num)
    _ = 2000 * x ^ (1 / 2000 : ℝ) := by ring

/-- `(log x)^n ≤ 2000^n x^{n/2000}`.-/
theorem log_pow_le {x : ℝ} (hx : 1 ≤ x) (n : ℕ) :
    (Real.log x) ^ n ≤ 2000 ^ n * x ^ ((n : ℝ) / 2000) := by
  have hx0 : 0 ≤ x := by linarith
  calc (Real.log x) ^ n ≤ (2000 * x ^ (1 / 2000 : ℝ)) ^ n :=
        pow_le_pow_left₀ (Real.log_nonneg hx) (log_le_2000_rpow hx0) n
    _ = 2000 ^ n * (x ^ (1 / 2000 : ℝ)) ^ (n : ℕ) := by rw [mul_pow]
    _ = 2000 ^ n * x ^ ((n : ℝ) / 2000) := by
        rw [← Real.rpow_natCast (x ^ (1 / 2000 : ℝ)) n, ← Real.rpow_mul hx0]
        congr 1
        ring_nf

theorem exp_nat_mul_loglog {x : ℝ} (hx : 0 < Real.log x) (n : ℕ) :
    Real.exp ((n : ℝ) * Real.log (Real.log x)) = (Real.log x) ^ n := by
  rw [← Real.log_pow, Real.exp_log (pow_pos hx n)]

theorem exp_neg_nat_mul_loglog {x : ℝ} (hx : 0 < Real.log x) (n : ℕ) :
    Real.exp (-((n : ℝ) * Real.log (Real.log x))) = ((Real.log x) ^ n)⁻¹ := by
  rw [Real.exp_neg, exp_nat_mul_loglog hx n]

end TwinPrime
