import Tengoku.Twinprime.TwinPrime.Analytic.BVInternalCutoffs
import Tengoku.Twinprime.TwinPrime.Analytic.BVLogComparisons

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Numerical absorption of the finite Vaughan mean-value budget

The raw Type I and Type II budgets are kept explicit. The eighth-root
internal cutoff absorbs them into one fixed polynomial times `log^6 T`.
This module proves only the numerical comparisons applied to the separate
finite arithmetic mean-value estimates.
-/

noncomputable section

namespace TwinPrime.Analytic

def bvMeanPolynomial (T R : ℕ) : ℝ :=
  (T : ℝ) + (T : ℝ) ^ (15 / 16 : ℝ) * R + Real.sqrt (T : ℝ) * (R : ℝ) ^ 2

def bvMeanConstant : ℝ := 5 + 16 * (2 / Real.log 2) ^ 4

def bvTypeIBudget (T R : ℕ) : ℝ :=
  let W := bvInternalCutoff T
  2 * (W : ℝ) * (R : ℝ) ^ 2 * Real.sqrt (R : ℝ) *
      (1 + Real.log (R : ℝ)) * Real.log (T : ℝ) +
    ((W * W : ℕ) : ℝ) * Real.log ((W * W : ℕ) : ℝ) * (R : ℝ) ^ 2 *
      Real.sqrt (R : ℝ) * (1 + Real.log (R : ℝ)) +
    (W : ℝ) * Real.log (W : ℝ) * (R : ℝ) ^ 2

def bvTypeIIBudget (T R : ℕ) : ℝ :=
  let W := bvInternalCutoff T
  2 * (dyadicNatDepth T : ℝ) ^ 4 * Real.log (T : ℝ) * characterLargeSieveLogFactor R *
    ((T : ℝ) + (R : ℝ) * T *
      (1 / Real.sqrt ((W : ℝ) / 2) + 1 / Real.sqrt ((W : ℝ) / 2)) +
      (R : ℝ) ^ 2 * Real.sqrt (T : ℝ))

theorem bvMeanConstant_pos : 0 < bvMeanConstant := by
  unfold bvMeanConstant
  positivity

theorem bvMeanPolynomial_nonneg (T R : ℕ) : 0 ≤ bvMeanPolynomial T R := by
  unfold bvMeanPolynomial
  positivity

theorem bvMeanPolynomial_ge_endpoint (T R : ℕ) : (T : ℝ) ≤ bvMeanPolynomial T R := by
  unfold bvMeanPolynomial
  have h1 : 0 ≤ (T : ℝ) ^ (15 / 16 : ℝ) * R := by positivity
  have h2 : 0 ≤ Real.sqrt (T : ℝ) * (R : ℝ) ^ 2 := by positivity
  linarith

theorem bvMeanPolynomial_ge_modulus_sq (T R : ℕ) :
    Real.sqrt (T : ℝ) * (R : ℝ) ^ 2 ≤ bvMeanPolynomial T R := by
  unfold bvMeanPolynomial
  have h1 : 0 ≤ (T : ℝ) ^ (15 / 16 : ℝ) * R := by positivity
  have h2 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  linarith

/-- The three Type I contributions have aggregate constant four.-/
theorem bvTypeIBudget_le (T R : ℕ) (hT : 256 ≤ T) (hR1 : 1 ≤ R)
    (hR : (R : ℝ) ≤ Real.sqrt (T : ℝ)) :
    bvTypeIBudget T R ≤ 4 * Real.sqrt (T : ℝ) * (R : ℝ) ^ 2 * (Real.log (T : ℝ)) ^ 2 := by
  let w : ℝ := bvInternalCutoff T
  let l : ℝ := Real.log (T : ℝ)
  have hw0 : 0 ≤ w := Nat.cast_nonneg _
  have hw1 : 1 ≤ w := by
    dsimp only [w]
    exact_mod_cast (show 1 ≤ bvInternalCutoff T from
      (by have := bvInternalCutoff_two_le T hT; omega))
  have hwpos : 0 < w := zero_lt_one.trans_le hw1
  have hl1 : 1 ≤ l := one_le_log_of_256_le T hT
  have hl0 : 0 ≤ l := zero_le_one.trans hl1
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast (show 1 ≤ T by omega)
  have hwS : w ≤ Real.sqrt (T : ℝ) := bvInternalCutoff_le_sqrt T hT
  have hwT : w ≤ (T : ℝ) := hwS.trans (Real.sqrt_le_self_iff.mpr (Or.inr hT1))
  have hw2T : w ^ 2 ≤ (T : ℝ) := (bvInternalCutoff_sq_le_rpow_quarter T).trans
    (Real.rpow_le_self_of_one_le hT1 (by norm_num))
  have hwlog : Real.log w ≤ l := Real.log_le_log hwpos hwT
  have hwlog0 : 0 ≤ Real.log w := Real.log_nonneg hw1
  have hw2log : Real.log (w * w) ≤ l :=
    Real.log_le_log (mul_pos hwpos hwpos) (by simpa only [pow_two] using hw2T)
  have hw2log0 : 0 ≤ Real.log (w * w) := Real.log_nonneg (by nlinarith)
  have hrlog : 1 + Real.log (R : ℝ) ≤ l := one_add_log_modulus_le_log T R hT hR1 hR
  have hrlog0 : 0 ≤ 1 + Real.log (R : ℝ) := by
    have := Real.log_natCast_nonneg R
    linarith
  have hw2R : w ^ 2 * Real.sqrt (R : ℝ) ≤ Real.sqrt (T : ℝ) :=
    bvInternalCutoff_sq_mul_sqrt_modulus_le T R hT hR
  have hwR : w * Real.sqrt (R : ℝ) ≤ Real.sqrt (T : ℝ) :=
    (mul_le_mul_of_nonneg_right (show w ≤ w ^ 2 by nlinarith)
      (Real.sqrt_nonneg _)).trans hw2R
  have h1 : 2 * w * (R : ℝ) ^ 2 * Real.sqrt (R : ℝ) *
      (1 + Real.log (R : ℝ)) * l ≤ 2 * Real.sqrt (T : ℝ) * (R : ℝ) ^ 2 * l ^ 2 := by
    calc
      _ = 2 * (w * Real.sqrt (R : ℝ)) * (R : ℝ) ^ 2 * (1 + Real.log (R : ℝ)) * l := by ring
      _ ≤ 2 * Real.sqrt (T : ℝ) * (R : ℝ) ^ 2 * l * l :=
        mul_le_mul_of_nonneg_right (mul_le_mul
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hwR (by norm_num)) (sq_nonneg _))
          hrlog hrlog0 (by positivity)) hl0
      _ = _ := by ring
  have h2 : (w * w) * Real.log (w * w) * (R : ℝ) ^ 2 * Real.sqrt (R : ℝ) *
      (1 + Real.log (R : ℝ)) ≤ Real.sqrt (T : ℝ) * (R : ℝ) ^ 2 * l ^ 2 := by
    calc
      _ = (w ^ 2 * Real.sqrt (R : ℝ)) * (R : ℝ) ^ 2 * Real.log (w * w) *
          (1 + Real.log (R : ℝ)) := by ring
      _ ≤ Real.sqrt (T : ℝ) * (R : ℝ) ^ 2 * l * l :=
        mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right hw2R (sq_nonneg _))
          hw2log hw2log0 (by positivity)) hrlog hrlog0 (by positivity)
      _ = _ := by ring
  have h3 : w * Real.log w * (R : ℝ) ^ 2 ≤ Real.sqrt (T : ℝ) * (R : ℝ) ^ 2 * l ^ 2 := by
    calc
      _ ≤ Real.sqrt (T : ℝ) * l * (R : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul hwS hwlog hwlog0 (Real.sqrt_nonneg _)) (sq_nonneg _)
      _ ≤ Real.sqrt (T : ℝ) * l ^ 2 * (R : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by nlinarith : l ≤ l ^ 2)
          (Real.sqrt_nonneg _)) (sq_nonneg _)
      _ = _ := by ring
  unfold bvTypeIBudget
  simp only [Nat.cast_mul]
  change 2 * w * (R : ℝ) ^ 2 * Real.sqrt (R : ℝ) * (1 + Real.log (R : ℝ)) * l +
    (w * w) * Real.log (w * w) * (R : ℝ) ^ 2 * Real.sqrt (R : ℝ) *
      (1 + Real.log (R : ℝ)) + w * Real.log w * (R : ℝ) ^ 2 ≤ _
  linarith

/-- Both half-cutoff reciprocal factors are absorbed into the middle
`T^(15/16) R` term, at cost four for the complete polynomial.-/
theorem bvInternalCutoff_polynomial_le_four (T R : ℕ) (hT : 256 ≤ T) :
    ((T : ℝ) + (R : ℝ) * T *
      (1 / Real.sqrt ((bvInternalCutoff T : ℝ) / 2) +
        1 / Real.sqrt ((bvInternalCutoff T : ℝ) / 2)) +
      (R : ℝ) ^ 2 * Real.sqrt (T : ℝ)) ≤ 4 * bvMeanPolynomial T R := by
  have hT0 : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have hrec := bvInternalCutoff_half_reciprocal_sqrt_le T hT
  have hpair : 1 / Real.sqrt ((bvInternalCutoff T : ℝ) / 2) +
      1 / Real.sqrt ((bvInternalCutoff T : ℝ) / 2) ≤ 4 * (T : ℝ) ^ (-1 / 16 : ℝ) := by
    linarith
  have hpow : (T : ℝ) * (T : ℝ) ^ (-1 / 16 : ℝ) = (T : ℝ) ^ (15 / 16 : ℝ) := by
    calc
      _ = (T : ℝ) ^ (1 : ℝ) * (T : ℝ) ^ (-1 / 16 : ℝ) := by rw [Real.rpow_one]
      _ = (T : ℝ) ^ ((1 : ℝ) + (-1 / 16 : ℝ)) := (Real.rpow_add hT0 _ _).symm
      _ = _ := by norm_num
  calc
    _ ≤ (T : ℝ) + (R : ℝ) * T * (4 * (T : ℝ) ^ (-1 / 16 : ℝ)) +
        (R : ℝ) ^ 2 * Real.sqrt (T : ℝ) :=
      add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hpair (by positivity))) le_rfl
    _ = (T : ℝ) + 4 * (T : ℝ) ^ (15 / 16 : ℝ) * R + Real.sqrt (T : ℝ) * (R : ℝ) ^ 2 := by
      calc
        _ = (T : ℝ) + 4 * ((T : ℝ) * (T : ℝ) ^ (-1 / 16 : ℝ)) * R +
            Real.sqrt (T : ℝ) * (R : ℝ) ^ 2 := by ring
        _ = _ := by rw [hpow]
    _ ≤ _ := by
      unfold bvMeanPolynomial
      have hs : 0 ≤ Real.sqrt (T : ℝ) * (R : ℝ) ^ 2 := by positivity
      linarith

/-- The full Type II numerical budget, including its dyadic and coefficient
losses, is bounded by a fixed constant times `P log^6 T`.-/
theorem bvTypeIIBudget_le (T R : ℕ) (hT : 256 ≤ T)
    (hR : (R : ℝ) ≤ Real.sqrt (T : ℝ)) :
    bvTypeIIBudget T R ≤
      16 * (2 / Real.log 2) ^ 4 * bvMeanPolynomial T R * (Real.log (T : ℝ)) ^ 6 := by
  let l : ℝ := Real.log (T : ℝ)
  let a : ℝ := 2 / Real.log 2
  let B : ℝ := (T : ℝ) + (R : ℝ) * T *
      (1 / Real.sqrt ((bvInternalCutoff T : ℝ) / 2) +
        1 / Real.sqrt ((bvInternalCutoff T : ℝ) / 2)) +
      (R : ℝ) ^ 2 * Real.sqrt (T : ℝ)
  have hl0 : 0 ≤ l := Real.log_natCast_nonneg T
  have hB0 : 0 ≤ B := by dsimp only [B]; positivity
  have hL0 : 0 ≤ characterLargeSieveLogFactor R :=
    zero_le_one.trans (one_le_characterLargeSieveLogFactor R)
  have hD : (dyadicNatDepth T : ℝ) ≤ a * l := dyadicNatDepth_le_two_div_log_two_mul_log T hT
  have hD4 : (dyadicNatDepth T : ℝ) ^ 4 ≤ (a * l) ^ 4 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hD 4
  have hL : characterLargeSieveLogFactor R ≤ 2 * l := characterLargeSieveLogFactor_le_two_log T R hT hR
  have hB : B ≤ 4 * bvMeanPolynomial T R := bvInternalCutoff_polynomial_le_four T R hT
  have hcoef : 2 * (dyadicNatDepth T : ℝ) ^ 4 * l * characterLargeSieveLogFactor R ≤
      2 * (a * l) ^ 4 * l * (2 * l) :=
    mul_le_mul (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hD4 (by norm_num)) hl0) hL hL0 (by positivity)
  change 2 * (dyadicNatDepth T : ℝ) ^ 4 * l * characterLargeSieveLogFactor R * B ≤ _
  calc
    _ ≤ 2 * (a * l) ^ 4 * l * (2 * l) * (4 * bvMeanPolynomial T R) :=
      mul_le_mul hcoef hB hB0 (by positivity)
    _ = _ := by dsimp only [a, l]; ring

/-- Grouped absorption of the principal endpoint and both Vaughan budgets.-/
theorem bvMeanBudget_le (T R : ℕ) (hT : 256 ≤ T) (hRpos : 1 ≤ R)
    (hR : (R : ℝ) ≤ Real.sqrt (T : ℝ)) :
    (T : ℝ) * Real.log (T : ℝ) + bvTypeIBudget T R + bvTypeIIBudget T R ≤
      bvMeanConstant * bvMeanPolynomial T R * (Real.log (T : ℝ)) ^ 6 := by
  let l : ℝ := Real.log (T : ℝ)
  have hl1 : 1 ≤ l := one_le_log_of_256_le T hT
  have hl0 : 0 ≤ l := zero_le_one.trans hl1
  have hl6 : l ≤ l ^ 6 := by
    simpa only [pow_one] using pow_le_pow_right₀ hl1 (show (1 : ℕ) ≤ 6 by norm_num)
  have hl26 : l ^ 2 ≤ l ^ 6 := pow_le_pow_right₀ hl1 (by norm_num)
  have hP0 := bvMeanPolynomial_nonneg T R
  have h0 : (T : ℝ) * l ≤ bvMeanPolynomial T R * l ^ 6 :=
    mul_le_mul (bvMeanPolynomial_ge_endpoint T R) hl6 hl0 hP0
  have hI : bvTypeIBudget T R ≤ 4 * bvMeanPolynomial T R * l ^ 6 := by
    apply (bvTypeIBudget_le T R hT hRpos hR).trans
    have hs : 4 * (Real.sqrt (T : ℝ) * (R : ℝ) ^ 2) ≤ 4 * bvMeanPolynomial T R :=
      mul_le_mul_of_nonneg_left (bvMeanPolynomial_ge_modulus_sq T R) (by norm_num)
    have h := mul_le_mul hs hl26 (sq_nonneg l) (show 0 ≤ 4 * bvMeanPolynomial T R by positivity)
    simpa only [mul_assoc] using h
  have hII := bvTypeIIBudget_le T R hT hR
  calc
    _ ≤ bvMeanPolynomial T R * l ^ 6 + 4 * bvMeanPolynomial T R * l ^ 6 +
        16 * (2 / Real.log 2) ^ 4 * bvMeanPolynomial T R * l ^ 6 :=
      add_le_add (add_le_add h0 hI) hII
    _ = _ := by dsimp only [bvMeanConstant, l]; ring

/-- The fully expanded raw mean budget at the internal cutoff. Its left
side matches the finite Vaughan decomposition with `U = V = W`.-/
theorem bvInternalCutoff_mean_budget_le (T R : ℕ) (hT : 256 ≤ T) (hRpos : 1 ≤ R)
    (hR : (R : ℝ) ≤ Real.sqrt (T : ℝ)) :
    let W := bvInternalCutoff T
    (T : ℝ) * Real.log (T : ℝ) +
      2 * (W : ℝ) * (R : ℝ) ^ 2 * Real.sqrt (R : ℝ) * (1 + Real.log (R : ℝ)) * Real.log (T : ℝ) +
      ((W * W : ℕ) : ℝ) * Real.log ((W * W : ℕ) : ℝ) * (R : ℝ) ^ 2 *
        Real.sqrt (R : ℝ) * (1 + Real.log (R : ℝ)) +
      (W : ℝ) * Real.log (W : ℝ) * (R : ℝ) ^ 2 +
      2 * (dyadicNatDepth T : ℝ) ^ 4 * Real.log (T : ℝ) * characterLargeSieveLogFactor R *
        ((T : ℝ) + (R : ℝ) * T *
          (1 / Real.sqrt ((W : ℝ) / 2) + 1 / Real.sqrt ((W : ℝ) / 2)) +
          (R : ℝ) ^ 2 * Real.sqrt (T : ℝ)) ≤
      bvMeanConstant * bvMeanPolynomial T R * (Real.log (T : ℝ)) ^ 6 := by
  simpa only [bvTypeIBudget, bvTypeIIBudget, add_assoc] using bvMeanBudget_le T R hT hRpos hR

end TwinPrime.Analytic
