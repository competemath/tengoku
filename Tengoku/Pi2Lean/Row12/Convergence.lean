import Tengoku.Seed.Analysis.SpecificLimits.Normed
import Tengoku.Seed.Analysis.SpecialFunctions.Trigonometric.Basic
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Row12

noncomputable def coefficient (n : ℕ) : ℝ :=
  (Nat.factorial (6 * n) : ℝ) / (Nat.factorial n : ℝ) ^ 6 / (10 : ℝ) ^ (6 * n)

noncomputable def weight (n : ℕ) : ℝ :=
  532 * (n : ℝ) ^ 2 + 126 * (n : ℝ) + 9

noncomputable def term (n : ℕ) : ℝ :=
  (Nat.factorial (6 * n) : ℝ) / (Nat.factorial n : ℝ) ^ 6 *
    (532 * (n : ℝ) ^ 2 + 126 * (n : ℝ) + 9) / (10 : ℝ) ^ (6 * n)

noncomputable def rho : ℝ := 729 / 15625

/--
@isnad1 id=le.0h1v.s6.811f88932cc9 from=translated src=- shape=c7e46893 vocab=bf88f0e0
-/
theorem factorial_bound (n : ℕ) :
    Nat.factorial (6 * n) ≤ 6 ^ (6 * n) * (Nat.factorial n) ^ 6 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep : (6 * n + 1).ascFactorial 6 ≤ (6 * n + 6) ^ 6 :=
      Nat.ascFactorial_le_pow_add (6 * n) 6
    calc
      Nat.factorial (6 * (n + 1)) =
          Nat.factorial (6 * n) * (6 * n + 1).ascFactorial 6 := by
        rw [Nat.factorial_mul_ascFactorial]
        congr 1
      _ ≤ Nat.factorial (6 * n) * (6 * n + 6) ^ 6 := Nat.mul_le_mul_left _ hstep
      _ ≤ (6 ^ (6 * n) * (Nat.factorial n) ^ 6) * (6 * n + 6) ^ 6 :=
        Nat.mul_le_mul_right _ ih
      _ = 6 ^ (6 * (n + 1)) * (Nat.factorial (n + 1)) ^ 6 := by
        rw [show 6 * (n + 1) = 6 * n + 6 by omega, pow_add, Nat.factorial_succ]
        ring

/--
@isnad1 id=le.0h1v.s3.0502a35a4afa from=translated src=- shape=b9369acb vocab=50e716a1
-/
theorem coefficient_nonneg (n : ℕ) : 0 ≤ coefficient n := by
  unfold coefficient
  positivity

/--
@isnad1 id=le.0h1v.s4.d80ba6d5466c from=translated src=- shape=b217b3a9 vocab=6045e224
-/
theorem coefficient_le_geometric (n : ℕ) : coefficient n ≤ rho ^ n := by
  have hfac : (0 : ℝ) < (Nat.factorial n : ℝ) ^ 6 := by positivity
  have hbound : (Nat.factorial (6 * n) : ℝ) / (Nat.factorial n : ℝ) ^ 6 ≤
      (6 : ℝ) ^ (6 * n) := by
    apply (div_le_iff₀ hfac).2
    exact_mod_cast factorial_bound n
  calc
    coefficient n ≤ (6 : ℝ) ^ (6 * n) / (10 : ℝ) ^ (6 * n) := by
      exact div_le_div_of_nonneg_right hbound (by positivity)
    _ = rho ^ n := by
      rw [pow_mul, pow_mul, ← div_pow]
      norm_num [rho]

/--
@isnad1 id=eq.0h1v.s4.4c89c5050080 from=translated src=- shape=c45662b3 vocab=2de9b9eb
-/
theorem term_eq_coefficient_mul_weight (n : ℕ) : term n = coefficient n * weight n := by
  unfold term coefficient weight
  ring

/--
@isnad1 id=le.0h1v.s3.8f4cf7f51a3f from=translated src=- shape=b9369acb vocab=034f64e2
-/
theorem term_nonneg (n : ℕ) : 0 ≤ term n := by
  unfold term
  positivity

/--
@isnad1 id=summable.0h0v.s3.4e786fc48055 from=translated src=- shape=ef4b497d vocab=52f1e2c3
-/
theorem term_summable : Summable term := by
  have hr : ‖rho‖ < 1 := by norm_num [rho, Real.norm_eq_abs]
  have h2 := (summable_pow_mul_geometric_of_norm_lt_one 2 hr).mul_left (532 : ℝ)
  have h1 := (summable_pow_mul_geometric_of_norm_lt_one 1 hr).mul_left (126 : ℝ)
  have h0 := (summable_geometric_of_norm_lt_one hr).mul_left (9 : ℝ)
  have hmajor : Summable (fun n : ℕ => weight n * rho ^ n) := by
    exact ((h2.add h1).add h0).congr (fun n => by
      simp only [weight, pow_one]
      ring)
  apply Summable.of_nonneg_of_le term_nonneg _ hmajor
  intro n
  rw [term_eq_coefficient_mul_weight]
  have hw : 0 ≤ weight n := by unfold weight; positivity
  nlinarith [coefficient_le_geometric n]

/--
@isnad1 id=hassum.0h0v.s4.62d0080f559a from=translated src=- shape=bf6be8ff vocab=d394ffcf
-/
theorem term_hasSum : HasSum term (∑' n : ℕ, term n) := term_summable.hasSum

end Row12
