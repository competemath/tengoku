import Tengoku.Twinprime.TwinPrime.Analytic.MiddlePrimeIntegral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# An exact numerical certificate for the middle-prime sieve constant

The upper estimate for the logarithm is proved by differentiation.  The
final comparison then uses rational arithmetic, at a fixed distribution
power strictly below one half.
-/

noncomputable section

open Set MeasureTheory

namespace TwinPrime.Analytic

def middlePrimeSieveMainConstant (a v : ℝ) : ℝ :=
  2 * ((1 / a) * Real.log (v / (1 / 5)) +
    ((1 - a) / a) * Real.log ((a - 1 / 5) / (a - v)))

theorem middlePrimeSieveMainConstant_eq_integral (a v : ℝ)
    (hv : (1 / 5 : ℝ) ≤ v) (hva : v < a) :
    middlePrimeSieveMainConstant a v =
      2 * ∫ t in (1 / 5 : ℝ)..v, middlePrimeIntegrand a t := by
  rw [integral_middlePrimeIntegrand a (1 / 5) v (by norm_num) hv hva]
  rfl

/-- The degree-three alternating logarithm polynomial is an upper bound
on the full nonnegative half-line.-/
theorem log_one_add_le_cubic (x : ℝ) (hx : 0 ≤ x) :
    Real.log (1 + x) ≤ x - x ^ 2 / 2 + x ^ 3 / 3 := by
  let F : ℝ → ℝ := fun t => t - t ^ 2 / 2 + t ^ 3 / 3 - Real.log (1 + t)
  have hderiv (t : ℝ) (ht : 0 ≤ t) : HasDerivAt F (t ^ 3 / (1 + t)) t := by
    have ht1 : 1 + t ≠ 0 := by positivity
    have h := (((hasDerivAt_id t).sub (((hasDerivAt_id t).pow 2).div_const 2)).add
      (((hasDerivAt_id t).pow 3).div_const 3)).sub
      (((hasDerivAt_id t).const_add 1).log ht1)
    convert! h using 1
    dsimp
    field_simp
    ring
  have hmono : MonotoneOn F (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · intro t ht
      exact (hderiv t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hderiv t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht0 : 0 ≤ t := interior_subset ht
      rw [(hderiv t ht0).deriv]
      positivity
  have h := hmono (by simp) hx hx
  dsimp [F] at h
  simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    zero_pow (by norm_num : (3 : ℕ) ≠ 0), zero_div, sub_zero, zero_add,
    add_zero, Real.log_one, zero_sub, sub_nonneg] using h

/-- The exact fixed-power coefficient is below 0.263.  All constants and
all logarithm arguments are rational; no floating-point estimate enters.-/
theorem middlePrimeSieveMainConstant_fixed_lt :
    middlePrimeSieveMainConstant (49999 / 100000) (21 / 100) < 263 / 1000 := by
  have h₁ := log_one_add_le_cubic (1 / 20) (by norm_num)
  have h₂ := log_one_add_le_cubic (1000 / 28999) (by norm_num)
  norm_num at h₁ h₂
  unfold middlePrimeSieveMainConstant
  norm_num
  have hmain :
      2 * ((100000 / 49999 : ℝ) * Real.log (21 / 20) +
        (50001 / 49999 : ℝ) * Real.log (29999 / 28999)) ≤
      961951827676901725 / 3657898403618589003 := by
    calc
      _ ≤ 2 * ((100000 / 49999 : ℝ) * (1171 / 24000) +
          (50001 / 49999 : ℝ) * (2480327503000 / 73159431260997)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact add_le_add
          (mul_le_mul_of_nonneg_left h₁ (by norm_num))
          (mul_le_mul_of_nonneg_left h₂ (by norm_num))
      _ = _ := by norm_num
  exact hmain.trans_lt (by norm_num)

end TwinPrime.Analytic
