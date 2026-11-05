module

public import Tengoku.Seed.NumberTheory.LSeries.HurwitzZetaOdd
import Tengoku.Seed.CategoryTheory.Category.Init
import Tengoku.Seed.Combinatorics.Matroid.Init
import Tengoku.Seed.NumberTheory.ArithmeticFunction.Misc

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Trigonometric and Abel-summation lemmas for `LValueAtOne`

This file collects the residue-class rewrites and complex logarithm boundary
identities shared by the odd and even `L(1, χ)` formulas.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Topology

namespace KummerCriterion

section LValueAtOne

variable (p : ℕ) [hp : Fact p.Prime]

/-- For a nonzero residue `a: ZMod p`, the standard real representative lies
strictly between `0` and `1` after dividing by `p`.-/
lemma zmod_val_div_prime_mem_Ioo {a : ZMod p} (ha : a ≠ 0) :
    (a.val / p : ℝ) ∈ Set.Ioo 0 1 := by
  have hp_pos : 0 < p := hp.out.pos
  have hval_pos : 0 < a.val := by
    by_contra h
    have hval_zero : a.val = 0 := Nat.eq_zero_of_not_pos h
    exact ha <| (ZMod.val_eq_zero a).mp hval_zero
  refine Set.mem_Ioo.mpr ⟨?_, ?_⟩
  · exact div_pos (Nat.cast_pos.mpr hval_pos) (Nat.cast_pos.mpr hp_pos)
  · exact (div_lt_one (Nat.cast_pos.mpr hp_pos)).2 <| Nat.cast_lt.mpr (ZMod.val_lt a)

/-- Rewrite `sinZeta` at `ZMod.toAddCircle a` using the standard real
representative `a.val / p`.-/
lemma sinZeta_toAddCircle_eq_val_div_prime (a : ZMod p) (s : ℂ) :
    HurwitzZeta.sinZeta (ZMod.toAddCircle a) s = HurwitzZeta.sinZeta (a.val / p : ℝ) s := by
  rw [ZMod.toAddCircle_apply]

/-- The unit-circle point with argument `2πx` is nontrivial when `0 < x < 1`.-/
lemma exp_two_pi_mul_I_ne_one {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) :
    Complex.exp ((2 * Real.pi * x) * Complex.I) ≠ 1 := by
  intro hexp
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp hexp
  have him : 2 * Real.pi * x = (m : ℝ) * (2 * Real.pi) := by
    simpa using congrArg Complex.im hm
  have hm_pos : (0 : ℝ) < m := by nlinarith [Real.pi_pos, hx₀, him]
  have hm_lt_one : (m : ℝ) < 1 := by nlinarith [Real.pi_pos, hx₁, him]
  have hm_pos_int : 0 < m := by exact_mod_cast hm_pos
  have hm_lt_one_int : m < 1 := by exact_mod_cast hm_lt_one
  omega

/-- Multiplying a unit-circle exponential by a nonnegative real scales its
norm by that real.-/
lemma norm_real_mul_exp_two_pi_mul_I (x : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    ‖(r : ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I)‖ = r := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr]
  rw [show ‖Complex.exp ((2 * Real.pi * x) * Complex.I)‖ = 1 by
    simpa [mul_assoc] using Complex.norm_exp_ofReal_mul_I (2 * Real.pi * x)]
  simp

/-- Partial sums of powers of a nontrivial unit complex number are bounded by
`2 / ‖z - 1‖`.-/
lemma norm_geom_sum_le_two_div_norm_sub_one {z : ℂ} (hz_norm : ‖z‖ = 1)
    (hz_ne_one : z ≠ 1) (n : ℕ) :
    ‖∑ i ∈ Finset.range n, z ^ i‖ ≤ 2 / ‖z - 1‖ := by
  calc
    ‖∑ i ∈ Finset.range n, z ^ i‖ = ‖(z ^ n - 1) / (z - 1)‖ := by
      rw [geom_sum_eq hz_ne_one]
    _ = ‖z ^ n - 1‖ / ‖z - 1‖ := by rw [Complex.norm_div]
    _ ≤ 2 / ‖z - 1‖ := by
      have hden : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz_ne_one)
      have hnum : ‖z ^ n - 1‖ ≤ 2 := by
        calc
          ‖z ^ n - 1‖ ≤ ‖z ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
          _ = 1 + 1 := by rw [norm_pow, hz_norm]; simp
          _ = 2 := by norm_num
      simpa [div_eq_mul_inv] using
        mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr hden.le)

/-- The reciprocal chord-length bound used for trigonometric partial sums.-/
lemma one_le_two_div_norm_one_sub_exp_two_pi_mul_I {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) :
    1 ≤ 2 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ := by
  have hnorm : ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ ≤ 2 := by
    calc
      ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖
          ≤ ‖(1 : ℂ)‖ + ‖Complex.exp ((2 * Real.pi * x) * Complex.I)‖ := norm_sub_le _ _
      _ = 1 + 1 := by
        rw [norm_one]
        simpa [mul_assoc] using Complex.norm_exp_ofReal_mul_I (2 * Real.pi * x)
      _ = 2 := by norm_num
  have hzero : (1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I) ≠ 0 :=
    sub_ne_zero.mpr (exp_two_pi_mul_I_ne_one hx₀ hx₁).symm
  have hden_pos : 0 < ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ :=
    norm_pos_iff.mpr hzero
  simpa using (one_le_div hden_pos).2 hnorm

/-- Rewriting `1 - e^{it}` in polar form on the upper unit semicircle.-/
lemma one_sub_exp_ofReal_mul_I (t : ℝ) :
    (1 : ℂ) - Complex.exp (t * Complex.I) =
      (2 * Real.sin (t / 2) : ℝ) *
        (Real.cos (t / 2 - Real.pi / 2) + Real.sin (t / 2 - Real.pi / 2) * Complex.I) := by
  calc
    (1 : ℂ) - Complex.exp (t * Complex.I)
        = ((1 - Real.cos t : ℝ) : ℂ) + (-Real.sin t : ℝ) * Complex.I := by
            rw [Complex.exp_ofReal_mul_I]
            simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    _ = ((2 * Real.sin (t / 2) ^ 2 : ℝ) : ℂ) +
          (-(2 * Real.sin (t / 2) * Real.cos (t / 2)) : ℝ) * Complex.I := by
            rw [show t = 2 * (t / 2) by ring, Real.cos_two_mul, Real.sin_two_mul]
            have hsq : 1 - (2 * Real.cos (t / 2) ^ 2 - 1) = 2 * Real.sin (t / 2) ^ 2 := by
              nlinarith [Real.sin_sq_add_cos_sq (t / 2)]
            rw [hsq]
            ring_nf
    _ = (2 * Real.sin (t / 2) : ℝ) *
          (Real.cos (t / 2 - Real.pi / 2) + Real.sin (t / 2 - Real.pi / 2) * Complex.I) := by
            simp [Real.cos_sub_pi_div_two, Real.sin_sub_pi_div_two, sq]
            ring

/-- The principal argument of `1 - e^{it}` for `0 < t < 2π`.-/
lemma arg_one_sub_exp_ofReal_mul_I {t : ℝ} (ht₀ : 0 < t) (ht₂π : t < 2 * Real.pi) :
    Complex.arg ((1 : ℂ) - Complex.exp (t * Complex.I)) = t / 2 - Real.pi / 2 := by
  have hs : 0 < 2 * Real.sin (t / 2) := by
    have hhalf : 0 < t / 2 ∧ t / 2 < Real.pi := by
      constructor <;> nlinarith [ht₀, ht₂π, Real.pi_pos]
    have hsin : 0 < Real.sin (t / 2) := Real.sin_pos_of_mem_Ioo hhalf
    positivity
  have hθ : t / 2 - Real.pi / 2 ∈ Set.Ioc (-Real.pi) Real.pi := by
    constructor
    · nlinarith [ht₀, Real.pi_pos]
    · nlinarith [ht₂π]
  rw [one_sub_exp_ofReal_mul_I]
  simpa using (Complex.arg_mul_cos_add_sin_mul_I hs hθ)

/-- The logarithm in the Abel sum formula has the expected boundary imaginary part.-/
lemma neg_log_one_sub_exp_ofReal_mul_I_im {t : ℝ} (ht₀ : 0 < t) (ht₂π : t < 2 * Real.pi) :
    (-Complex.log ((1 : ℂ) - Complex.exp (t * Complex.I))).im = Real.pi / 2 - t / 2 := by
  rw [show (-Complex.log ((1 : ℂ) - Complex.exp (t * Complex.I))).im =
      -(Complex.log ((1 : ℂ) - Complex.exp (t * Complex.I))).im by simp]
  rw [Complex.log_im, arg_one_sub_exp_ofReal_mul_I ht₀ ht₂π]
  ring

/-- Abel summation identity for the damped sine series attached to `sinZeta` at `s = 1`.-/
lemma hasSum_mul_rpow_sin (x r : ℝ) (hr₀ : 0 ≤ r) (hr₁ : r < 1) :
    HasSum (fun n : ℕ => (r ^ n / n) * Real.sin (2 * Real.pi * x * n))
      (-Complex.log ((1 : ℂ) - (r : ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I))).im := by
  let z : ℂ := (r : ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I)
  have hz : ‖z‖ < 1 := by
    rw [show ‖z‖ = r by simpa [z] using norm_real_mul_exp_two_pi_mul_I x hr₀]
    exact hr₁
  refine (Complex.hasSum_im (Complex.hasSum_taylorSeries_neg_log hz)).congr_fun ?_
  intro n
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [z]
  · rw [show z = (r : ℂ) * Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I) by simp [z]]
    rw [Complex.div_natCast_im, mul_pow, Complex.mul_im, ← Complex.ofReal_pow, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, ← Complex.exp_nat_mul]
    rw [show (n : ℂ) * ((2 * Real.pi * x : ℝ) * Complex.I) =
        ((2 * Real.pi * x * n : ℝ) : ℂ) * Complex.I by
          norm_num
          ring]
    rw [Complex.exp_ofReal_mul_I_im]
    ring

/-- Abel summation identity for the damped cosine series attached to `cosZeta` at `s = 1`.-/
lemma hasSum_mul_rpow_cos (x r : ℝ) (hr₀ : 0 ≤ r) (hr₁ : r < 1) :
    HasSum (fun n : ℕ => (r ^ n / n) * Real.cos (2 * Real.pi * x * n))
      (-Real.log ‖(1 : ℂ) - (r : ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I)‖) := by
  let z : ℂ := (r : ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I)
  have hz : ‖z‖ < 1 := by
    rw [show ‖z‖ = r by simpa [z] using norm_real_mul_exp_two_pi_mul_I x hr₀]
    exact hr₁
  have hsum :
      HasSum (fun n : ℕ => (z ^ n / n).re) (-Complex.log ((1 : ℂ) - z)).re :=
    (Complex.hasSum_re (Complex.hasSum_taylorSeries_neg_log hz))
  have hsum' :
      HasSum (fun n : ℕ => (r ^ n / n) * Real.cos (2 * Real.pi * x * n))
        (-Complex.log ((1 : ℂ) - z)).re := by
    refine hsum.congr_fun ?_
    intro n
    rcases n.eq_zero_or_pos with rfl | hn
    · simp [z]
    · rw [show z = (r : ℂ) * Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I) by simp [z]]
      rw [Complex.div_natCast_re, mul_pow, Complex.mul_re, ← Complex.ofReal_pow,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, ← Complex.exp_nat_mul]
      rw [show (n : ℂ) * ((2 * Real.pi * x : ℝ) * Complex.I) =
          ((2 * Real.pi * x * n : ℝ) : ℂ) * Complex.I by
            norm_num
            ring]
      rw [Complex.exp_ofReal_mul_I_re]
      ring
  have hvalue : (-Complex.log ((1 : ℂ) - z)).re = -Real.log ‖(1 : ℂ) - z‖ := by
    simpa using congrArg Neg.neg (Complex.log_re ((1 : ℂ) - z))
  simpa [hvalue, z] using hsum'

/-- The norm of `1 - e^{it}` on the upper unit semicircle.-/
lemma norm_one_sub_exp_ofReal_mul_I {t : ℝ} (ht₀ : 0 < t) (ht₂π : t < 2 * Real.pi) :
    ‖(1 : ℂ) - Complex.exp (t * Complex.I)‖ = 2 * Real.sin (t / 2) := by
  rw [← norm_neg, neg_sub, mul_comm, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs,
    abs_of_pos (mul_pos two_pos (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)))]

end LValueAtOne

end KummerCriterion
