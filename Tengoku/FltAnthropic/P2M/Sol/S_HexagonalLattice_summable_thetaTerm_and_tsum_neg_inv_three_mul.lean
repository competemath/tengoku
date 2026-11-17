import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HexagonalLattice_summable_thetaTerm_and_tsum_neg_inv_three_mul.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HexagonalLattice_summable_thetaTerm_and_tsum_neg_inv_three_mul.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HexagonalLattice_summable_thetaTerm_and_tsum_neg_inv_three_mul

set_option autoImplicit false

open Complex Real

open scoped Topology

namespace A2HexPoisson

noncomputable section

def hexThetaTerm (σ : ℂ) (p : ℤ × ℤ) : ℂ :=
  cexp (2 * π * I * σ * ((p.1 : ℂ) ^ 2 + (p.1 : ℂ) * (p.2 : ℂ) + (p.2 : ℂ) ^ 2))

def hexTheta (σ : ℂ) : ℂ :=
  ∑' p : ℤ × ℤ, hexThetaTerm σ p

/--
@isnad1 id=eq.0h3v.s4.2b7ccedf644e from=translated src=- shape=f6ae3939 vocab=a2740bb7
-/
lemma hexThetaTerm_swap (σ : ℂ) (x y : ℤ) :
    hexThetaTerm σ (x, y) = hexThetaTerm σ (y, x) := by
  unfold hexThetaTerm
  congr 1
  push_cast
  ring

/--
@isnad1 id=eq.0h2v.s7.874588abf793 from=translated src=- shape=8d8df624 vocab=20cba5d3
-/
lemma norm_hexThetaTerm (σ : ℂ) (p : ℤ × ℤ) :
    ‖hexThetaTerm σ p‖ =
      rexp (-(2 * π * σ.im) * ((p.1 : ℝ) ^ 2 + (p.1 : ℝ) * (p.2 : ℝ) + (p.2 : ℝ) ^ 2)) := by
  rw [hexThetaTerm, Complex.norm_exp]
  congr 1
  rw [show (2 * (π : ℂ) * I * σ * ((p.1 : ℂ) ^ 2 + (p.1 : ℂ) * (p.2 : ℂ) + (p.2 : ℂ) ^ 2)) =
      (((2 * π * ((p.1 : ℝ) ^ 2 + (p.1 : ℝ) * (p.2 : ℝ) + (p.2 : ℝ) ^ 2) : ℝ)) : ℂ) * (σ * I) by
    push_cast; ring]
  rw [Complex.re_ofReal_mul, Complex.mul_I_re]
  ring

/--
@isnad1 id=le.0h2v.s6.75667d9ee366 from=translated src=- shape=86f79774 vocab=cef4cf1d
-/
lemma sq_add_sq_le_two_mul_form (x y : ℝ) :
    x ^ 2 + y ^ 2 ≤ 2 * (x ^ 2 + x * y + y ^ 2) := by
  nlinarith [sq_nonneg (x + y)]

/--
@isnad1 id=summable.1h2v.s6.23947a574d2f from=translated src=- shape=340fcc67 vocab=3647cd27
-/
lemma summable_norm_cexp_neg_quadratic {a : ℂ} (ha : 0 < a.re) (b : ℂ) :
    Summable fun n : ℤ => ‖cexp (-π * a * (n : ℂ) ^ 2 + 2 * π * b * (n : ℂ))‖ := by
  rw [summable_norm_iff]
  have hre : (-(π : ℂ) * a).re < 0 := by
    rw [neg_mul, neg_re, Complex.re_ofReal_mul, neg_lt_zero]
    exact mul_pos pi_pos ha
  have hO : (fun x : ℝ => cexp (-(π : ℂ) * a * (x : ℂ) ^ 2 + 2 * π * b * (x : ℂ)))
      =O[Filter.cocompact ℝ] fun x : ℝ => |x| ^ (-2 : ℝ) :=
    (cexp_neg_quadratic_isLittleO_abs_rpow_cocompact hre (2 * π * b) (-2)).isBigO
  have hZ := hO.comp_tendsto Int.tendsto_coe_cofinite
  simp only [Function.comp_def, Complex.ofReal_intCast] at hZ
  exact summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two) hZ

/--
@isnad1 id=summable.1h1v.s5.5b8573b29b41 from=translated src=- shape=f3594e1b vocab=0137c2a1
-/
lemma summable_rexp_neg_mul_int_sq {c : ℝ} (hc : 0 < c) :
    Summable fun n : ℤ => rexp (-(c * (n : ℝ) ^ 2)) := by
  have h0 : (0 : ℝ) < ((c / π : ℝ) : ℂ).re := by
    rw [Complex.ofReal_re]
    exact div_pos hc pi_pos
  refine (summable_norm_cexp_neg_quadratic h0 0).congr fun n => ?_
  rw [mul_zero, zero_mul, add_zero, Complex.norm_exp]
  congr 1
  rw [show (-(π : ℂ) * ((c / π : ℝ) : ℂ) * (n : ℂ) ^ 2) = ((-(c * (n : ℝ) ^ 2) : ℝ) : ℂ) by
    push_cast
    field_simp]
  exact Complex.ofReal_re _

/--
@isnad1 id=summable.1h1v.s5.1aaee711cdde from=translated src=- shape=d2cf2fee vocab=c00fecf3
-/
lemma summable_hexThetaTerm {σ : ℂ} (hσ : 0 < σ.im) : Summable (hexThetaTerm σ) := by
  apply Summable.of_norm
  have hbound : ∀ p : ℤ × ℤ, ‖hexThetaTerm σ p‖ ≤
      rexp (-(π * σ.im * (p.1 : ℝ) ^ 2)) * rexp (-(π * σ.im * (p.2 : ℝ) ^ 2)) := by
    intro p
    rw [norm_hexThetaTerm, ← Real.exp_add, Real.exp_le_exp]
    nlinarith [sq_add_sq_le_two_mul_form (p.1 : ℝ) (p.2 : ℝ), mul_pos pi_pos hσ]
  exact Summable.of_nonneg_of_le (fun p => norm_nonneg _) hbound
    (Summable.mul_of_nonneg
      (summable_rexp_neg_mul_int_sq (mul_pos pi_pos hσ))
      (summable_rexp_neg_mul_int_sq (mul_pos pi_pos hσ))
      (fun n => (Real.exp_pos _).le) (fun n => (Real.exp_pos _).le))

/--
@isnad1 id=ne.1h1v.s4.b6cf537274cc from=translated src=- shape=2154ac66 vocab=3c72e7c9
-/
lemma ne_zero_of_im_pos {σ : ℂ} (hσ : 0 < σ.im) : σ ≠ 0 := by
  rintro rfl
  simp at hσ

/--
@isnad1 id=lt.1h1v.s5.42944671f302 from=translated src=- shape=88db4cda vocab=20df8abe
-/
lemma re_neg_two_I_mul {σ : ℂ} (hσ : 0 < σ.im) : 0 < (-2 * I * σ).re := by
  rw [show (-2 * I * σ : ℂ) = ((-2 : ℝ) : ℂ) * (σ * I) by push_cast; ring,
    Complex.re_ofReal_mul, Complex.mul_I_re]
  linarith

/--
@isnad1 id=lt.1h1v.s6.48809229a9c5 from=translated src=- shape=b7f1ff54 vocab=44219891
-/
lemma re_neg_three_I_mul_div_two {σ : ℂ} (hσ : 0 < σ.im) : 0 < (-3 * I * σ / 2).re := by
  rw [show (-3 * I * σ / 2 : ℂ) = ((-3 / 2 : ℝ) : ℂ) * (σ * I) by push_cast; ring,
    Complex.re_ofReal_mul, Complex.mul_I_re]
  linarith

/--
@isnad1 id=lt.1h1v.s5.7327e937ddcc from=translated src=- shape=3766181f vocab=2c79fcc4
-/
lemma im_neg_one_div_three_mul_pos {σ : ℂ} (hσ : 0 < σ.im) : 0 < (-1 / (3 * σ)).im := by
  have h3σ : (3 : ℂ) * σ ≠ 0 := mul_ne_zero (by norm_num) (ne_zero_of_im_pos hσ)
  have him : ((3 : ℂ) * σ).im = 3 * σ.im := by
    simp [Complex.mul_im]
  rw [show (-1 / (3 * σ) : ℂ) = -((3 : ℂ) * σ)⁻¹ by rw [neg_div, one_div]]
  rw [Complex.neg_im, Complex.inv_im, neg_div, neg_neg, him]
  exact div_pos (by linarith) (Complex.normSq_pos.mpr h3σ)

/--
@isnad1 id=eq.1h1v.s6.fa3b8c512d4c from=translated src=- shape=d0e70757 vocab=556b818f
-/
lemma neg_pi_div_neg_two_I_mul {σ : ℂ} (hσ : σ ≠ 0) :
    -(π : ℂ) / (-2 * I * σ) = -((π : ℂ) * I) / (2 * σ) := by
  rw [div_eq_div_iff (mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) hσ)
    (mul_ne_zero (by norm_num) hσ)]
  linear_combination (-2 * (π : ℂ) * σ) * Complex.I_sq

/--
@isnad1 id=eq.1h1v.s6.32cb9a9da8b0 from=translated src=- shape=1de98fb6 vocab=556b818f
-/
lemma neg_pi_div_neg_three_I_mul_div_two {σ : ℂ} (hσ : σ ≠ 0) :
    -(π : ℂ) / (-3 * I * σ / 2) = -(2 * (π : ℂ) * I) / (3 * σ) := by
  rw [div_eq_div_iff
    (div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) hσ) (by norm_num))
    (mul_ne_zero (by norm_num) hσ)]
  linear_combination (-3 * (π : ℂ) * σ) * Complex.I_sq

/--
@isnad1 id=eq.0h3v.s8.bc2fb63e3713 from=translated src=- shape=a5b6f997 vocab=63d32d8e
-/
lemma exponent_initial (σ : ℂ) (x y : ℤ) :
    2 * π * I * σ * ((x : ℂ) ^ 2 + (x : ℂ) * (y : ℂ) + (y : ℂ) ^ 2) =
      2 * π * I * σ * (x : ℂ) ^ 2 +
        (-π * (-2 * I * σ) * (y : ℂ) ^ 2 + 2 * π * (I * σ * (x : ℂ)) * (y : ℂ)) := by
  ring

/--
@isnad1 id=eq.1h3v.s8.41c0b874dd03 from=translated src=- shape=06447903 vocab=789ed919
-/
lemma exponent_split {σ : ℂ} (hσ : σ ≠ 0) (x m : ℤ) :
    2 * π * I * σ * (x : ℂ) ^ 2 +
        -π / (-2 * I * σ) * ((m : ℂ) + I * (I * σ * (x : ℂ))) ^ 2 =
      (-π * (-3 * I * σ / 2) * (x : ℂ) ^ 2 + 2 * π * (I * (m : ℂ) / 2) * (x : ℂ)) +
        -π / (-2 * I * σ) * (m : ℂ) ^ 2 := by
  rw [show I * (I * σ * (x : ℂ)) = -(σ * (x : ℂ)) by
    linear_combination (σ * (x : ℂ)) * Complex.I_sq, neg_pi_div_neg_two_I_mul hσ]
  field_simp
  ring

/--
@isnad1 id=eq.1h3v.s8.ed7446489010 from=translated src=- shape=289efa10 vocab=789ed919
-/
lemma exponent_total {σ : ℂ} (hσ : σ ≠ 0) (m k : ℤ) :
    -π / (-2 * I * σ) * (m : ℂ) ^ 2 +
        -π / (-3 * I * σ / 2) * ((k : ℂ) + I * (I * (m : ℂ) / 2)) ^ 2 =
      2 * π * I * (-1 / (3 * σ)) *
        ((k : ℂ) ^ 2 + (k : ℂ) * (-(m : ℂ)) + (-(m : ℂ)) ^ 2) := by
  rw [show I * (I * (m : ℂ) / 2) = -((m : ℂ) / 2) by
    linear_combination ((m : ℂ) / 2) * Complex.I_sq, neg_pi_div_neg_two_I_mul hσ,
    neg_pi_div_neg_three_I_mul_div_two hσ]
  field_simp
  ring

/--
@isnad1 id=eq.1h2v.s8.bd4998e3e32f from=translated src=- shape=18e34358 vocab=da88d487
-/
lemma inner_poisson {σ : ℂ} (hσ : 0 < σ.im) (x : ℤ) :
    (∑' y : ℤ, hexThetaTerm σ (x, y)) =
      1 / (-2 * I * σ) ^ (1 / 2 : ℂ) *
        ∑' m : ℤ,
          (cexp (-π * (-3 * I * σ / 2) * (x : ℂ) ^ 2 + 2 * π * (I * (m : ℂ) / 2) * (x : ℂ)) *
            cexp (-π / (-2 * I * σ) * (m : ℂ) ^ 2)) := by
  have ha : 0 < (-2 * I * σ).re := re_neg_two_I_mul hσ
  have hσ0 : σ ≠ 0 := ne_zero_of_im_pos hσ
  calc
    (∑' y : ℤ, hexThetaTerm σ (x, y)) =
        ∑' y : ℤ, cexp (2 * π * I * σ * (x : ℂ) ^ 2) *
          cexp (-π * (-2 * I * σ) * (y : ℂ) ^ 2 + 2 * π * (I * σ * (x : ℂ)) * (y : ℂ)) := by
      refine tsum_congr fun y => ?_
      rw [hexThetaTerm, ← Complex.exp_add]
      exact congrArg cexp (exponent_initial σ x y)
    _ = cexp (2 * π * I * σ * (x : ℂ) ^ 2) *
        ∑' y : ℤ, cexp (-π * (-2 * I * σ) * (y : ℂ) ^ 2 + 2 * π * (I * σ * (x : ℂ)) * (y : ℂ)) :=
      tsum_mul_left
    _ = cexp (2 * π * I * σ * (x : ℂ) ^ 2) *
        (1 / (-2 * I * σ) ^ (1 / 2 : ℂ) *
          ∑' m : ℤ, cexp (-π / (-2 * I * σ) * ((m : ℂ) + I * (I * σ * (x : ℂ))) ^ 2)) := by
      rw [Complex.tsum_exp_neg_quadratic ha (I * σ * (x : ℂ))]
    _ = 1 / (-2 * I * σ) ^ (1 / 2 : ℂ) *
        ∑' m : ℤ, cexp (2 * π * I * σ * (x : ℂ) ^ 2) *
          cexp (-π / (-2 * I * σ) * ((m : ℂ) + I * (I * σ * (x : ℂ))) ^ 2) := by
      rw [tsum_mul_left]
      ring
    _ = 1 / (-2 * I * σ) ^ (1 / 2 : ℂ) *
        ∑' m : ℤ,
          (cexp (-π * (-3 * I * σ / 2) * (x : ℂ) ^ 2 + 2 * π * (I * (m : ℂ) / 2) * (x : ℂ)) *
            cexp (-π / (-2 * I * σ) * (m : ℂ) ^ 2)) := by
      congr 1
      refine tsum_congr fun m => ?_
      rw [← Complex.exp_add, ← Complex.exp_add]
      exact congrArg cexp (exponent_split hσ0 x m)

/--
@isnad1 id=eq.1h2v.s8.d2bb32a3875b from=translated src=- shape=dd36b7f0 vocab=da88d487
-/
lemma outer_poisson {σ : ℂ} (hσ : 0 < σ.im) (m : ℤ) :
    (∑' x : ℤ,
        (cexp (-π * (-3 * I * σ / 2) * (x : ℂ) ^ 2 + 2 * π * (I * (m : ℂ) / 2) * (x : ℂ)) *
          cexp (-π / (-2 * I * σ) * (m : ℂ) ^ 2))) =
      1 / (-3 * I * σ / 2) ^ (1 / 2 : ℂ) *
        ∑' k : ℤ, hexThetaTerm (-1 / (3 * σ)) (k, -m) := by
  have ha : 0 < (-3 * I * σ / 2).re := re_neg_three_I_mul_div_two hσ
  have hσ0 : σ ≠ 0 := ne_zero_of_im_pos hσ
  calc
    (∑' x : ℤ,
        (cexp (-π * (-3 * I * σ / 2) * (x : ℂ) ^ 2 + 2 * π * (I * (m : ℂ) / 2) * (x : ℂ)) *
          cexp (-π / (-2 * I * σ) * (m : ℂ) ^ 2))) =
        (∑' x : ℤ,
          cexp (-π * (-3 * I * σ / 2) * (x : ℂ) ^ 2 + 2 * π * (I * (m : ℂ) / 2) * (x : ℂ))) *
          cexp (-π / (-2 * I * σ) * (m : ℂ) ^ 2) :=
      tsum_mul_right
    _ = (1 / (-3 * I * σ / 2) ^ (1 / 2 : ℂ) *
          ∑' k : ℤ, cexp (-π / (-3 * I * σ / 2) * ((k : ℂ) + I * (I * (m : ℂ) / 2)) ^ 2)) *
          cexp (-π / (-2 * I * σ) * (m : ℂ) ^ 2) := by
      rw [Complex.tsum_exp_neg_quadratic ha (I * (m : ℂ) / 2)]
    _ = 1 / (-3 * I * σ / 2) ^ (1 / 2 : ℂ) *
          ∑' k : ℤ, cexp (-π / (-2 * I * σ) * (m : ℂ) ^ 2) *
            cexp (-π / (-3 * I * σ / 2) * ((k : ℂ) + I * (I * (m : ℂ) / 2)) ^ 2) := by
      rw [tsum_mul_left]
      ring
    _ = 1 / (-3 * I * σ / 2) ^ (1 / 2 : ℂ) *
          ∑' k : ℤ, hexThetaTerm (-1 / (3 * σ)) (k, -m) := by
      congr 1
      refine tsum_congr fun k => ?_
      rw [← Complex.exp_add, hexThetaTerm]
      refine congrArg cexp ?_
      push_cast
      exact exponent_total hσ0 m k

/--
@isnad1 id=summable.1h1v.s8.7a0e82780397 from=translated src=- shape=7d51eed5 vocab=70eab4a8
-/
lemma summable_middle {σ : ℂ} (hσ : 0 < σ.im) :
    Summable (Function.uncurry fun x m : ℤ =>
      cexp (-π * (-3 * I * σ / 2) * (x : ℂ) ^ 2 + 2 * π * (I * (m : ℂ) / 2) * (x : ℂ)) *
        cexp (-π / (-2 * I * σ) * (m : ℂ) ^ 2)) := by
  have ha₁ : 0 < (-3 * I * σ / 2).re := re_neg_three_I_mul_div_two hσ
  have ha₂ : 0 < ((-2 * I * σ)⁻¹).re := by
    rw [Complex.inv_re]
    exact div_pos (re_neg_two_I_mul hσ) (Complex.normSq_pos.mpr
      (mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) (ne_zero_of_im_pos hσ)))
  apply Summable.of_norm
  refine Summable.congr
    (Summable.mul_of_nonneg (summable_norm_cexp_neg_quadratic ha₁ 0)
      (summable_norm_cexp_neg_quadratic ha₂ 0)
      (fun x => norm_nonneg _) (fun m => norm_nonneg _)) ?_
  rintro ⟨x, m⟩
  simp only [Function.uncurry_apply_pair, norm_mul]
  congr 1
  ·
    rw [Complex.norm_exp, Complex.norm_exp]
    congr 1
    simp only [Complex.add_re]
    congr 1
    rw [show (2 * (π : ℂ) * (0 : ℂ) * (x : ℂ)) = (0 : ℂ) by ring,
      show (2 * (π : ℂ) * (I * (m : ℂ) / 2) * (x : ℂ)) =
        ((π * (m : ℝ) * (x : ℝ) : ℝ) : ℂ) * I by push_cast; ring]
    rw [Complex.zero_re, Complex.re_ofReal_mul, Complex.I_re, mul_zero]
  ·
    refine congrArg norm (congrArg cexp ?_)
    rw [mul_zero, zero_mul, add_zero, div_eq_mul_inv]

/--
@isnad1 id=eq.1h1v.s7.7a627a355c8c from=translated src=- shape=c2f4de0a vocab=8d6d99d5
-/
theorem hexTheta_eq_mul_self_neg_inv {σ : ℂ} (hσ : 0 < σ.im) :
    hexTheta σ =
      1 / (-2 * I * σ) ^ (1 / 2 : ℂ) * (1 / (-3 * I * σ / 2) ^ (1 / 2 : ℂ)) *
        hexTheta (-1 / (3 * σ)) := by
  have hσ' : 0 < (-1 / (3 * σ)).im := im_neg_one_div_three_mul_pos hσ
  calc
    hexTheta σ = ∑' x : ℤ, ∑' y : ℤ, hexThetaTerm σ (x, y) :=
      (summable_hexThetaTerm hσ).tsum_prod
    _ = ∑' x : ℤ, (1 / (-2 * I * σ) ^ (1 / 2 : ℂ) *
          ∑' m : ℤ,
            (cexp (-π * (-3 * I * σ / 2) * (x : ℂ) ^ 2 + 2 * π * (I * (m : ℂ) / 2) * (x : ℂ)) *
              cexp (-π / (-2 * I * σ) * (m : ℂ) ^ 2))) :=
      tsum_congr fun x => inner_poisson hσ x
    _ = 1 / (-2 * I * σ) ^ (1 / 2 : ℂ) *
          ∑' x : ℤ, ∑' m : ℤ,
            (cexp (-π * (-3 * I * σ / 2) * (x : ℂ) ^ 2 + 2 * π * (I * (m : ℂ) / 2) * (x : ℂ)) *
              cexp (-π / (-2 * I * σ) * (m : ℂ) ^ 2)) :=
      tsum_mul_left
    _ = 1 / (-2 * I * σ) ^ (1 / 2 : ℂ) *
          ∑' m : ℤ, ∑' x : ℤ,
            (cexp (-π * (-3 * I * σ / 2) * (x : ℂ) ^ 2 + 2 * π * (I * (m : ℂ) / 2) * (x : ℂ)) *
              cexp (-π / (-2 * I * σ) * (m : ℂ) ^ 2)) := by
      congr 1
      exact ((summable_middle hσ).tsum_comm).symm
    _ = 1 / (-2 * I * σ) ^ (1 / 2 : ℂ) *
          ∑' m : ℤ, (1 / (-3 * I * σ / 2) ^ (1 / 2 : ℂ) *
            ∑' k : ℤ, hexThetaTerm (-1 / (3 * σ)) (k, -m)) := by
      congr 1
      exact tsum_congr fun m => outer_poisson hσ m
    _ = 1 / (-2 * I * σ) ^ (1 / 2 : ℂ) * (1 / (-3 * I * σ / 2) ^ (1 / 2 : ℂ) *
          ∑' m : ℤ, ∑' k : ℤ, hexThetaTerm (-1 / (3 * σ)) (k, -m)) := by
      rw [tsum_mul_left]
    _ = 1 / (-2 * I * σ) ^ (1 / 2 : ℂ) * (1 / (-3 * I * σ / 2) ^ (1 / 2 : ℂ)) *
          hexTheta (-1 / (3 * σ)) := by
      have hS : (∑' m : ℤ, ∑' k : ℤ, hexThetaTerm (-1 / (3 * σ)) (k, -m)) =
          hexTheta (-1 / (3 * σ)) :=
        calc
          (∑' m : ℤ, ∑' k : ℤ, hexThetaTerm (-1 / (3 * σ)) (k, -m)) =
              ∑' m : ℤ, ∑' k : ℤ, hexThetaTerm (-1 / (3 * σ)) (-m, k) :=
            tsum_congr fun m => tsum_congr fun k => hexThetaTerm_swap _ k (-m)
          _ = ∑' m : ℤ, ∑' k : ℤ, hexThetaTerm (-1 / (3 * σ)) (m, k) :=
            tsum_comp_neg fun m => ∑' k : ℤ, hexThetaTerm (-1 / (3 * σ)) (m, k)
          _ = hexTheta (-1 / (3 * σ)) := ((summable_hexThetaTerm hσ').tsum_prod).symm
      rw [hS]
      ring

/--
@isnad1 id=lt.2h2v.s6.d83fe3f452de from=translated src=- shape=23638374 vocab=9de3e924
-/
lemma re_cpow_half_mul_cpow_half_pos {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    0 < (a ^ (1 / 2 : ℂ) * b ^ (1 / 2 : ℂ)).re := by
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  have hb0 : b ≠ 0 := fun h => by simp [h] at hb
  have harga : |Complex.arg a| < π / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl ha)
  have hargb : |Complex.arg b| < π / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hb)
  rw [abs_lt] at harga hargb
  have hcos : 0 < Real.cos (Complex.arg a * (1 / 2) + Complex.arg b * (1 / 2)) :=
    Real.cos_pos_of_mem_Ioo
      ⟨by linarith [harga.1, hargb.1], by linarith [harga.2, hargb.2]⟩
  rw [Real.cos_add] at hcos
  have hra : 0 < ‖a‖ ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos (norm_pos_iff.mpr ha0) _
  have hrb : 0 < ‖b‖ ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos (norm_pos_iff.mpr hb0) _
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.mul_re,
    Complex.cpow_ofReal_re, Complex.cpow_ofReal_re, Complex.cpow_ofReal_im,
    Complex.cpow_ofReal_im]
  nlinarith [mul_pos hra hrb, hcos]

lemma eq_of_sq_eq_sq_of_re_pos {a b : ℂ} (h : a ^ 2 = b ^ 2) (ha : 0 < a.re)
    (hb : 0 < b.re) : a = b := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h' | h'
  · exact h'
  · exfalso
    rw [h', Complex.neg_re] at ha
    linarith

/--
@isnad1 id=eq.1h1v.s6.59a49df5b123 from=translated src=- shape=73871a8e vocab=83137b25
-/
lemma sq_cpow_half {z : ℂ} (hz : z ≠ 0) : (z ^ (1 / 2 : ℂ)) ^ 2 = z := by
  rw [sq, ← Complex.cpow_add _ _ hz]
  norm_num

/--
@isnad1 id=eq.1h1v.s7.29d020f996d5 from=translated src=- shape=73a6d55e vocab=4f1cc2a8
-/
lemma cpow_half_mul_cpow_half {σ : ℂ} (hσ : 0 < σ.im) :
    (-2 * I * σ) ^ (1 / 2 : ℂ) * (-3 * I * σ / 2) ^ (1 / 2 : ℂ) =
      -I * (Real.sqrt 3 : ℂ) * σ := by
  have hσ0 : σ ≠ 0 := ne_zero_of_im_pos hσ
  have ha : (-2 : ℂ) * I * σ ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) hσ0
  have hb : (-3 : ℂ) * I * σ / 2 ≠ 0 :=
    div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) hσ0) (by norm_num)
  have hs3 : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  refine eq_of_sq_eq_sq_of_re_pos ?_
    (re_cpow_half_mul_cpow_half_pos (re_neg_two_I_mul hσ) (re_neg_three_I_mul_div_two hσ)) ?_
  ·
    rw [mul_pow, sq_cpow_half ha, sq_cpow_half hb,
      show (-I * ((Real.sqrt 3 : ℝ) : ℂ) * σ) ^ 2 =
        ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 * (I ^ 2 * σ ^ 2) by ring,
      hs3]
    ring
  ·
    rw [show (-I * ((Real.sqrt 3 : ℝ) : ℂ) * σ) = ((Real.sqrt 3 : ℝ) : ℂ) * (σ * -I) by ring,
      Complex.re_ofReal_mul, mul_neg, Complex.neg_re, Complex.mul_I_re, neg_neg]
    exact mul_pos (Real.sqrt_pos.mpr (by norm_num)) hσ

/--
@isnad1 id=ne.1h1v.s5.b7807f9b282c from=translated src=- shape=050bcab7 vocab=83137b25
-/
lemma cpow_half_ne_zero {z : ℂ} (hz : z ≠ 0) : z ^ (1 / 2 : ℂ) ≠ 0 := fun h =>
  hz ((Complex.cpow_eq_zero_iff _ _).mp h).1

/--
@isnad1 id=eq.1h1v.s6.7aa41fc26fdd from=translated src=- shape=703e8aea vocab=ece98043
-/
theorem hexTheta_fricke {σ : ℂ} (hσ : 0 < σ.im) :
    hexTheta (-1 / (3 * σ)) = -I * (Real.sqrt 3 : ℂ) * σ * hexTheta σ := by
  have hσ0 : σ ≠ 0 := ne_zero_of_im_pos hσ
  have ha : (-2 : ℂ) * I * σ ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) hσ0
  have hb : (-3 : ℂ) * I * σ / 2 ≠ 0 :=
    div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) hσ0) (by norm_num)
  have hu : (-2 * I * σ) ^ (1 / 2 : ℂ) ≠ 0 := cpow_half_ne_zero ha
  have hv : (-3 * I * σ / 2) ^ (1 / 2 : ℂ) ≠ 0 := cpow_half_ne_zero hb
  have hone : (-2 * I * σ) ^ (1 / 2 : ℂ) * (-3 * I * σ / 2) ^ (1 / 2 : ℂ) *
      (1 / (-2 * I * σ) ^ (1 / 2 : ℂ) * (1 / (-3 * I * σ / 2) ^ (1 / 2 : ℂ))) = 1 := by
    field_simp
  rw [hexTheta_eq_mul_self_neg_inv hσ, ← cpow_half_mul_cpow_half hσ, ← mul_assoc, hone,
    one_mul]

end

end A2HexPoisson

/--
@isnad1 id=and.1h1v.s9.eb10663e67f8 from=translated src=- shape=0f23317e vocab=3b5f28e8
-/
theorem solution (σ : ℂ) (hσ : 0 < σ.im) :
    Summable (fun p : ℤ × ℤ =>
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * σ *
        ((p.1 : ℂ) ^ 2 + (p.1 : ℂ) * (p.2 : ℂ) + (p.2 : ℂ) ^ 2))) ∧
    (∑' p : ℤ × ℤ, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (-1 / (3 * σ)) *
        ((p.1 : ℂ) ^ 2 + (p.1 : ℂ) * (p.2 : ℂ) + (p.2 : ℂ) ^ 2))) =
      -Complex.I * (Real.sqrt 3 : ℂ) * σ *
        ∑' p : ℤ × ℤ, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * σ *
          ((p.1 : ℂ) ^ 2 + (p.1 : ℂ) * (p.2 : ℂ) + (p.2 : ℂ) ^ 2)) :=
  ⟨A2HexPoisson.summable_hexThetaTerm hσ, A2HexPoisson.hexTheta_fricke hσ⟩
