import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Exact sign certificates for the transformed phase numerator in Appendix A.3.
The coefficients are the `C_k(e)` from equation (A.21).
-/

namespace PiIrrationality

def phaseC0 (e : ℝ) : ℝ :=
  1160625 * (e ^ 2 + 1) ^ 3

def phaseC1 (e : ℝ) : ℝ :=
  -175 * (26528 * e - 26529) * (e ^ 2 + 1) ^ 2

def phaseC2 (e : ℝ) : ℝ :=
  2 * (e ^ 2 + 1) *
    (2212607 * e ^ 2 - 3795652 * e + 3126443)

def phaseC3 (e : ℝ) : ℝ :=
  8 * (418731 * e ^ 3 + 420703 * e ^ 2 + 923835 * e - 500369)

def phaseC4 (e : ℝ) : ℝ :=
  -128 * (14851 * e ^ 2 - 143914 * e + 168053)

def phaseC5 (e : ℝ) : ℝ :=
  512 * (15784 * e - 43639)

def phaseC6 (_e : ℝ) : ℝ := -7606272

noncomputable def phaseTransformedPolynomial (e : ℝ) : Polynomial ℝ :=
  Polynomial.C (phaseC0 e) +
    Polynomial.C (phaseC1 e) * Polynomial.X +
    Polynomial.C (phaseC2 e) * Polynomial.X ^ 2 +
    Polynomial.C (phaseC3 e) * Polynomial.X ^ 3 +
    Polynomial.C (phaseC4 e) * Polynomial.X ^ 4 +
    Polynomial.C (phaseC5 e) * Polynomial.X ^ 5 +
    Polynomial.C (phaseC6 e) * Polynomial.X ^ 6

theorem phaseTransformedPolynomial_coeff_zero (e : ℝ) :
    (phaseTransformedPolynomial e).coeff 0 = phaseC0 e := by
  simp [phaseTransformedPolynomial]

theorem phaseTransformedPolynomial_coeff_one (e : ℝ) :
    (phaseTransformedPolynomial e).coeff 1 = phaseC1 e := by
  simp [phaseTransformedPolynomial]

theorem phaseTransformedPolynomial_coeff_two (e : ℝ) :
    (phaseTransformedPolynomial e).coeff 2 = phaseC2 e := by
  simp [phaseTransformedPolynomial]

theorem phaseTransformedPolynomial_coeff_three (e : ℝ) :
    (phaseTransformedPolynomial e).coeff 3 = phaseC3 e := by
  simp [phaseTransformedPolynomial]

theorem phaseTransformedPolynomial_coeff_four (e : ℝ) :
    (phaseTransformedPolynomial e).coeff 4 = phaseC4 e := by
  simp [phaseTransformedPolynomial]

theorem phaseTransformedPolynomial_coeff_five (e : ℝ) :
    (phaseTransformedPolynomial e).coeff 5 = phaseC5 e := by
  simp [phaseTransformedPolynomial]

theorem phaseTransformedPolynomial_coeff_six (e : ℝ) :
    (phaseTransformedPolynomial e).coeff 6 = phaseC6 e := by
  simp [phaseTransformedPolynomial]

theorem phaseC0_pos {e : ℝ} (he : (9 : ℝ) / 10 < e) : 0 < phaseC0 e := by
  have hbase : 0 < e ^ 2 + 1 := by nlinarith [sq_nonneg e]
  dsimp [phaseC0]
  positivity

theorem phaseC1_pos {e : ℝ} (he : (9 : ℝ) / 10 < e) (he1 : e < 1) :
    0 < phaseC1 e := by
  have hfactor : 26528 * e - 26529 < 0 := by linarith
  have hsq : 0 < (e ^ 2 + 1) ^ 2 := by positivity
  dsimp [phaseC1]
  nlinarith

theorem phaseC2_pos {e : ℝ} (he : (9 : ℝ) / 10 < e) : 0 < phaseC2 e := by
  have he0 : 0 ≤ e := by linarith
  have hmul : 0 ≤ e * (e - (9 : ℝ) / 10) :=
    mul_nonneg he0 (by linarith)
  have hq : 0 < 2212607 * e ^ 2 - 3795652 * e + 3126443 := by
    nlinarith
  have hsq : 0 < e ^ 2 + 1 := by nlinarith [sq_nonneg e]
  dsimp [phaseC2]
  nlinarith

theorem phaseC3_pos {e : ℝ} (he : (9 : ℝ) / 10 < e) : 0 < phaseC3 e := by
  have he0 : 0 < e := by linarith
  have he2 : (81 : ℝ) / 100 < e ^ 2 := by
    nlinarith [sq_nonneg (e - (9 : ℝ) / 10)]
  have he3 : (729 : ℝ) / 1000 < e ^ 3 := by
    have hleft : (81 : ℝ) / 100 * e < e ^ 2 * e :=
      (mul_lt_mul_of_pos_right he2 he0)
    have hright : (729 : ℝ) / 1000 < (81 : ℝ) / 100 * e := by
      nlinarith
    nlinarith [hleft, hright]
  dsimp [phaseC3]
  nlinarith

theorem phaseC4_neg {e : ℝ} (he : (9 : ℝ) / 10 < e) (he1 : e < 1) : phaseC4 e < 0 := by
  have hq : 0 < 14851 * e ^ 2 - 143914 * e + 168053 := by
    nlinarith [sq_nonneg (e - 1)]
  dsimp [phaseC4]
  nlinarith

theorem phaseC5_neg {e : ℝ} (he1 : e < 1) : phaseC5 e < 0 := by
  have hfactor : 15784 * e - 43639 < 0 := by linarith
  dsimp [phaseC5]
  nlinarith

theorem phaseC6_neg (e : ℝ) : phaseC6 e < 0 := by
  norm_num [phaseC6]

theorem phase_transformed_signs {e : ℝ}
    (he : (9 : ℝ) / 10 < e) (he1 : e < 1) :
    0 < phaseC0 e ∧ 0 < phaseC1 e ∧ 0 < phaseC2 e ∧ 0 < phaseC3 e ∧
      phaseC4 e < 0 ∧ phaseC5 e < 0 ∧ phaseC6 e < 0 := by
  exact ⟨phaseC0_pos he, phaseC1_pos he he1, phaseC2_pos he,
    phaseC3_pos he, phaseC4_neg he he1, phaseC5_neg he1, phaseC6_neg e⟩

end PiIrrationality
