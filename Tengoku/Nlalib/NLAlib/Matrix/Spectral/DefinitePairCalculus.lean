import Tengoku.Nlalib.NLAlib.Matrix.Spectral.DefiniteCongruence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
/-!
# Scalar formulas for positive definite pairs

Simultaneous congruence gives positive diagonal parameters and exact
determinant, inverse, and trace formulas. Source: Horn--Johnson (2013),
Section 7.6; supports `log-det-concavity` and determinant inequalities.
-/

noncomputable section
open Matrix
open scoped MatrixOrder
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
/-- Two positive definite real matrices admit simultaneous congruence to
identity and a strictly positive diagonal. Horn--Johnson (2013),
Theorem 7.6.1; helper for determinant and inverse convexity.
@isnad1 id=ex.2h3v.s7.fdc9db8ce03e from=translated src=- shape=02896a56 vocab=169247e4
-/
theorem exists_positive_definite_pair_congruence {A B : Matrix n n ℝ}
    (hA : A.PosDef) (hB : B.PosDef) :
    ∃ (S : Matrix n n ℝ) (d : n → ℝ), IsUnit S ∧ A = S * Sᵀ ∧
      B = S * diagonal d * Sᵀ ∧ (∀ i, 0 < d i) := by
  obtain ⟨S, d, hS, hAA, hBB, -⟩ := exists_definite_pair_congruence_diagonal hA hB.isHermitian
  refine ⟨S, d, hS, hAA, hBB, ?_⟩
  rw [hBB] at hB
  have hd : (diagonal d).PosDef := hS.posDef_star_right_conjugate_iff.mp hB
  exact Matrix.posDef_diagonal_iff.mp hd

open scoped Matrix.Norms.L2Operator in
/-- A linear combination of a simultaneous definite pair has the same
congruence factor and the affine diagonal combination. Horn--Johnson (2013),
Section 7.6; helper for determinant and inverse convexity.
@isnad1 id=eq.2h7v.s8.4532e0224f68 from=translated src=- shape=e847afca vocab=59e074b2
-/
theorem smul_add_smul_eq_congruence_diagonal {A B S : Matrix n n ℝ} {d : n → ℝ}
    (hA : A = S * Sᵀ) (hB : B = S * diagonal d * Sᵀ) (a b : ℝ) :
    a • A + b • B = S * diagonal (fun i => a + b * d i) * Sᵀ := by
  rw [hA, hB]
  have hd : diagonal (fun i => a + b * d i) = a • (1 : Matrix n n ℝ) + b • diagonal d := by
    rw [Matrix.smul_one_eq_diagonal, ← Matrix.diagonal_smul, ← Matrix.diagonal_add]
    rfl
  rw [hd]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]

open scoped Matrix.Norms.L2Operator in
/-- The determinant of a diagonal congruence is the factor determinant
squared times the diagonal product. Horn--Johnson (2013), Section 7.6;
helper for determinant inequalities.
@isnad1 id=eq.0h3v.s6.90b682a16a4b from=translated src=- shape=d50127e5 vocab=9f8e5e52
-/
theorem det_congruence_diagonal (S : Matrix n n ℝ) (d : n → ℝ) :
    (S * diagonal d * Sᵀ).det = S.det ^ 2 * ∏ i, d i := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
  ring

open scoped Matrix.Norms.L2Operator in
/-- Log determinant of a positive diagonal congruence separates into a
constant factor and scalar logarithms. Horn--Johnson (2013), Section 7.6;
helper for strict log-determinant concavity.
@isnad1 id=eq.2h3v.s7.08a0d8298a93 from=translated src=- shape=271a6ffc vocab=608c6af7
-/
theorem log_det_congruence_diagonal {S : Matrix n n ℝ} (hS : IsUnit S)
    (d : n → ℝ) (hd : ∀ i, 0 < d i) :
    Real.log (S * diagonal d * Sᵀ).det = Real.log (S.det ^ 2) + ∑ i, Real.log (d i) := by
  rw [det_congruence_diagonal, Real.log_mul
    (pow_ne_zero _ ((Matrix.isUnit_iff_isUnit_det S).mp hS).ne_zero)
    (Finset.prod_ne_zero_iff.mpr (fun i _ => (hd i).ne')), Real.log_prod (fun i _ => (hd i).ne')]

open scoped Matrix.Norms.L2Operator in
/-- Inverting a nonsingular diagonal congruence inverts the diagonal entries
and reverses the factors. Horn--Johnson (2013), Section 7.6;
helper for strict inverse-trace convexity.
@isnad1 id=eq.1h3v.s7.3a3b813abc2e from=translated src=- shape=216774c5 vocab=eb103c72
-/
theorem inv_congruence_diagonal (S : Matrix n n ℝ) (d : n → ℝ) (hd : ∀ i, d i ≠ 0) :
    (S * diagonal d * Sᵀ)⁻¹ = Sᵀ⁻¹ * diagonal (fun i => (d i)⁻¹) * S⁻¹ := by
  have hD : (diagonal d)⁻¹ = diagonal (fun i => (d i)⁻¹) := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j; simp [hd i]
    · simp [hij]
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, hD, Matrix.mul_assoc]

open scoped Matrix.Norms.L2Operator in
/-- Trace of a diagonal congruence is a weighted sum of the diagonal
entries, with column-Gram diagonal weights. Horn--Johnson (2013),
Section 7.6; helper for strict inverse-trace convexity.
@isnad1 id=eq.0h3v.s6.e3200c9c3208 from=translated src=- shape=3a1a7b31 vocab=0e52cbf2
-/
theorem trace_congruence_diagonal (S : Matrix n n ℝ) (d : n → ℝ) :
    (S * diagonal d * Sᵀ).trace = ∑ i, d i * (Sᵀ * S) i i := by
  rw [Matrix.trace_mul_cycle]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_diagonal]
  apply Finset.sum_congr rfl
  intro i _
  ring

end NLAlib
