import Tengoku.Nlalib.NLAlib.Polynomial.OrthogonalPolynomials.MomentCoordinates
import Tengoku.Nlalib.NLAlib.Polynomial.Quadrature.MomentGauss
import Tengoku.Nlalib.NLAlib.ForMathlib.Analysis.Calculus.LagrangeContinuity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Moment truncation preserves finite Gauss data

The first `2n` moments determine every order at most `n`, every included
recurrence coefficient, the Jacobi matrix, and its canonical Gauss nodes and
weights. The equalities hold even at early singular systems because the
definitions are total. Source: AQ22–AQ23 in the operator re-derivations.
-/

noncomputable section
open Polynomial Finset
namespace NLAlib

/-- The first `2n` monomial moments of a polynomial functional.-/
def finiteMomentVector (L : ℝ[X] →ₗ[ℝ] ℝ) (n : ℕ) : Fin (2 * n) → ℝ :=
  fun i => L (X ^ i.val)

/-- Truncating above degree `2n-1` preserves each lower-order Hankel matrix.
@isnad1 id=eq.1h3v.s6.181f34d35e3a from=translated src=- shape=9307e037 vocab=41fd92b1
-/
theorem hankelMomentMatrix_finiteMomentVector_eq (L : ℝ[X] →ₗ[ℝ] ℝ) {n k : ℕ} (hk : k ≤ n) :
    hankelMomentMatrix (finiteMomentFunctional (finiteMomentVector L n)) k = hankelMomentMatrix L k := by
  ext i j
  apply finiteMomentFunctional_apply_eq_of_degree_lt
  rw [degree_X_pow]
  exact_mod_cast (show i.val + j.val < 2 * n by have := i.isLt; have := j.isLt; omega)

/-- Every canonical polynomial through order `n` depends only on `2n` moments.
@isnad1 id=eq.1h3v.s6.36030ca45da0 from=translated src=- shape=c0bc6a8a vocab=0cfb7e34
-/
theorem monicOrthogonalPolynomial_finiteMomentVector_eq
    (L : ℝ[X] →ₗ[ℝ] ℝ) {n k : ℕ} (hk : k ≤ n) :
    monicOrthogonalPolynomial (finiteMomentFunctional (finiteMomentVector L n)) k =
      monicOrthogonalPolynomial L k := by
  apply monicOrthogonalPolynomial_eq_of_moments_eq
  intro j hj
  apply finiteMomentFunctional_apply_eq_of_degree_lt
  rw [degree_X_pow]
  exact_mod_cast (show j < 2 * n by omega)

/-- Included squared monic norms depend only on the same finite moments.
@isnad1 id=eq.1h3v.s6.b866b6698a18 from=translated src=- shape=787e1608 vocab=0ee6722f
-/
theorem orthogonalPolynomialNorm_finiteMomentVector_eq
    (L : ℝ[X] →ₗ[ℝ] ℝ) {n k : ℕ} (hk : k < n) :
    orthogonalPolynomialNorm (finiteMomentFunctional (finiteMomentVector L n)) k =
      orthogonalPolynomialNorm L k := by
  unfold orthogonalPolynomialNorm
  rw [monicOrthogonalPolynomial_finiteMomentVector_eq L hk.le]
  apply finiteMomentFunctional_apply_eq_of_degree_lt
  rw [degree_pow, degree_eq_natDegree (monic_monicOrthogonalPolynomial L k).ne_zero,
    natDegree_monicOrthogonalPolynomial, nsmul_eq_mul]
  exact_mod_cast (show 2 * k < 2 * n by omega)

/-- Included diagonal coefficients are exactly those of the finite moment vector.
@isnad1 id=eq.1h3v.s6.66e70d1a9f39 from=translated src=- shape=787e1608 vocab=0dd6e0ae
-/
theorem orthogonalRecurrenceAlpha_finiteMomentVector_eq
    (L : ℝ[X] →ₗ[ℝ] ℝ) {n k : ℕ} (hk : k < n) :
    orthogonalRecurrenceAlpha (finiteMomentFunctional (finiteMomentVector L n)) k =
      orthogonalRecurrenceAlpha L k := by
  unfold orthogonalRecurrenceAlpha
  rw [orthogonalPolynomialNorm_finiteMomentVector_eq L hk,
    monicOrthogonalPolynomial_finiteMomentVector_eq L hk.le]
  congr 1
  apply finiteMomentFunctional_apply_eq_of_degree_lt
  rw [degree_mul, degree_X, degree_pow,
    degree_eq_natDegree (monic_monicOrthogonalPolynomial L k).ne_zero,
    natDegree_monicOrthogonalPolynomial, nsmul_eq_mul]
  exact_mod_cast (show 1 + 2 * k < 2 * n by omega)

/-- Included subdiagonal coefficients, including the zero-order boundary,
are exactly those determined by the finite moment vector.
@isnad1 id=eq.1h3v.s6.40ea3d7bd33c from=translated src=- shape=787e1608 vocab=1903d423
-/
theorem orthogonalRecurrenceBeta_finiteMomentVector_eq
    (L : ℝ[X] →ₗ[ℝ] ℝ) {n k : ℕ} (hk : k < n) :
    orthogonalRecurrenceBeta (finiteMomentFunctional (finiteMomentVector L n)) k =
      orthogonalRecurrenceBeta L k := by
  unfold orthogonalRecurrenceBeta
  split_ifs
  · rfl
  · rw [orthogonalPolynomialNorm_finiteMomentVector_eq L hk,
      orthogonalPolynomialNorm_finiteMomentVector_eq L (by omega : k - 1 < n)]

/-- Included normalized polynomials are preserved, even when their norms vanish.
@isnad1 id=eq.1h3v.s6.52ced65ea1e8 from=translated src=- shape=061db611 vocab=212ff988
-/
theorem orthonormalMomentPolynomial_finiteMomentVector_eq
    (L : ℝ[X] →ₗ[ℝ] ℝ) {n k : ℕ} (hk : k < n) :
    orthonormalMomentPolynomial (finiteMomentFunctional (finiteMomentVector L n)) k =
      orthonormalMomentPolynomial L k := by
  simp only [orthonormalMomentPolynomial, orthogonalPolynomialNorm_finiteMomentVector_eq L hk,
    monicOrthogonalPolynomial_finiteMomentVector_eq L hk.le]

private theorem degree_orthonormalMomentPolynomial_le (L : ℝ[X] →ₗ[ℝ] ℝ) (k : ℕ) :
    (orthonormalMomentPolynomial L k).degree ≤ k := by
  rw [orthonormalMomentPolynomial, C_mul']
  apply (degree_smul_le _ _).trans_eq
  rw [degree_eq_natDegree (monic_monicOrthogonalPolynomial L k).ne_zero,
    natDegree_monicOrthogonalPolynomial]

/-- The actual normalized multiplication matrix is determined by `2n` moments.
@isnad1 id=eq.0h2v.s6.aa6dd6f13820 from=translated src=- shape=3ff12929 vocab=b882fbc6
-/
theorem orthogonalPolynomialJacobiMatrix_finiteMomentVector_eq (L : ℝ[X] →ₗ[ℝ] ℝ) (n : ℕ) :
    orthogonalPolynomialJacobiMatrix (finiteMomentFunctional (finiteMomentVector L n)) n =
      orthogonalPolynomialJacobiMatrix L n := by
  ext i j
  simp only [orthogonalPolynomialJacobiMatrix,
    orthonormalMomentPolynomial_finiteMomentVector_eq L i.isLt,
    orthonormalMomentPolynomial_finiteMomentVector_eq L j.isLt]
  apply finiteMomentFunctional_apply_eq_of_degree_lt
  apply (degree_mul_le _ _).trans_lt
  apply (add_le_add ((degree_mul_le _ _).trans
    (add_le_add (by rw [degree_X]) (degree_orthonormalMomentPolynomial_le L j.val)))
    (degree_orthonormalMomentPolynomial_le L i.val)).trans_lt
  exact_mod_cast (show 1 + j.val + i.val < 2 * n by have := i.isLt; have := j.isLt; omega)

/-- The canonical nodes are determined by `2n` moments, with their fixed indexing.
@isnad1 id=eq.0h2v.s6.81ad8cba1027 from=translated src=- shape=f566a48b vocab=efcddd78
-/
theorem momentGaussNodes_finiteMomentVector_eq (L : ℝ[X] →ₗ[ℝ] ℝ) (n : ℕ) :
    momentGaussNodes (finiteMomentFunctional (finiteMomentVector L n)) n = momentGaussNodes L n := by
  funext i
  exact Matrix.IsHermitian.eigenvalues₀_congr
    (isHermitian_orthogonalPolynomialJacobiMatrix (finiteMomentFunctional (finiteMomentVector L n)) n)
    (isHermitian_orthogonalPolynomialJacobiMatrix L n)
    (orthogonalPolynomialJacobiMatrix_finiteMomentVector_eq L n)
    ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i)

/-- The canonical integrated-cardinal weights are determined by `2n` moments.
@isnad1 id=eq.0h2v.s6.f0202e8f453d from=translated src=- shape=f566a48b vocab=df920768
-/
theorem momentGaussWeights_finiteMomentVector_eq (L : ℝ[X] →ₗ[ℝ] ℝ) (n : ℕ) :
    momentGaussWeights (finiteMomentFunctional (finiteMomentVector L n)) n = momentGaussWeights L n := by
  funext i
  unfold momentGaussWeights
  rw [momentGaussNodes_finiteMomentVector_eq]
  apply finiteMomentFunctional_apply_eq_of_degree_lt
  apply (Lagrange.degree_basis_le_of_mem _ (mem_univ i)).trans_lt
  simp only [card_univ, Fintype.card_fin]
  exact_mod_cast (show n - 1 < 2 * n by have := i.isLt; omega)

end NLAlib
