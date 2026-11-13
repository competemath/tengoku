import Tengoku.Nlalib.NLAlib.Krylov.Quadrature.DiscreteMeasure
import Tengoku.Nlalib.NLAlib.Krylov.Quadrature.SpectralMoments
import Tengoku.Nlalib.NLAlib.Polynomial.OrthogonalPolynomials.PositiveMomentFunctional
import Tengoku.Nlalib.NLAlib.Polynomial.OrthogonalPolynomials.JacobiMatrix

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Canonical Jacobi construction for finite discrete measures

The actual normalized moment polynomials evaluated at distinct atomic nodes
give an orthogonal square matrix. It transforms the diagonal node matrix to the
canonical normalized multiplication matrix and transforms the square-root
weights to the first coordinate. Source: Gautschi (2004), §2.2.3;
operator re-derivations OF20–OF21.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix MeasureTheory Finset
open scoped Matrix
namespace NLAlib
variable {N : ℕ}

/-- The square matrix of the actual canonical normalized moment polynomials
at atomic nodes, with square-root atomic weights. The definition is total;
its orthogonal interpretation requires distinct nodes and positive weights.-/
def discreteOrthogonalPolynomialEvaluationMatrix (t w : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun r j => Real.sqrt (w r) * (orthonormalMomentPolynomial
    (polynomialIntegral (spectralMeasure (Matrix.isHermitian_diagonal t) (fun r => Real.sqrt (w r)))
      (hasPolynomialMoments_spectralMeasure (Matrix.isHermitian_diagonal t) (fun r => Real.sqrt (w r))))
        j.val).eval (t r)

private theorem polynomialIntegral_diagonal_sqrt_apply_eq_sum
    (t w : Fin N → ℝ) (hw : ∀ i, 0 ≤ w i) (p : ℝ[X]) :
    polynomialIntegral (spectralMeasure (Matrix.isHermitian_diagonal t) (fun r => Real.sqrt (w r)))
      (hasPolynomialMoments_spectralMeasure (Matrix.isHermitian_diagonal t) (fun r => Real.sqrt (w r))) p =
        ∑ r : Fin N, w r * p.eval (t r) := by
  rw [polynomialIntegral_apply, integral_eval_spectralMeasure, aeval_diagonal]
  simp only [dotProduct, Matrix.mulVec_diagonal]
  apply Finset.sum_congr rfl
  intro r _
  calc
    Real.sqrt (w r)*(p.eval (t r)*Real.sqrt (w r)) = (Real.sqrt (w r))^2*p.eval (t r) := by ring
    _ = _ := by rw [Real.sq_sqrt (hw r)]

private theorem discrete_hankel_posDef (t w : Fin N → ℝ)
    (ht : Function.Injective t) (hw : ∀ i, 0 < w i) :
    (hankelMomentMatrix (polynomialIntegral
      (spectralMeasure (Matrix.isHermitian_diagonal t) (fun r => Real.sqrt (w r)))
      (hasPolynomialMoments_spectralMeasure (Matrix.isHermitian_diagonal t) (fun r => Real.sqrt (w r)))) N).PosDef := by
  apply (posDef_hankelMomentMatrix_spectralMeasure_iff _ _ _).mpr
  rw [krylovGrade_diagonal_sqrt_eq_card t w ht hw]

/-- The actual canonical normalized polynomial evaluation matrix has
orthonormal columns for distinct finite nodes and positive weights, including
the empty discrete measure.
Source: OF20, canonical discrete orthogonality.
atlas: discrete-measure-jacobi-matrix (partial)-/
theorem hasOrthonormalCols_discreteOrthogonalPolynomialEvaluationMatrix
    (t w : Fin N → ℝ) (ht : Function.Injective t) (hw : ∀ i, 0 < w i) :
    HasOrthonormalCols (discreteOrthogonalPolynomialEvaluationMatrix t w) := by
  let L := polynomialIntegral (spectralMeasure (Matrix.isHermitian_diagonal t) (fun r => Real.sqrt (w r)))
    (hasPolynomialMoments_spectralMeasure (Matrix.isHermitian_diagonal t) (fun r => Real.sqrt (w r)))
  have hpos := discrete_hankel_posDef t w ht hw
  apply hasOrthonormalCols_iff_conjTranspose_mul_self.mpr
  ext i j
  have horth := functional_orthonormalMomentPolynomial_mul L
    (hankelMomentDet_ne_zero_of_posDef_of_le hpos i.isLt.le)
    (hankelMomentDet_ne_zero_of_posDef_of_le hpos j.isLt.le)
    (orthogonalPolynomialNorm_pos_of_posDef hpos i.isLt)
    (orthogonalPolynomialNorm_pos_of_posDef hpos j.isLt)
  rw [polynomialIntegral_diagonal_sqrt_apply_eq_sum t w (fun i => (hw i).le)] at horth
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial,
    discreteOrthogonalPolynomialEvaluationMatrix, Matrix.one_apply]
  have heq : (∑ r : Fin N, (Real.sqrt (w r)*(orthonormalMomentPolynomial L i.val).eval (t r))*
      (Real.sqrt (w r)*(orthonormalMomentPolynomial L j.val).eval (t r))) =
      ∑ r : Fin N, w r*(orthonormalMomentPolynomial L i.val*orthonormalMomentPolynomial L j.val).eval (t r) := by
    apply Finset.sum_congr rfl
    intro r _
    rw [eval_mul]
    calc
      _ = (Real.sqrt (w r))^2*((orthonormalMomentPolynomial L i.val).eval (t r)*
          (orthonormalMomentPolynomial L j.val).eval (t r)) := by ring
      _ = _ := by rw [Real.sq_sqrt (hw r).le]
  rw [heq, horth]
  simp only [Fin.val_inj]

/-- The actual canonical discrete evaluation matrix also has orthonormal rows,
because it is square. Source: OF20, finite discrete dual orthogonality.
atlas: discrete-measure-jacobi-matrix (partial)-/
theorem discreteOrthogonalPolynomialEvaluationMatrix_mul_conjTranspose_eq_one
    (t w : Fin N → ℝ) (ht : Function.Injective t) (hw : ∀ i, 0 < w i) :
    discreteOrthogonalPolynomialEvaluationMatrix t w *
      (discreteOrthogonalPolynomialEvaluationMatrix t w)ᴴ = 1 :=
  (hasOrthonormalCols_discreteOrthogonalPolynomialEvaluationMatrix t w ht hw).mul_conjTranspose_self

end NLAlib
