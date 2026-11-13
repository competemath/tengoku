import Tengoku.Nlalib.NLAlib.Estimation.Reconstruction.NormalMixedMoments
import Tengoku.Nlalib.NLAlib.Estimation.Reconstruction.NormalSpectralCoordinates
import Tengoku.Nlalib.NLAlib.Krylov.QueryModel.AdjointChebyshev
import Tengoku.Nlalib.NLAlib.Krylov.QueryModel.ChebyshevArithmetic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Native two-sided queries compute the actual normal spectral moments

The strategy receives only the initial vector and degree before the oracle is
supplied. Its exact output is the basis-independent spectral moment matrix.
The scalar-expression accounting includes both recurrences and the cross-Gram.
Source: MMSUW 2026, Lemma 2.1, Algorithm 1 and Section 2.4.
-/

noncomputable section
open scoped Matrix
open MeasureTheory
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Arbitrary polynomial mixed moments in the native real Euclidean coordinates.
atlas: normal-matrix-mixed-chebyshev-moments (partial)
@isnad1 id=eq.1h5v.s11.11145e269bbf from=translated src=- shape=33fd200a vocab=b2bf30e6
-/
theorem integral_normalCoordinateSpectralLaw_star_poly_mul_poly
    {A : Matrix n n ℂ} (hA : A*Aᴴ=Aᴴ*A) (b : n → ℂ) (p q : Polynomial ℂ) :
    (∫ x : EuclideanSpace ℝ (Fin 2), star (p.eval (x 0 : ℂ))*q.eval (x 1 : ℂ)
      ∂normalCoordinateSpectralLaw hA b) =
      star ((Polynomial.aeval (realPart A : Matrix n n ℂ) p)*ᵥb) ⬝ᵥ
        ((Polynomial.aeval (imaginaryPart A : Matrix n n ℂ) q)*ᵥb) := by
  rw [normalCoordinateSpectralLaw, integral_map
    Complex.orthonormalBasisOneI.repr.continuous.measurable.aemeasurable (by fun_prop)]
  exact integral_normalSpectralLaw_star_poly_re_mul_poly_im hA b p q

/-- The scalar primitive program is the actual spectral mixed-moment matrix.
atlas: normal-matrix-mixed-chebyshev-moments (partial)
@isnad1 id=eq.1h6v.s8.7ef4572234c6 from=translated src=- shape=aa3ff595 vocab=7c909c56
-/
theorem run_normalMixedMomentProgram_eq_integral
    {A : Matrix n n ℂ} (hA : A*Aᴴ=Aᴴ*A) (b : n → ℂ) (M : ℕ)
    (j k : Fin (M+1)) :
    ((normalMixedMomentProgram b M).run (matrixAdjointOracle A)) j k =
      ∫ z, ((normalizedChebyshev j z.re * normalizedChebyshev k z.im : ℝ) : ℂ)
        ∂normalSpectralLaw hA b := by
  rw [run_normalMixedMomentProgram]
  exact (integral_normalSpectralLaw_normalizedChebyshev_eq_crossGram hA b M j k).symm

/-- The same output is the actual tensor moment in real Euclidean coordinates.
atlas: normal-matrix-mixed-chebyshev-moments (partial)
@isnad1 id=eq.1h6v.s8.20b4e9a39ca3 from=translated src=- shape=85dd073f vocab=4d1c121e
-/
theorem run_normalMixedMomentProgram_eq_coordinate_integral
    {A : Matrix n n ℂ} (hA : A*Aᴴ=Aᴴ*A) (b : n → ℂ) (M : ℕ)
    (j k : Fin (M+1)) :
    ((normalMixedMomentProgram b M).run (matrixAdjointOracle A)) j k =
      ∫ x : EuclideanSpace ℝ (Fin 2),
        ((normalizedChebyshev j (x 0) * normalizedChebyshev k (x 1) : ℝ) : ℂ)
        ∂normalCoordinateSpectralLaw hA b := by
  rw [normalCoordinateSpectralLaw, integral_map
    Complex.orthonormalBasisOneI.repr.continuous.measurable.aemeasurable (by
      apply Continuous.aestronglyMeasurable
      unfold normalizedChebyshev
      fun_prop)]
  simpa only [Complex.orthonormalBasisOneI_repr_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one] using
    run_normalMixedMomentProgram_eq_integral hA b M j k

omit [DecidableEq n] in
/-- Every response history of the native recurrence has the advertised
dimension-linear, degree-quadratic scalar work, including normalization and
every output entry. Matrix-vector products are charged separately as queries.
atlas: normal-matrix-mixed-chebyshev-moments (partial)
@isnad1 id=le.0h7v.s7.40599cfa3aa0 from=translated src=- shape=711397b7 vocab=327778c3
-/
theorem normalMixedScalarWork_le (M : ℕ)
    (matrixResponse adjointResponse previous : Bool → Fin M → n → ℂ)
    (X Y : Matrix n (Fin (M+1)) ℂ) :
    normalMixedScalarWork M matrixResponse adjointResponse previous X Y ≤
      13*Fintype.card n*(M+1)^2 :=
  (normalMixedScalarWork_le_budget M matrixResponse adjointResponse previous X Y).trans
    (normalMixedArithmeticBudget_le _ _)

end NLAlib
