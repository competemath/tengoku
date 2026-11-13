import Tengoku.Nlalib.NLAlib.Polynomial.OrthogonalPolynomials.MomentBasis
import Tengoku.Nlalib.NLAlib.Polynomial.OrthogonalPolynomials.MomentTruncation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Finite data of actual fixed-basis modified moments

The canonical fixed-basis chart has the same first `2n` moments as its original
functional, so every included recurrence coefficient and native Gauss datum
agrees. No positivity assumption is required for these total identities.
Source: Gautschi (2004), §2.1; operator re-derivations AQ22--AQ31.
-/

noncomputable section
open Polynomial Module
namespace NLAlib
variable {d n : ℕ}

/-- A fixed polynomial basis of degree below `d` reconstructs all first `2n`
monomial moments whenever `2n ≤ d`.
@isnad1 id=eq.1h4v.s7.5f8ff77730f6 from=translated src=- shape=7a0142df vocab=d0279c48
-/
theorem finiteMomentVector_coordinate_polynomialBasis_eq
    (b : Basis (Fin d) ℝ (degreeLT ℝ d)) (L : ℝ[X] →ₗ[ℝ] ℝ) (hd : 2*n ≤ d) :
    finiteMomentVector
      (coordinateMomentFunctional (polynomialBasisCoordinate b) (polynomialBasisMomentVector b L)) n =
      finiteMomentVector L n := by
  funext i
  apply coordinateMomentFunctional_polynomialBasis_eq_of_degree_lt
  rw [degree_X_pow]
  exact_mod_cast i.isLt.trans_le hd

/-- The actual fixed-basis chart's finite Hankel matrix equals that of the
original moment functional. In particular its positive domain is exactly the
original finite positive moment domain. Source: AQ26--AQ31.
atlas: recurrence-coefficient-moment-sensitivity (partial)
@isnad1 id=eq.1h4v.s7.f48751e68073 from=translated src=- shape=dce6728b vocab=83eea97e
-/
theorem hankelMomentMatrix_coordinate_polynomialBasis_eq
    (b : Basis (Fin d) ℝ (degreeLT ℝ d)) (L : ℝ[X] →ₗ[ℝ] ℝ) (hd : 2*n ≤ d) :
    hankelMomentMatrix
      (coordinateMomentFunctional (polynomialBasisCoordinate b) (polynomialBasisMomentVector b L)) n =
      hankelMomentMatrix L n := by
  rw [← hankelMomentMatrix_finiteMomentVector_eq _ le_rfl,
    finiteMomentVector_coordinate_polynomialBasis_eq b L hd,
    hankelMomentMatrix_finiteMomentVector_eq _ le_rfl]

/-- Included monic norms in actual fixed-basis moments are the original norms.
@isnad1 id=eq.2h5v.s7.4f9e2776afe0 from=translated src=- shape=10bdcd84 vocab=cd471692
-/
theorem orthogonalPolynomialNorm_coordinate_polynomialBasis_eq
    (b : Basis (Fin d) ℝ (degreeLT ℝ d)) (L : ℝ[X] →ₗ[ℝ] ℝ) (hd : 2*n ≤ d)
    {k : ℕ} (hk : k < n) :
    orthogonalPolynomialNorm
      (coordinateMomentFunctional (polynomialBasisCoordinate b) (polynomialBasisMomentVector b L)) k =
      orthogonalPolynomialNorm L k := by
  rw [← orthogonalPolynomialNorm_finiteMomentVector_eq _ hk,
    finiteMomentVector_coordinate_polynomialBasis_eq b L hd,
    orthogonalPolynomialNorm_finiteMomentVector_eq _ hk]

/-- Included diagonal coefficients in actual fixed-basis moments equal the
original coefficients, including the highest diagonal with no extra moment.
Source: AQ29--AQ31.
atlas: recurrence-coefficient-moment-sensitivity (partial)
@isnad1 id=eq.2h5v.s7.c8dc83df029d from=translated src=- shape=10bdcd84 vocab=147f6302
-/
theorem orthogonalRecurrenceAlpha_coordinate_polynomialBasis_eq
    (b : Basis (Fin d) ℝ (degreeLT ℝ d)) (L : ℝ[X] →ₗ[ℝ] ℝ) (hd : 2*n ≤ d)
    {k : ℕ} (hk : k < n) :
    orthogonalRecurrenceAlpha
      (coordinateMomentFunctional (polynomialBasisCoordinate b) (polynomialBasisMomentVector b L)) k =
      orthogonalRecurrenceAlpha L k := by
  rw [← orthogonalRecurrenceAlpha_finiteMomentVector_eq _ hk,
    finiteMomentVector_coordinate_polynomialBasis_eq b L hd,
    orthogonalRecurrenceAlpha_finiteMomentVector_eq _ hk]

/-- Included positive-order subdiagonals and the order-zero boundary in actual
fixed-basis moments equal the original coefficients.
@isnad1 id=eq.2h5v.s7.ebdff18f205a from=translated src=- shape=10bdcd84 vocab=a661e1a0
-/
theorem orthogonalRecurrenceBeta_coordinate_polynomialBasis_eq
    (b : Basis (Fin d) ℝ (degreeLT ℝ d)) (L : ℝ[X] →ₗ[ℝ] ℝ) (hd : 2*n ≤ d)
    {k : ℕ} (hk : k < n) :
    orthogonalRecurrenceBeta
      (coordinateMomentFunctional (polynomialBasisCoordinate b) (polynomialBasisMomentVector b L)) k =
      orthogonalRecurrenceBeta L k := by
  rw [← orthogonalRecurrenceBeta_finiteMomentVector_eq _ hk,
    finiteMomentVector_coordinate_polynomialBasis_eq b L hd,
    orthogonalRecurrenceBeta_finiteMomentVector_eq _ hk]

/-- The canonical Jacobi matrix in actual fixed-basis coordinates is the
original finite Jacobi matrix.
@isnad1 id=eq.1h4v.s7.b210093debfd from=translated src=- shape=e9878569 vocab=32060439
-/
theorem orthogonalPolynomialJacobiMatrix_coordinate_polynomialBasis_eq
    (b : Basis (Fin d) ℝ (degreeLT ℝ d)) (L : ℝ[X] →ₗ[ℝ] ℝ) (hd : 2*n ≤ d) :
    orthogonalPolynomialJacobiMatrix
      (coordinateMomentFunctional (polynomialBasisCoordinate b) (polynomialBasisMomentVector b L)) n =
      orthogonalPolynomialJacobiMatrix L n := by
  rw [← orthogonalPolynomialJacobiMatrix_finiteMomentVector_eq _ n,
    finiteMomentVector_coordinate_polynomialBasis_eq b L hd,
    orthogonalPolynomialJacobiMatrix_finiteMomentVector_eq _ n]

/-- The actual fixed-basis chart preserves the canonical ordered Gauss nodes.
@isnad1 id=eq.1h4v.s7.ee678fb23de6 from=translated src=- shape=13dfab26 vocab=58451fc0
-/
theorem momentGaussNodes_coordinate_polynomialBasis_eq
    (b : Basis (Fin d) ℝ (degreeLT ℝ d)) (L : ℝ[X] →ₗ[ℝ] ℝ) (hd : 2*n ≤ d) :
    momentGaussNodes
      (coordinateMomentFunctional (polynomialBasisCoordinate b) (polynomialBasisMomentVector b L)) n =
      momentGaussNodes L n := by
  rw [← momentGaussNodes_finiteMomentVector_eq _ n,
    finiteMomentVector_coordinate_polynomialBasis_eq b L hd,
    momentGaussNodes_finiteMomentVector_eq _ n]

/-- The actual fixed-basis chart preserves the canonical integrated Gauss
weights.
@isnad1 id=eq.1h4v.s7.010185559ab3 from=translated src=- shape=13dfab26 vocab=893f560b
-/
theorem momentGaussWeights_coordinate_polynomialBasis_eq
    (b : Basis (Fin d) ℝ (degreeLT ℝ d)) (L : ℝ[X] →ₗ[ℝ] ℝ) (hd : 2*n ≤ d) :
    momentGaussWeights
      (coordinateMomentFunctional (polynomialBasisCoordinate b) (polynomialBasisMomentVector b L)) n =
      momentGaussWeights L n := by
  rw [← momentGaussWeights_finiteMomentVector_eq _ n,
    finiteMomentVector_coordinate_polynomialBasis_eq b L hd,
    momentGaussWeights_finiteMomentVector_eq _ n]

end NLAlib
