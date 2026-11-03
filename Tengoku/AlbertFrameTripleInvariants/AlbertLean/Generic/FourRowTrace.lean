import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.FourRowFactorization
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.FourRowMatrix
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.FourRowQuadratic
import Tengoku.Seed.LinearAlgebra.Matrix.Charpoly.Coeff
import Tengoku.Seed.LinearAlgebra.Matrix.NonsingularInverse
import Tengoku.Seed.Tactic.LinearCombination
import Tengoku.Seed.Tactic.Module

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms AlbertLean.Generic.FourRowTrace.trace_satisfies_quadratic_of_matrix_constraints` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms AlbertLean.Generic.FourRowTrace.matrix_cubic_identity_of_det_constraints` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms AlbertLean.Generic.FourRowTrace.matrix_eq_trace_reconstruction_of_constraints` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms AlbertLean.Generic.FourRowTrace.eq_or_eq_or_eq_of_three_quadratic_roots` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Trace reduction for the determinant-filtered matrix quadratic

This module joins the direct characteristic-polynomial factorization to the
scalar cubic calculation and Cayley--Hamilton reconstruction.  It contains
only ordinary three-by-three matrix algebra.
-/

noncomputable section

namespace AlbertLean.Generic.FourRowTrace

open Polynomial
open FourRowFactorization FourRowMatrix FourRowQuadratic

variable {K : Type*} [Field K]

/-- In dimension three the quadratic coefficient of the characteristic
polynomial is minus the matrix trace.
@isnad1 id=eq.0h2v.s6.3c98c70aa42b from=translated src=- shape=8c2e7ac0 vocab=c15cb796
-/
theorem charpoly_coeff_two_eq_neg_trace
    (X : Matrix (Fin 3) (Fin 3) K) :
    X.charpoly.coeff 2 = -Matrix.trace X := by
  have hTrace : Matrix.trace X = -X.charpoly.coeff 2 := by
    simpa using Matrix.trace_eq_neg_charpoly_coeff X
  linear_combination hTrace

/-- The determinant at `X` and at `1+X` put the characteristic polynomial in
the same one-parameter cubic normal form used by the scalar factor lemma.
@isnad1 id=eq.2h4v.s8.5030eb4cb542 from=translated src=- shape=82cbb5dd vocab=5aab58bc
-/
theorem charpoly_eq_cubicNormalForm_of_det_constraints
    (X : Matrix (Fin 3) (Fin 3) K) (c d : K)
    (hdetX : X.det = c)
    (hdetOneX : (1 + X).det = -d) :
    X.charpoly = cubicNormalForm c d (-Matrix.trace X) := by
  have hDegree : X.charpoly.natDegree <= 3 := by
    rw [Matrix.charpoly_natDegree_eq_dim]
    simp
  have hLead : X.charpoly.coeff 3 = 1 := by
    simpa [Matrix.charpoly_natDegree_eq_dim] using X.charpoly_monic.coeff_natDegree
  have hZero : X.charpoly.eval 0 = -c := by
    simpa [hdetX] using charpoly_eval_zero_three X
  have hNegOne : X.charpoly.eval (-1) = d := by
    simpa [hdetOneX] using charpoly_eval_neg_one_three X
  have hNormal :=
    eq_cubicNormalForm_of_endpoints X.charpoly c d
      hDegree hLead hZero hNegOne
  simpa [charpoly_coeff_two_eq_neg_trace X] using hNormal

/-- Cayley--Hamilton in the coefficient order needed by matrix
reconstruction.  The linear coefficient is recovered solely from the two
determinant constraints.
@isnad1 id=eq.2h4v.s10.f8da8f72d8d9 from=translated src=- shape=45859940 vocab=4496f70f
-/
theorem matrix_cubic_identity_of_det_constraints
    (X : Matrix (Fin 3) (Fin 3) K) (c d : K)
    (hdetX : X.det = c)
    (hdetOneX : (1 + X).det = -d) :
    X ^ 3 - Matrix.trace X • X ^ 2 +
        (-d - 1 - c - Matrix.trace X) • X - c • 1 = 0 := by
  have hCH := Matrix.aeval_self_charpoly X
  rw [charpoly_eq_cubicNormalForm_of_det_constraints X c d hdetX hdetOneX] at hCH
  simp only [cubicNormalForm, map_sub, map_add, map_mul, map_pow,
    Polynomial.aeval_X, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one,
    Matrix.smul_mul, Matrix.one_mul, sub_mul, add_mul] at hCH
  convert hCH using 1 <;> module

/-- The trace of every determinant-filtered solution satisfies the scalar
quadratic obtained from the two characteristic cubic factors.
@isnad1 id=eq.7h6v.s10.5d898999d770 from=translated src=- shape=18c536a8 vocab=0779e019
-/
theorem trace_satisfies_quadratic_of_matrix_constraints
    (X U V : Matrix (Fin 3) (Fin 3) K) (c d : K)
    (hquad : X ^ 2 + X * U + V = 0)
    (hc : c ≠ 0) (hd : d ≠ 0)
    (hdetX : X.det = c)
    (hdetOneX : (1 + X).det = -d)
    (hdetV : V.det = c ^ 2)
    (hdetNegOne : (1 - U + V).det = d ^ 2) :
    Matrix.trace X ^ 2 +
        (quadraticPolynomial U V).coeff 5 * Matrix.trace X +
        ((quadraticPolynomial U V).coeff 4 + 2 * (1 + c + d) -
          (quadraticPolynomial U V).coeff 5) = 0 := by
  let Z := -U - X
  have hDegreeX : X.charpoly.natDegree <= 3 := by
    rw [Matrix.charpoly_natDegree_eq_dim]
    simp
  have hDegreeZ : Z.charpoly.natDegree <= 3 := by
    rw [Matrix.charpoly_natDegree_eq_dim]
    simp
  have hLeadX : X.charpoly.coeff 3 = 1 := by
    simpa [Matrix.charpoly_natDegree_eq_dim] using X.charpoly_monic.coeff_natDegree
  have hLeadZ : Z.charpoly.coeff 3 = 1 := by
    simpa [Matrix.charpoly_natDegree_eq_dim] using Z.charpoly_monic.coeff_natDegree
  have hZeroX : X.charpoly.eval 0 = -c := by
    simpa [hdetX] using charpoly_eval_zero_three X
  have hNegOneX : X.charpoly.eval (-1) = d := by
    simpa [hdetOneX] using charpoly_eval_neg_one_three X
  have hEndpointsZ : Z.charpoly.eval 0 = -c ∧ Z.charpoly.eval (-1) = d := by
    simpa [Z] using complementary_charpoly_endpoints X U V c d hquad hc hd
      hdetX hdetOneX hdetV hdetNegOne
  have hFactor : quadraticPolynomial U V = X.charpoly * Z.charpoly := by
    simpa [Z] using quadraticPolynomial_eq_charpoly_mul X U V hquad
  have hScalar :=
    coeff_two_satisfies_quadratic_of_cubic_factorization
      X.charpoly Z.charpoly (quadraticPolynomial U V) c d
      hDegreeX hDegreeZ hLeadX hLeadZ hZeroX hEndpointsZ.1
      hNegOneX hEndpointsZ.2 hFactor
  rw [charpoly_coeff_two_eq_neg_trace X] at hScalar
  simpa using hScalar

/-- Three roots of one monic quadratic over a field cannot all be distinct.-/
theorem eq_or_eq_or_eq_of_three_quadratic_roots
    (a b x y z : K)
    (hx : x ^ 2 + a * x + b = 0)
    (hy : y ^ 2 + a * y + b = 0)
    (hz : z ^ 2 + a * z + b = 0) :
    x = y ∨ x = z ∨ y = z := by
  by_cases hxy : x = y
  · exact Or.inl hxy
  by_cases hxz : x = z
  · exact Or.inr (Or.inl hxz)
  right
  right
  have hxyFactor : (x - y) * (x + y + a) = 0 := by
    linear_combination hx - hy
  have hxzFactor : (x - z) * (x + z + a) = 0 := by
    linear_combination hx - hz
  have hxySum : x + y + a = 0 :=
    (mul_eq_zero.mp hxyFactor).resolve_left (sub_ne_zero.mpr hxy)
  have hxzSum : x + z + a = 0 :=
    (mul_eq_zero.mp hxzFactor).resolve_left (sub_ne_zero.mpr hxz)
  linear_combination hxySum - hxzSum

/-- On the reconstruction open, a solution is a rational expression in its
trace.  The typeclass is exactly the invertibility of the displayed
denominator matrix.
@isnad1 id=eq.3h6v.s11.95a6d934c660 from=translated src=- shape=54d49f11 vocab=a486dae0
-/
theorem matrix_eq_trace_reconstruction_of_constraints
    (X U V : Matrix (Fin 3) (Fin 3) K) (c d : K)
    (hquad : X ^ 2 + X * U + V = 0)
    (hdetX : X.det = c)
    (hdetOneX : (1 + X).det = -d)
    [Invertible (U ^ 2 - V + Matrix.trace X • U +
      (-d - 1 - c - Matrix.trace X) • 1)] :
    X = (c • 1 - V * U - Matrix.trace X • V) *
      ⅟(U ^ 2 - V + Matrix.trace X • U +
        (-d - 1 - c - Matrix.trace X) • 1) := by
  exact matrix_reconstruction_of_right_quadratic
    X U V (Matrix.trace X) (-d - 1 - c - Matrix.trace X) c hquad
    (matrix_cubic_identity_of_det_constraints X c d hdetX hdetOneX)

/-- Over a field, nonzero determinant is an explicit sufficient hypothesis
for the reconstruction denominator above to be invertible.
@isnad1 id=eq.4h6v.s11.ffdbd9aef672 from=translated src=- shape=1c402a4f vocab=8808bbd4
-/
theorem matrix_eq_trace_reconstruction_of_det_ne_zero
    (X U V : Matrix (Fin 3) (Fin 3) K) (c d : K)
    (hquad : X ^ 2 + X * U + V = 0)
    (hdetX : X.det = c)
    (hdetOneX : (1 + X).det = -d)
    (hE : (U ^ 2 - V + Matrix.trace X • U +
      (-d - 1 - c - Matrix.trace X) • 1).det ≠ 0) :
    X = (c • 1 - V * U - Matrix.trace X • V) *
      (U ^ 2 - V + Matrix.trace X • U +
        (-d - 1 - c - Matrix.trace X) • 1)⁻¹ := by
  let E := U ^ 2 - V + Matrix.trace X • U +
    (-d - 1 - c - Matrix.trace X) • (1 : Matrix (Fin 3) (Fin 3) K)
  let _ : Invertible E :=
    Matrix.invertibleOfIsUnitDet E (isUnit_iff_ne_zero.mpr (by simpa [E] using hE))
  have hReconstruct :=
    matrix_eq_trace_reconstruction_of_constraints X U V c d
      hquad hdetX hdetOneX
  simpa [E, Matrix.invOf_eq_nonsing_inv] using hReconstruct

end AlbertLean.Generic.FourRowTrace
