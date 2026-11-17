/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
import Tengoku.JacobianTwo.JacobianTwo.ConstantLeadingQuadratic
import Tengoku.JacobianTwo.JacobianTwo.QuadraticGCDDescent
import Tengoku.JacobianTwo.JacobianTwo.QuadraticUnitConclusion

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Conclusion for a variable-leading quadratic coordinate

The denominator descent and unit conclusion eliminate a genuinely variable
quadratic leading coefficient.  First this is proved for an odd-degree Keller
mate with the exact UFD leading-coefficient shape.  Target shears and the UFD
shape theorem then reduce an arbitrary Keller mate to that case.
-/

noncomputable section

open scoped Polynomial Polynomial.Bivariate
open Polynomial

namespace JacobianTwo.VariableLeadingQuadraticConclusion

open JacobianTwo.AffineCoordinate
open JacobianTwo.ConstantLeadingQuadratic
open JacobianTwo.QuadraticDirectPackage
open JacobianTwo.QuadraticGCDDescent
open JacobianTwo.QuadraticReduction
open JacobianTwo.QuadraticUnitConclusion
open JacobianTwo.VariableLeadingQuadratic

variable {K : Type*} [Field K] [CharZero K]

/-- An odd-degree Keller mate with the UFD square-root shape forces the square
root `h` of the quadratic leading coefficient to be a unit.
@isnad1 id=isunit.7h9v.s9.aa05787ec58c from=translated src=- shape=24e12269 vocab=80318ffc
-/
theorem odd_residual_squareRoot_isUnit
    {eps k lam : K} {h g f : K[X]} {m : ℕ} (P : K[X][Y])
    (heps : eps ≠ 0) (hk : k ≠ 0) (hlam : lam ≠ 0) (hh : h ≠ 0)
    (hdegree : P.natDegree = 2 * m + 1)
    (hlead : P.leadingCoeff = C lam * h ^ P.natDegree)
    (hjac : jacobian P
      (variableQuadraticCoordinate (C eps * h ^ 2) g f) = CC k) :
    IsUnit h := by
  obtain ⟨H, B, hrepr⟩ :=
    exists_fractionAffineTransport_parityDecomposition
      (f := f) P heps
  have hrepr' : fractionAffineTransport eps h g P =
      H.comp (fractionCenteredQuadratic eps h g f) +
        X * (B.comp (fractionCenteredQuadratic eps h g f)) := by
    simpa only [fractionCenteredQuadratic] using hrepr
  have cert : Certificate eps k lam h g f P H B m :=
    certificate_of_odd_degree_keller_parityRepresentation
      P H B heps hk hlam hh hdegree hlead hjac hrepr'
  have hdiv : h ∣ g := h_dvd_g_of_certificate heps hh cert
  exact isUnit_of_certificate_of_dvd cert heps hk hh hdiv

/-- In every Keller pair whose second coordinate is quadratic in `y`, the
quadratic leading coefficient is a unit of `K[X]`, hence cannot genuinely
depend on `x`.
@isnad1 id=isunit.3h6v.s7.22f4b1cb5472 from=translated src=- shape=a0315d19 vocab=6178ceae
-/
theorem quadratic_leadingCoefficient_isUnit
    {P : K[X][Y]} {a g f : K[X]} {k : K}
    (ha : a ≠ 0) (hk : k ≠ 0)
    (hjac : jacobian P (variableQuadraticCoordinate a g f) = CC k) :
    IsUnit a := by
  obtain ⟨_H, R, _hdecomposition, hRjac, hRodd⟩ :=
    exists_target_shear_add_odd_residual ha hk hjac
  obtain ⟨eps, h, lam, heps, hlam, haShape, hRlead⟩ :=
    odd_natDegree_quadraticCoeff_and_leadingCoeff_shape
      ha hRodd hRjac
  have hh : h ≠ 0 := by
    intro hzero
    apply ha
    rw [haShape, hzero]
    simp
  obtain ⟨m, hRdegree⟩ := hRodd
  have hRjac' :
      jacobian R
        (variableQuadraticCoordinate (C eps * h ^ 2) g f) = CC k := by
    rw [← haShape]
    exact hRjac
  have hunit : IsUnit h :=
    odd_residual_squareRoot_isUnit R heps hk hlam hh
      hRdegree hRlead hRjac'
  rw [haShape]
  exact (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr heps)).mul
    (hunit.pow 2)

/-- Evaluation of the polynomial map with a possibly variable quadratic
leading coefficient.-/
def variableQuadraticCoordinateMap
    (P : K[X][Y]) (a g f : K[X]) (p : K × K) : K × K :=
  (P.evalEval p.1 p.2,
    (variableQuadraticCoordinate a g f).evalEval p.1 p.2)

omit [CharZero K] in
/-- A scalar specialization of the variable-leading coordinate is the
constant-leading coordinate definitionally.
@isnad1 id=eq.0h4v.s7.904b609c52c5 from=translated src=- shape=685195c5 vocab=b6a352e9
-/
theorem variableQuadraticCoordinate_C_eq
    (eps : K) (g f : K[X]) :
    variableQuadraticCoordinate (C eps) g f =
      quadraticCoordinate eps g f := by
  rfl

omit [CharZero K] in
/-- The corresponding evaluation maps agree under the scalar
specialization.
@isnad1 id=eq.0h5v.s7.ba82a3da41bc from=translated src=- shape=c9533cec vocab=593c1297
-/
theorem variableQuadraticCoordinateMap_C_eq
    (P : K[X][Y]) (eps : K) (g f : K[X]) :
    variableQuadraticCoordinateMap P (C eps) g f =
      quadraticCoordinateMap P eps g f := by
  rfl

/-- Therefore every Keller map whose second coordinate is quadratic in `y`
is bijective.
@isnad1 id=bijectiv.3h6v.s7.ca55252c63cb from=translated src=- shape=a43b46f0 vocab=8bde1e3e
-/
theorem variableLeadingQuadratic_bijective
    {P : K[X][Y]} {a g f : K[X]} {k : K}
    (ha : a ≠ 0) (hk : k ≠ 0)
    (hjac : jacobian P (variableQuadraticCoordinate a g f) = CC k) :
    Function.Bijective (variableQuadraticCoordinateMap P a g f) := by
  have haUnit := quadratic_leadingCoefficient_isUnit ha hk hjac
  obtain ⟨eps, hepsUnit, hscalar⟩ := Polynomial.isUnit_iff.mp haUnit
  have heps : eps ≠ 0 := isUnit_iff_ne_zero.mp hepsUnit
  have hjacScalar :
      jacobian P (quadraticCoordinate eps g f) = CC k := by
    rw [← variableQuadraticCoordinate_C_eq]
    rw [hscalar]
    exact hjac
  rw [← hscalar, variableQuadraticCoordinateMap_C_eq]
  exact constantLeadingQuadratic_bijective heps hk hjacScalar

omit [CharZero K] in
/-- With zero quadratic coefficient, `variableQuadraticCoordinate` is exactly
the affine coordinate.
@isnad1 id=eq.0h3v.s6.da397491a4dd from=translated src=- shape=b2996637 vocab=79efd45d
-/
theorem variableQuadraticCoordinate_zero_eq (g f : K[X]) :
    variableQuadraticCoordinate 0 g f = affineCoordinate g f := by
  simp [variableQuadraticCoordinate, affineCoordinate]

omit [CharZero K] in
/-- The corresponding evaluation map also reduces to the affine-coordinate
map.
@isnad1 id=eq.0h4v.s6.6043000690af from=translated src=- shape=745ebfd0 vocab=f482c113
-/
theorem variableQuadraticCoordinateMap_zero_eq
    (P : K[X][Y]) (g f : K[X]) :
    variableQuadraticCoordinateMap P 0 g f =
      affineCoordinateMap P g f := by
  funext p
  simp only [variableQuadraticCoordinateMap, affineCoordinateMap,
    variableQuadraticCoordinate_zero_eq]

/-- Full at-most-quadratic wrapper.  The nonzero branch is the
variable-leading theorem, while the zero branch is the affine-coordinate
theorem.
@isnad1 id=bijectiv.2h6v.s7.e6aad1721b56 from=translated src=- shape=f3a63253 vocab=8bde1e3e
-/
theorem variableLeadingQuadratic_bijective_full
    {P : K[X][Y]} {a g f : K[X]} {k : K}
    (hk : k ≠ 0)
    (hjac : jacobian P (variableQuadraticCoordinate a g f) = CC k) :
    Function.Bijective (variableQuadraticCoordinateMap P a g f) := by
  by_cases ha : a = 0
  · subst a
    have hjacAffine : jacobian P (affineCoordinate g f) = CC k := by
      rw [← variableQuadraticCoordinate_zero_eq]
      exact hjac
    rw [variableQuadraticCoordinateMap_zero_eq]
    exact affineCoordinate_bijective hk hjacAffine
  · exact variableLeadingQuadratic_bijective ha hk hjac

end JacobianTwo.VariableLeadingQuadraticConclusion
