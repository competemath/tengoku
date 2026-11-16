/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
import Tengoku.JacobianTwo.JacobianTwo.Counterexample
import Tengoku.Seed.Tactic.FieldSimp
import Tengoku.Seed.Tactic.FinCases
import Tengoku.Seed.Tactic.LinearCombination
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The cubic fiber of the announced three-dimensional map

This module records the exact algebra behind the fiber coordinate used in the
analysis of the announced map.  For a target `(a, b, c)`, the auxiliary
coordinate `T` satisfies

`p(T) = c * T^3 - 2 * T^2 + b * T - 2 * a = 0`,

and the quantity `r(T) = p'(T)` reconstructs the source whenever it is
nonzero.  The final lemmas give the cancellations used when `T` is large.
-/

noncomputable section

namespace JacobianTwo.CubicFiber

section Algebra

variable {R : Type*} [CommRing R]

/-- The scalar cubic equation for a fiber over `(a, b, c)`.-/
def p (a b c T : R) : R := c * T ^ 3 - 2 * T ^ 2 + b * T - 2 * a

/-- The derivative of the fiber cubic, evaluated at `T`.-/
def r (b c T : R) : R := 3 * c * T ^ 2 - 4 * T + b

/-- The polynomial version of `p`.-/
def fiberPolynomial (a b c : R) : Polynomial R :=
  Polynomial.C c * Polynomial.X ^ 3 - 2 * Polynomial.X ^ 2 +
    Polynomial.C b * Polynomial.X - Polynomial.C (2 * a)

/-- The polynomial version of `r`.-/
def derivativePolynomial (b c : R) : Polynomial R :=
  Polynomial.C (3 * c) * Polynomial.X ^ 2 - 4 * Polynomial.X +
    Polynomial.C b

/-- Evaluation of the polynomial fiber equation is the scalar expression
`p`.-/
theorem eval_fiberPolynomial (a b c T : R) :
    (fiberPolynomial a b c).eval T = p a b c T := by
  simp [fiberPolynomial, p]

/-- Formal differentiation of the cubic gives `derivativePolynomial`.-/
theorem derivative_fiberPolynomial (a b c : R) :
    (fiberPolynomial a b c).derivative = derivativePolynomial b c := by
  simp [fiberPolynomial, derivativePolynomial, Polynomial.C_ofNat]
  ring

/-- Evaluation of the formal derivative is the scalar expression `r`.-/
theorem eval_derivativePolynomial (b c T : R) :
    (derivativePolynomial b c).eval T = r b c T := by
  simp [derivativePolynomial, r]

/-- The equation cutting out the candidate nonproper-value set.-/
def nonproperPolynomial (a b c : R) : R :=
  27 * a ^ 2 * c ^ 2 - 18 * a * b * c + 16 * a + b ^ 3 * c - b ^ 2

/-- The coefficient formula for the discriminant of
`c*T^3 - 2*T^2 + b*T - 2*a`.  It is kept explicit so the certificate does not
depend on a normalization convention for polynomial discriminants.-/
def cubicDiscriminant (a b c : R) : R :=
  18 * c * (-2) * b * (-2 * a) -
    4 * (-2 : R) ^ 3 * (-2 * a) +
    (-2 : R) ^ 2 * b ^ 2 -
    4 * c * b ^ 3 -
    27 * c ^ 2 * (-2 * a) ^ 2

/-- The universal cubic discriminant coefficient expression is exactly `-4`
times the nonproper-set polynomial.-/
theorem cubicDiscriminant_eq (a b c : R) :
    cubicDiscriminant a b c = -4 * nonproperPolynomial a b c := by
  simp [cubicDiscriminant, nonproperPolynomial]
  ring

/-- Viewed as a quadratic in `a`, the polynomial cutting out the discriminant
hypersurface has discriminant `-4 * (3*b*c - 4)^3`.  The identity is the
finite algebraic input to the generic nonsquare-discriminant argument.-/
theorem nonproperPolynomial_discriminantInA (b c : R) :
    (16 - 18 * b * c) ^ 2 -
        4 * (27 * c ^ 2) * (b ^ 3 * c - b ^ 2) =
      -4 * (3 * b * c - 4) ^ 3 := by
  ring

/-- An integral-coefficient Bezout certificate for the common-root
condition.  Specializing both `p` and `r` to zero leaves
`2 * nonproperPolynomial = 0`.-/
theorem resultant_certificate (a b c T : R) :
    ((-27 * a * c ^ 2 + 15 * b * c - 16) +
        (-9 * b * c ^ 2 + 12 * c) * T) * p a b c T +
      ((-6 * a * c + 2 * b ^ 2 * c - 2 * b) +
        (9 * a * c ^ 2 - 7 * b * c + 8) * T +
        (3 * b * c ^ 2 - 4 * c) * T ^ 2) * r b c T =
      2 * nonproperPolynomial a b c := by
  simp [p, r, nonproperPolynomial]
  ring

/-- A common root of the fiber cubic and its derivative lies on the proposed
nonproper-value hypersurface.-/
theorem common_root_forces_nonproperPolynomial_zero
    {K : Type*} [Field K] [CharZero K] (a b c T : K)
    (hp : p a b c T = 0) (hr : r b c T = 0) :
    nonproperPolynomial a b c = 0 := by
  have h := resultant_certificate a b c T
  rw [hp, hr] at h
  have htwo : (2 : K) * nonproperPolynomial a b c = 0 := by
    simpa using h.symm
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- The quadratic expression that controls the large-`T` chart.-/
def escapeDenominator (a b T : R) : R := T ^ 2 - b * T + 3 * a

/-- A denominator-free elimination identity.-/
theorem derivative_mul_eq (a b c T : R) :
    T * r b c T = 3 * p a b c T + 2 * escapeDenominator a b T := by
  simp [p, r, escapeDenominator]
  ring

end Algebra

section Reconstruction

variable {K : Type*} [Field K] [CharZero K]

/-- First coordinate of the announced map, written as a scalar expression.-/
def announcedFirst (x y z : K) : K :=
  (1 + x * y) ^ 3 * z + y ^ 2 * (1 + x * y) * (4 + 3 * x * y)

/-- Second coordinate of the announced map, written as a scalar expression.-/
def announcedSecond (x y z : K) : K :=
  y + 3 * x * (1 + x * y) ^ 2 * z +
    3 * x * y ^ 2 * (4 + 3 * x * y)

/-- Third coordinate of the announced map, written as a scalar expression.-/
def announcedThird (x y z : K) : K :=
  2 * x - 3 * x ^ 2 * y - x ^ 3 * z

/-- The scalar form of the announced polynomial map.-/
def announcedMap (q : Fin 3 → K) : Fin 3 → K :=
  ![announcedFirst (q 0) (q 1) (q 2),
    announcedSecond (q 0) (q 1) (q 2),
    announcedThird (q 0) (q 1) (q 2)]

omit [CharZero K] in
/-- The simple projective root at infinity, present when the target's third
coordinate is zero, reconstructs to this finite source point.-/
theorem announcedMap_at_x_zero (a b : K) :
    announcedMap ![0, b, a - 4 * b ^ 2] = ![a, b, 0] := by
  funext i
  fin_cases i
  · simp [announcedMap, announcedFirst]
    ring
  · simp [announcedMap, announcedSecond]
  · simp [announcedMap, announcedThird]

/-- Over `ℂ`, the scalar definition is the map certified in
`Counterexample`.-/
theorem announcedMap_eq_complexMap (q : Fin 3 → ℂ) :
    announcedMap q = Counterexample.complexMap q := by
  rw [Counterexample.complexMap_formula]
  rfl

/-- The reconstructed `x` coordinate on the chart `r ≠ 0`.-/
def reconstructedX (rho : K) : K := 2 / rho

/-- The reconstructed `y` coordinate.-/
def reconstructedY (T rho : K) : K := T - rho / 2

/-- The reconstructed `z` coordinate.-/
def reconstructedZ (c T rho : K) : K :=
  5 * rho ^ 2 / 4 - 3 * T * rho / 2 - c * rho ^ 3 / 8

/-- The reconstructed source point.-/
def reconstructedSource (b c T : K) : Fin 3 → K :=
  let rho := r b c T
  ![reconstructedX rho, reconstructedY T rho, reconstructedZ c T rho]

/-- The discriminant hypersurface parametrized by a repeated finite root.-/
def repeatedRootTarget (T c : K) : Fin 3 → K :=
  ![T ^ 2 - c * T ^ 3, 4 * T - 3 * c * T ^ 2, c]

omit [CharZero K] in
/-- The repeated-root parametrization lies on the discriminant
hypersurface.-/
theorem repeatedRootTarget_nonproperPolynomial (T c : K) :
    nonproperPolynomial (repeatedRootTarget T c 0)
        (repeatedRootTarget T c 1) (repeatedRootTarget T c 2) = 0 := by
  simp [repeatedRootTarget, nonproperPolynomial]
  ring

/-- Parametrization of the targets whose projective fiber cubic is a cube.-/
def tripleRootTarget (T : K) : Fin 3 → K :=
  ![T ^ 2 / 3, 2 * T, 2 / (3 * T)]

/-- The triple-root targets are exactly on the two displayed equations for
the omitted curve.-/
theorem tripleRootTarget_on_omittedCurve (T : K) (hT : T ≠ 0) :
    3 * tripleRootTarget T 1 * tripleRootTarget T 2 = 4 ∧
      (tripleRootTarget T 1) ^ 2 = 12 * tripleRootTarget T 0 := by
  constructor <;> simp [tripleRootTarget] <;> field_simp [hT] <;> ring

/-- At a target on the omitted curve, the fiber polynomial is an exact cube.-/
theorem p_tripleRootTarget (T U : K) (hT : T ≠ 0) :
    p (tripleRootTarget T 0) (tripleRootTarget T 1)
        (tripleRootTarget T 2) U =
      (2 / (3 * T)) * (U - T) ^ 3 := by
  simp [p, tripleRootTarget]
  field_simp [hT]
  ring

/-- The source used to approach a repeated-root target while prescribing the
fiber derivative to be `epsilon`.-/
def escapingSource (T c epsilon : K) : Fin 3 → K :=
  ![reconstructedX epsilon, reconstructedY T epsilon,
    reconstructedZ c T epsilon]

/-- Raw first-coordinate reconstruction, before imposing the cubic equation
or substituting the derivative formula.-/
theorem announcedFirst_reconstructed_raw (c T rho : K) (hrho : rho ≠ 0) :
    announcedFirst (reconstructedX rho) (reconstructedY T rho)
        (reconstructedZ c T rho) =
      T * (-2 * c * T ^ 2 + 2 * T + rho) / 2 := by
  simp [announcedFirst, reconstructedX, reconstructedY, reconstructedZ]
  field_simp [hrho]
  ring

/-- Raw second-coordinate reconstruction.-/
theorem announcedSecond_reconstructed_raw (c T rho : K) (hrho : rho ≠ 0) :
    announcedSecond (reconstructedX rho) (reconstructedY T rho)
        (reconstructedZ c T rho) =
      -3 * c * T ^ 2 + 4 * T + rho := by
  simp [announcedSecond, reconstructedX, reconstructedY, reconstructedZ]
  field_simp [hrho]
  ring

/-- Raw third-coordinate reconstruction.-/
theorem announcedThird_reconstructed_raw (c T rho : K) (hrho : rho ≠ 0) :
    announcedThird (reconstructedX rho) (reconstructedY T rho)
        (reconstructedZ c T rho) = c := by
  simp [announcedThird, reconstructedX, reconstructedY, reconstructedZ]
  field_simp [hrho]
  ring

/-- Exact image of the escaping family.  As `epsilon` tends to zero, the
first source coordinate is `2/epsilon` while the image tends to
`repeatedRootTarget T c`.  This theorem certifies the algebraic identity; the
limit statement itself is kept in the accompanying mathematical note.-/
theorem announcedMap_escapingSource (T c epsilon : K) (hepsilon : epsilon ≠ 0) :
    announcedMap (escapingSource T c epsilon) =
      ![T ^ 2 - c * T ^ 3 + epsilon * T / 2,
        4 * T - 3 * c * T ^ 2 + epsilon, c] := by
  have hfirst := announcedFirst_reconstructed_raw c T epsilon hepsilon
  have hsecond := announcedSecond_reconstructed_raw c T epsilon hepsilon
  have hthird := announcedThird_reconstructed_raw c T epsilon hepsilon
  funext i
  fin_cases i <;>
    simp [announcedMap, escapingSource, hfirst, hsecond, hthird] <;>
    ring

/-- If `T` lies on the fiber cubic and `r(T)` is nonzero, reconstruction sends
the source to the target `(a, b, c)`.-/
theorem announcedMap_reconstructed (a b c T : K)
    (hp : p a b c T = 0) (hr : r b c T ≠ 0) :
    announcedMap (reconstructedSource b c T) = ![a, b, c] := by
  have hfirst :
      announcedFirst (reconstructedX (r b c T))
          (reconstructedY T (r b c T)) (reconstructedZ c T (r b c T)) = a := by
    rw [announcedFirst_reconstructed_raw c T (r b c T) hr]
    field_simp
    simp [p, r] at hp ⊢
    linear_combination hp
  have hsecond :
      announcedSecond (reconstructedX (r b c T))
          (reconstructedY T (r b c T)) (reconstructedZ c T (r b c T)) = b := by
    rw [announcedSecond_reconstructed_raw c T (r b c T) hr]
    simp [r]
    ring
  have hthird :
      announcedThird (reconstructedX (r b c T))
          (reconstructedY T (r b c T)) (reconstructedZ c T (r b c T)) = c :=
    announcedThird_reconstructed_raw c T (r b c T) hr
  funext i
  fin_cases i <;>
    simp [announcedMap, reconstructedSource, hfirst, hsecond, hthird]

omit [CharZero K] in
/-- Solving the cubic equation for `c`, valid away from `T = 0`.-/
theorem eliminate_c (a b c T : K) (hp : p a b c T = 0) (hT : T ≠ 0) :
    c = (2 * T ^ 2 - b * T + 2 * a) / T ^ 3 := by
  field_simp [hT]
  simp [p] at hp ⊢
  linear_combination hp

omit [CharZero K] in
/-- The exact cancellation behind
`x = T / (T^2 - b*T + 3*a)` after eliminating `c`.-/
theorem largeT_x_cancellation (a b c T : K)
    (hp : p a b c T = 0) (hT : T ≠ 0) (hr : r b c T ≠ 0) :
    reconstructedX (r b c T) = T / escapeDenominator a b T := by
  have hder : T * r b c T = 2 * escapeDenominator a b T := by
    simpa [hp] using derivative_mul_eq a b c T
  have hden : escapeDenominator a b T ≠ 0 := by
    intro hzero
    have hzero' : T * r b c T = 0 := by simp [hder, hzero]
    exact (mul_ne_zero hT hr) hzero'
  simp [reconstructedX]
  field_simp [hr, hden]
  simpa [mul_comm] using hder.symm

/-- The exact cancellation behind `y = b - 3*a/T` after eliminating `c`.-/
theorem largeT_y_cancellation (a b c T : K)
    (hp : p a b c T = 0) (hT : T ≠ 0) :
    reconstructedY T (r b c T) = b - 3 * a / T := by
  simp [reconstructedY]
  field_simp [hT]
  simp [p, r] at hp ⊢
  linear_combination -3 * hp

/-- The polynomial in `u = 1/T` giving the exact inverse-power expansion of
the reconstructed `z` coordinate.-/
def zInfinityExpansion (a b u : K) : K :=
  a - 4 * b ^ 2 +
    (21 * a * b + 5 * b ^ 3) * u +
    (-27 * a ^ 2 - 42 * a * b ^ 2 - b ^ 4) * u ^ 2 +
    (117 * a ^ 2 * b + 11 * a * b ^ 3) * u ^ 3 +
    (-108 * a ^ 3 - 45 * a ^ 2 * b ^ 2) * u ^ 4 +
    81 * a ^ 3 * b * u ^ 5 -
    54 * a ^ 4 * u ^ 6

/-- After eliminating `c` with the cubic equation, the reconstructed `z`
coordinate is exactly a polynomial in `1/T`, with constant term
`a - 4*b^2`.-/
theorem largeT_z_cancellation (a b c T : K)
    (hp : p a b c T = 0) (hT : T ≠ 0) :
    reconstructedZ c T (r b c T) = zInfinityExpansion a b (1 / T) := by
  rw [eliminate_c a b c T hp hT]
  simp [reconstructedZ, r, zInfinityExpansion]
  field_simp [hT]
  ring

end Reconstruction

end JacobianTwo.CubicFiber
