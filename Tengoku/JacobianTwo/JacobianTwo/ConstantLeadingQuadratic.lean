/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
import Tengoku.JacobianTwo.JacobianTwo.AffineCoordinate
import Tengoku.Seed.Tactic.FieldSimp
import Tengoku.Seed.Tactic.LinearCombination
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Keller maps with a constant-leading quadratic coordinate

This module studies a plane polynomial map whose second coordinate is
quadratic in `y` with nonzero constant leading coefficient, while imposing no
degree bound on its first coordinate.  The formal Jacobian forces the
quadratic discriminant to be affine in `x`.
-/

noncomputable section

open scoped Polynomial Polynomial.Bivariate

namespace JacobianTwo.ConstantLeadingQuadratic

open Polynomial
open JacobianTwo.AffineCoordinate

variable {K : Type*} [Field K]

@[simp]
theorem CC_mul_scalar (a b : K) : CC (a * b) = CC a * CC b := by
  change C (C (a * b)) = C (C a) * C (C b)
  rw [C_mul, C_mul]

@[simp]
theorem CC_add_scalar (a b : K) : CC (a + b) = CC a + CC b := by
  change C (C (a + b)) = C (C a) + C (C b)
  rw [C_add, C_add]

@[simp]
theorem CC_sub_scalar (a b : K) : CC (a - b) = CC a - CC b := by
  change C (C (a - b)) = C (C a) - C (C b)
  rw [map_sub, map_sub]

@[simp]
theorem CC_pow_scalar (a : K) (n : ℕ) : CC (a ^ n) = CC a ^ n := by
  change C (C (a ^ n)) = C (C a) ^ n
  rw [map_pow, map_pow]

@[simp]
theorem CC_zero_scalar : CC (0 : K) = (0 : K[X][Y]) := by
  change C (C (0 : K)) = (0 : K[X][Y])
  rw [map_zero, map_zero]

@[simp]
theorem CC_one_scalar : CC (1 : K) = (1 : K[X][Y]) := by
  change C (C (1 : K)) = (1 : K[X][Y])
  rw [map_one, map_one]

@[simp]
theorem CC_natCast (n : ℕ) : CC (n : K) = (n : K[X][Y]) := by
  change C (C (n : K)) = (n : K[X][Y])
  rw [map_natCast, map_natCast]

@[simp]
theorem CC_ofNat_scalar (n : ℕ) [n.AtLeastTwo] :
    CC (ofNat(n) : K) = (ofNat(n) : K[X][Y]) := by
  change C (C (ofNat(n) : K)) = (ofNat(n) : K[X][Y])
  rw [C_ofNat, C_ofNat]

@[simp]
theorem C_natCast_inner (n : ℕ) : C (n : K[X]) = (n : K[X][Y]) := by
  rw [map_natCast]

/-- A polynomial that is quadratic in `y` with scalar leading coefficient.-/
def quadraticCoordinate (eps : K) (g f : K[X]) : K[X][Y] :=
  CC eps * Y ^ 2 + C g * Y + C f

/-- Twice the leading coefficient times `y`, plus the linear coefficient.-/
def criticalLinear (eps : K) (g : K[X]) : K[X][Y] :=
  CC (2 * eps) * Y + C g

/-- The discriminant of `eps*y^2 + g(x)*y + f(x)` as a quadratic in `y`.-/
def discriminant (eps : K) (g f : K[X]) : K[X] :=
  g ^ 2 - C (4 * eps) * f

/-- The polynomial section on which the derivative of the quadratic
coordinate with respect to `y` vanishes.-/
def criticalSection (eps : K) (g : K[X]) : K[X] :=
  -(C ((2 * eps)⁻¹) * g)

@[simp]
theorem yDerivative_quadraticCoordinate (eps : K) (g f : K[X]) :
    yDerivative (quadraticCoordinate eps g f) = criticalLinear eps g := by
  simp [quadraticCoordinate, criticalLinear, yDerivative_apply, derivative_pow, C_ofNat]
  ring

@[simp]
theorem xDerivative_quadraticCoordinate (eps : K) (g f : K[X]) :
    xDerivative (quadraticCoordinate eps g f) =
      C (derivative g) * Y + C (derivative f) := by
  simp [quadraticCoordinate, Derivation.leibniz]

@[simp]
theorem yDerivative_criticalLinear (eps : K) (g : K[X]) :
    yDerivative (criticalLinear eps g) = CC (2 * eps) := by
  simp [criticalLinear]

@[simp]
theorem xDerivative_criticalLinear (eps : K) (g : K[X]) :
    xDerivative (criticalLinear eps g) = C (derivative g) := by
  rw [criticalLinear, map_add, Derivation.leibniz, xDerivative_CC,
    xDerivative_Y, xDerivative_C]
  simp

/-- Completing the square without introducing denominators.-/
theorem criticalLinear_sq_sub (eps : K) (g f : K[X]) :
    criticalLinear eps g ^ 2 -
        CC (4 * eps) * quadraticCoordinate eps g f =
      C (discriminant eps g f) := by
  simp [criticalLinear, quadraticCoordinate, discriminant, C_ofNat]
  ring

/-- The Jacobian of the critical linear form and the quadratic coordinate is
half the derivative of the discriminant.  This denominator-free form remains
valid before assuming characteristic zero.-/
theorem two_mul_jacobian_criticalLinear (eps : K) (g f : K[X]) :
    CC 2 * jacobian (criticalLinear eps g) (quadraticCoordinate eps g f) =
      C (derivative (discriminant eps g f)) := by
  rw [jacobian, xDerivative_criticalLinear, yDerivative_quadraticCoordinate,
    yDerivative_criticalLinear, xDerivative_quadraticCoordinate]
  simp [discriminant, derivative_sub, derivative_pow, criticalLinear, C_ofNat]
  ring

theorem derivative_discriminant (eps : K) (g f : K[X]) :
    derivative (discriminant eps g f) =
      C 2 * g * derivative g - C (4 * eps) * derivative f := by
  simp [discriminant, derivative_sub, derivative_pow, C_ofNat]

theorem eval_criticalLinear_at_criticalSection [CharZero K]
    {eps : K} (g : K[X])
    (heps : eps ≠ 0) :
    (criticalLinear eps g).eval (criticalSection eps g) = 0 := by
  have htwo : (2 : K) ≠ 0 := by norm_num
  have htwoeps : 2 * eps ≠ 0 := mul_ne_zero htwo heps
  have hcoeff : C (2 * eps) * C ((2 * eps)⁻¹) = (1 : K[X]) := by
    calc
      C (2 * eps) * C ((2 * eps)⁻¹) =
          C ((2 * eps) * (2 * eps)⁻¹) := C_mul.symm
      _ = C 1 := by rw [mul_inv_cancel₀ htwoeps]
      _ = 1 := C_1
  rw [criticalLinear, criticalSection]
  simp only [eval_add, eval_mul, eval_C, eval_X]
  calc
    C (2 * eps) * (-(C ((2 * eps)⁻¹) * g)) + g =
        -(C (2 * eps) * C ((2 * eps)⁻¹)) * g + g := by ring
    _ = 0 := by rw [hcoeff]; ring

theorem four_eps_mul_eval_xDerivative_at_criticalSection [CharZero K]
    {eps : K}
    (g f : K[X]) (heps : eps ≠ 0) :
    C (4 * eps) *
        (xDerivative (quadraticCoordinate eps g f)).eval
          (criticalSection eps g) =
      -derivative (discriminant eps g f) := by
  have htwo : (2 : K) ≠ 0 := by norm_num
  have htwoeps : 2 * eps ≠ 0 := mul_ne_zero htwo heps
  have hratio_scalar : (4 * eps) * (2 * eps)⁻¹ = (2 : K) := by
    field_simp
    norm_num
  have hratio : C (4 * eps) * C ((2 * eps)⁻¹) = C (2 : K) := by
    calc
      C (4 * eps) * C ((2 * eps)⁻¹) =
          C ((4 * eps) * (2 * eps)⁻¹) := C_mul.symm
      _ = C 2 := by rw [hratio_scalar]
  rw [xDerivative_quadraticCoordinate]
  simp only [eval_add, eval_mul, eval_C, eval_X, criticalSection]
  rw [derivative_discriminant]
  calc
    C (4 * eps) *
        (derivative g * (-(C ((2 * eps)⁻¹) * g)) + derivative f) =
        -(C (4 * eps) * C ((2 * eps)⁻¹)) * derivative g * g +
          C (4 * eps) * derivative f := by ring
    _ = -(C 2 * g * derivative g - C (4 * eps) * derivative f) := by
      rw [hratio]
      ring

/-- Evaluating the actual bivariate Jacobian on the critical section turns
the Keller equation into a product equation in `K[x]`.-/
theorem eval_yDerivative_mul_derivative_discriminant [CharZero K]
    {P : K[X][Y]} {eps k : K} {g f : K[X]}
    (heps : eps ≠ 0)
    (hjac : jacobian P (quadraticCoordinate eps g f) = CC k) :
    (yDerivative P).eval (criticalSection eps g) *
        derivative (discriminant eps g f) =
      C (4 * eps * k) := by
  let z := criticalSection eps g
  let py := (yDerivative P).eval z
  let qx := (xDerivative (quadraticCoordinate eps g f)).eval z
  have hcrit : (yDerivative (quadraticCoordinate eps g f)).eval z = 0 := by
    rw [yDerivative_quadraticCoordinate]
    exact eval_criticalLinear_at_criticalSection g heps
  have heval := congrArg (fun R : K[X][Y] => R.eval z) hjac
  have heval' : -(py * qx) = C k := by
    simpa only [jacobian, eval_sub, eval_mul, hcrit, mul_zero, zero_sub,
      eval_C, py, qx] using heval
  have hqx : C (4 * eps) * qx =
      -derivative (discriminant eps g f) := by
    exact four_eps_mul_eval_xDerivative_at_criticalSection g f heps
  have hdisc : derivative (discriminant eps g f) = -(C (4 * eps) * qx) := by
    have hneg := congrArg Neg.neg hqx
    simpa using hneg.symm
  calc
    (yDerivative P).eval (criticalSection eps g) *
          derivative (discriminant eps g f) =
        py * (-(C (4 * eps) * qx)) := by rw [hdisc]
    _ = C (4 * eps) * (-(py * qx)) := by ring
    _ = C (4 * eps) * C k := by rw [heval']
    _ = C (4 * eps * k) := C_mul.symm

/-- A nonzero constant Jacobian forces the quadratic discriminant to be
affine.  The scalar `rho` is the value of `P_y` on the critical section.-/
theorem affine_discriminant [CharZero K]
    {P : K[X][Y]} {eps k : K} {g f : K[X]}
    (heps : eps ≠ 0) (hk : k ≠ 0)
    (hjac : jacobian P (quadraticCoordinate eps g f) = CC k) :
    ∃ rho A B : K,
      rho ≠ 0 ∧ A ≠ 0 ∧ rho * A = 4 * eps * k ∧
      (yDerivative P).eval (criticalSection eps g) = C rho ∧
      discriminant eps g f = C A * X + C B := by
  let py := (yDerivative P).eval (criticalSection eps g)
  let dDelta := derivative (discriminant eps g f)
  have hprod : py * dDelta = C (4 * eps * k) :=
    eval_yDerivative_mul_derivative_discriminant heps hjac
  have hfour : (4 : K) ≠ 0 := by norm_num
  have hscalar : 4 * eps * k ≠ 0 := mul_ne_zero (mul_ne_zero hfour heps) hk
  have hrhs : C (4 * eps * k) ≠ (0 : K[X]) := C_ne_zero.mpr hscalar
  have hpy : py ≠ 0 := by
    intro hzero
    apply hrhs
    rw [← hprod, hzero, zero_mul]
  have hdDelta : dDelta ≠ 0 := by
    intro hzero
    apply hrhs
    rw [← hprod, hzero, mul_zero]
  have hdegrees : py.natDegree + dDelta.natDegree = 0 := by
    rw [← natDegree_mul hpy hdDelta, hprod]
    exact natDegree_C _
  obtain ⟨hpydegree, hddegree⟩ := Nat.add_eq_zero_iff.mp hdegrees
  let rho := py.coeff 0
  let A := dDelta.coeff 0
  have hpyC : py = C rho := by
    dsimp [rho]
    exact eq_C_of_natDegree_eq_zero hpydegree
  have hdC : dDelta = C A := by
    dsimp [A]
    exact eq_C_of_natDegree_eq_zero hddegree
  have hrho : rho ≠ 0 := by
    intro hzero
    apply hpy
    rw [hpyC, hzero, C_0]
  have hA : A ≠ 0 := by
    intro hzero
    apply hdDelta
    rw [hdC, hzero, C_0]
  have hrhoA : rho * A = 4 * eps * k := by
    rw [hpyC, hdC, ← C_mul] at hprod
    exact C_injective hprod
  let B := (discriminant eps g f - C A * X).coeff 0
  have hconstant : discriminant eps g f - C A * X = C B := by
    dsimp [B]
    apply eq_C_of_derivative_eq_zero
    rw [derivative_sub, ← show dDelta = derivative (discriminant eps g f) by rfl,
      hdC, derivative_C_mul_X, sub_self]
  have hDelta : discriminant eps g f = C A * X + C B := by
    linear_combination hconstant
  exact ⟨rho, A, B, hrho, hA, hrhoA, hpyC, hDelta⟩

/-- Evaluation of the explicit source-coordinate pair `(s,Q)`.-/
def coordinatePairMap (eps : K) (g f : K[X]) (p : K × K) : K × K :=
  ((criticalLinear eps g).evalEval p.1 p.2,
    (quadraticCoordinate eps g f).evalEval p.1 p.2)

/-- Explicit inverse to `(x,y) ↦ (s,Q)` once the discriminant is `A*x+B`.-/
def coordinatePairInverse (eps A B : K) (g : K[X]) (p : K × K) : K × K :=
  let x := (p.1 ^ 2 - 4 * eps * p.2 - B) / A
  (x, (p.1 - g.eval x) / (2 * eps))

@[simp]
theorem evalEval_criticalLinear (eps x y : K) (g : K[X]) :
    (criticalLinear eps g).evalEval x y = 2 * eps * y + g.eval x := by
  simp [criticalLinear, evalEval]

@[simp]
theorem evalEval_quadraticCoordinate (eps x y : K) (g f : K[X]) :
    (quadraticCoordinate eps g f).evalEval x y =
      eps * y ^ 2 + g.eval x * y + f.eval x := by
  simp [quadraticCoordinate, evalEval]

theorem eval_discriminant_of_eq_affine {eps A B x : K} {g f : K[X]}
    (hDelta : discriminant eps g f = C A * X + C B) :
    (discriminant eps g f).eval x = A * x + B := by
  rw [hDelta]
  simp

theorem coordinatePairInverse_left [CharZero K]
    {eps A B : K} {g f : K[X]}
    (heps : eps ≠ 0) (hA : A ≠ 0)
    (hDelta : discriminant eps g f = C A * X + C B) :
    Function.LeftInverse (coordinatePairInverse eps A B g)
      (coordinatePairMap eps g f) := by
  rintro ⟨x, y⟩
  let s := 2 * eps * y + g.eval x
  let q := eps * y ^ 2 + g.eval x * y + f.eval x
  have hdisc : g.eval x ^ 2 - 4 * eps * f.eval x = A * x + B := by
    have h := eval_discriminant_of_eq_affine (x := x) hDelta
    simpa [discriminant] using h
  have hsq : s ^ 2 - 4 * eps * q = A * x + B := by
    dsimp [s, q]
    calc
      (2 * eps * y + g.eval x) ^ 2 -
          4 * eps * (eps * y ^ 2 + g.eval x * y + f.eval x) =
        g.eval x ^ 2 - 4 * eps * f.eval x := by ring
      _ = A * x + B := hdisc
  let x' := (s ^ 2 - 4 * eps * q - B) / A
  have hx : x' = x := by
    dsimp [x']
    field_simp
    linear_combination hsq
  simp only [coordinatePairMap, evalEval_criticalLinear,
    evalEval_quadraticCoordinate, coordinatePairInverse]
  change (x', (s - g.eval x') / (2 * eps)) = (x, y)
  apply Prod.ext
  · exact hx
  · simp only [hx]
    dsimp [s]
    field_simp
    ring

theorem coordinatePairInverse_right [CharZero K]
    {eps A B : K} {g f : K[X]}
    (heps : eps ≠ 0) (hA : A ≠ 0)
    (hDelta : discriminant eps g f = C A * X + C B) :
    Function.RightInverse (coordinatePairInverse eps A B g)
      (coordinatePairMap eps g f) := by
  rintro ⟨u, v⟩
  let x := (u ^ 2 - 4 * eps * v - B) / A
  let y := (u - g.eval x) / (2 * eps)
  have hxrel : A * x + B = u ^ 2 - 4 * eps * v := by
    dsimp [x]
    field_simp
    ring
  have hdisc : g.eval x ^ 2 - 4 * eps * f.eval x = A * x + B := by
    have h := eval_discriminant_of_eq_affine (x := x) hDelta
    simpa [discriminant] using h
  have hs : 2 * eps * y + g.eval x = u := by
    dsimp [y]
    field_simp
    ring
  let q := eps * y ^ 2 + g.eval x * y + f.eval x
  have hsq : (2 * eps * y + g.eval x) ^ 2 - 4 * eps * q =
      g.eval x ^ 2 - 4 * eps * f.eval x := by
    dsimp [q]
    ring
  have hfour : (4 : K) ≠ 0 := by norm_num
  have hfour_eps : 4 * eps ≠ 0 := mul_ne_zero hfour heps
  have hq : q = v := by
    rw [hs, hdisc, hxrel] at hsq
    apply mul_left_cancel₀ hfour_eps
    linear_combination -hsq
  simp only [coordinatePairInverse]
  change coordinatePairMap eps g f (x, y) = (u, v)
  apply Prod.ext
  · simpa [coordinatePairMap] using hs
  · simpa [coordinatePairMap, q] using hq

/-- The pair `(s,Q)` is a polynomial coordinate system whenever the
discriminant is affine with nonzero slope.-/
theorem coordinatePair_bijective [CharZero K]
    {eps A B : K} {g f : K[X]}
    (heps : eps ≠ 0) (hA : A ≠ 0)
    (hDelta : discriminant eps g f = C A * X + C B) :
    Function.Bijective (coordinatePairMap eps g f) := by
  exact ⟨(coordinatePairInverse_left heps hA hDelta).injective,
    (coordinatePairInverse_right heps hA hDelta).surjective⟩

/-! ### Polynomial source changes -/

/-- Chain rule for the coefficientwise `x`-derivative after substituting the
outer variable.-/
theorem xDerivative_comp (P T : K[X][Y]) :
    xDerivative (P.comp T) =
      (xDerivative P).comp T +
        (yDerivative P).comp T * xDerivative T := by
  induction P using Polynomial.induction_on' with
  | add P R hP hR =>
      simp only [add_comp, map_add, hP, hR]
      ring
  | monomial n a =>
      rw [← C_mul_X_pow_eq_monomial]
      simp [Derivation.leibniz, yDerivative_apply]
      ring

/-- Chain rule for the formal `y`-derivative after polynomial composition.-/
theorem yDerivative_comp (P T : K[X][Y]) :
    yDerivative (P.comp T) =
      (yDerivative P).comp T * yDerivative T := by
  simp [yDerivative_apply, derivative_comp]
  ring

/-- Substitution in `y` multiplies a Jacobian by the derivative of the
substituted polynomial.-/
theorem jacobian_comp (P Q T : K[X][Y]) :
    jacobian (P.comp T) (Q.comp T) =
      (jacobian P Q).comp T * yDerivative T := by
  rw [jacobian, xDerivative_comp P T, xDerivative_comp Q T,
    yDerivative_comp P T, yDerivative_comp Q T]
  rw [jacobian]
  simp only [sub_comp, mul_comp]
  ring

/-- The translation amount used to complete the square.-/
def halfLinear (eps : K) (g : K[X]) : K[X] :=
  C ((2 * eps)⁻¹) * g

/-- Substitute `y - g/(2*eps)` for the original `y`.-/
def centerSubstitution (eps : K) (g : K[X]) : K[X][Y] :=
  Y - C (halfLinear eps g)

/-- The constant term after completing the square.-/
def centeredResidual (eps : K) (g f : K[X]) : K[X] :=
  f - C ((4 * eps)⁻¹) * g ^ 2

theorem yDerivative_centerSubstitution (eps : K) (g : K[X]) :
    yDerivative (centerSubstitution eps g) = 1 := by
  simp [centerSubstitution]

theorem jacobian_comp_centerSubstitution (P Q : K[X][Y]) (eps : K) (g : K[X]) :
    jacobian (P.comp (centerSubstitution eps g))
        (Q.comp (centerSubstitution eps g)) =
      (jacobian P Q).comp (centerSubstitution eps g) := by
  rw [jacobian_comp, yDerivative_centerSubstitution, mul_one]

theorem quadraticCoordinate_comp_centerSubstitution [CharZero K]
    {eps : K} (g f : K[X]) (heps : eps ≠ 0) :
    (quadraticCoordinate eps g f).comp (centerSubstitution eps g) =
      CC eps * Y ^ 2 + C (centeredResidual eps g f) := by
  have hcrossScalar :
      2 * eps * (eps⁻¹ * (2 : K)⁻¹) = 1 := by
    field_simp
  have hconstantScalar :
      eps * (eps⁻¹ * (2 : K)⁻¹) ^ 2 -
          eps⁻¹ * (2 : K)⁻¹ + eps⁻¹ * (4 : K)⁻¹ = 0 := by
    field_simp
    ring
  have hcross := congrArg (fun z : K => (CC z : K[X][Y])) hcrossScalar
  have hconstant :=
    congrArg (fun z : K => (CC z : K[X][Y])) hconstantScalar
  simp only [CC_mul_scalar, CC_add_scalar, CC_sub_scalar, CC_pow_scalar,
    CC_ofNat_scalar, CC_zero_scalar, CC_one_scalar] at hcross hconstant
  simp [quadraticCoordinate, centerSubstitution, halfLinear, centeredResidual]
  linear_combination -(Y * C g) * hcross + (C g) ^ 2 * hconstant

theorem centeredResidual_eq_affine [CharZero K]
    {eps A B : K} {g f : K[X]}
    (heps : eps ≠ 0)
    (hDelta : discriminant eps g f = C A * X + C B) :
    centeredResidual eps g f =
      C (-((4 * eps)⁻¹ * A)) * X + C (-((4 * eps)⁻¹ * B)) := by
  have hfour : (4 : K) ≠ 0 := by norm_num
  have hfoureps : 4 * eps ≠ 0 := mul_ne_zero hfour heps
  have hunit : C ((4 * eps)⁻¹) * C (4 * eps) = (1 : K[X]) := by
    calc
      C ((4 * eps)⁻¹) * C (4 * eps) =
          C ((4 * eps)⁻¹ * (4 * eps)) := C_mul.symm
      _ = C 1 := by rw [inv_mul_cancel₀ hfoureps]
      _ = 1 := C_1
  rw [show centeredResidual eps g f =
      -(C ((4 * eps)⁻¹) * discriminant eps g f) by
    calc
      centeredResidual eps g f =
          f - C ((4 * eps)⁻¹) * g ^ 2 := rfl
      _ = 1 * f - C ((4 * eps)⁻¹) * g ^ 2 := by rw [one_mul]
      _ = (C ((4 * eps)⁻¹) * C (4 * eps)) * f -
          C ((4 * eps)⁻¹) * g ^ 2 := by rw [hunit]
      _ = -(C ((4 * eps)⁻¹) * discriminant eps g f) := by
        simp only [discriminant]
        ring]
  rw [hDelta]
  simp only [mul_add, neg_add_rev, C_mul, C_neg]
  ring

/-! ### Swapping the two source variables -/

theorem xDerivative_swap (P : K[X][Y]) :
    xDerivative (Bivariate.swap P) = Bivariate.swap (yDerivative P) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | monomial n p =>
      induction p using Polynomial.induction_on' with
      | add p q hp hq =>
          simpa only [map_add] using congrArg₂ (fun U V => U + V) hp hq
      | monomial m a =>
          simp_rw [← C_mul_X_pow_eq_monomial]
          simp [Bivariate.swap_C_C, Bivariate.swap_X, Bivariate.swap_Y,
            Derivation.leibniz, yDerivative_apply]

theorem yDerivative_swap (P : K[X][Y]) :
    yDerivative (Bivariate.swap P) = Bivariate.swap (xDerivative P) := by
  have h := xDerivative_swap (Bivariate.swap P)
  rw [Bivariate.swap_swap_apply] at h
  have hs := congrArg Bivariate.swap h
  rw [Bivariate.swap_swap_apply] at hs
  exact hs.symm

theorem jacobian_swap (P Q : K[X][Y]) :
    jacobian (Bivariate.swap P) (Bivariate.swap Q) =
      -(Bivariate.swap (jacobian P Q)) := by
  rw [jacobian, xDerivative_swap, yDerivative_swap,
    xDerivative_swap, yDerivative_swap, jacobian]
  simp only [map_sub, map_mul]
  ring

/-- After completing the square and exchanging the source variables, the
quadratic coordinate becomes affine in the new `y` variable.-/
theorem swap_quadraticCoordinate_comp_centerSubstitution [CharZero K]
    {eps A B : K} {g f : K[X]}
    (heps : eps ≠ 0)
    (hDelta : discriminant eps g f = C A * X + C B) :
    Bivariate.swap
        ((quadraticCoordinate eps g f).comp (centerSubstitution eps g)) =
      affineCoordinate (C (-((4 * eps)⁻¹ * A)))
        (C eps * X ^ 2 + C (-((4 * eps)⁻¹ * B))) := by
  rw [quadraticCoordinate_comp_centerSubstitution g f heps]
  rw [map_add, map_mul, map_pow, Bivariate.swap_C_C, Bivariate.swap_Y,
    Bivariate.swap_C, centeredResidual_eq_affine heps hDelta]
  simp [affineCoordinate]
  ring

/-- The centered-and-swapped map has the negated constant Jacobian.-/
theorem jacobian_swap_comp_centerSubstitution
    {P Q : K[X][Y]} {eps k : K} (g : K[X])
    (hjac : jacobian P Q = CC k) :
    jacobian (Bivariate.swap (P.comp (centerSubstitution eps g)))
        (Bivariate.swap (Q.comp (centerSubstitution eps g))) = CC (-k) := by
  rw [jacobian_swap, jacobian_comp_centerSubstitution, hjac]
  rw [C_comp, Bivariate.swap_C_C]
  change -C (C k) = C (C (-k))
  rw [C_neg, C_neg]

/-! ### Evaluation and transport back to the original coordinates -/

theorem evalEval_swap (P : K[X][Y]) (x y : K) :
    (Bivariate.swap P).evalEval x y = P.evalEval y x := by
  have hxy := coe_aevalAeval_eq_evalEval (A := K) x y
  have hyx := coe_aevalAeval_eq_evalEval (A := K) y x
  rw [← hxy, ← hyx]
  exact Bivariate.aevalAeval_swap x y P

theorem evalEval_comp (P T : K[X][Y]) (x y : K) :
    (P.comp T).evalEval x y = P.evalEval x (T.evalEval x y) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [add_comp, evalEval_add, hP, hQ]
  | monomial n p =>
      rw [← C_mul_X_pow_eq_monomial]
      simp [evalEval]

/-- Swapping commutes with substituting into a polynomial whose coefficients
are scalars.-/
theorem swap_map_comp (G : K[X]) (R : K[X][Y]) :
    Bivariate.swap ((G.map C).comp R) =
      (G.map C).comp (Bivariate.swap R) := by
  induction G using Polynomial.induction_on' with
  | add G H hG hH => simp only [Polynomial.map_add, add_comp, map_add, hG, hH]
  | monomial n a =>
      simp_rw [← C_mul_X_pow_eq_monomial]
      simp [Bivariate.swap_C_C]

@[simp]
theorem evalEval_centerSubstitution (eps x y : K) (g : K[X]) :
    (centerSubstitution eps g).evalEval x y =
      y - (halfLinear eps g).eval x := by
  simp [centerSubstitution, evalEval_C]

/-- The source change used by completing the square and then swapping the two
variables.-/
def centerSwapSource (eps : K) (g : K[X]) (p : K × K) : K × K :=
  (p.2, p.1 - (halfLinear eps g).eval p.2)

/-- The explicit inverse source change.-/
def centerSwapSourceInverse (eps : K) (g : K[X]) (p : K × K) : K × K :=
  (p.2 + (halfLinear eps g).eval p.1, p.1)

theorem centerSwapSourceInverse_left (eps : K) (g : K[X]) :
    Function.LeftInverse (centerSwapSourceInverse eps g)
      (centerSwapSource eps g) := by
  rintro ⟨x, y⟩
  simp [centerSwapSource, centerSwapSourceInverse]

theorem centerSwapSourceInverse_right (eps : K) (g : K[X]) :
    Function.RightInverse (centerSwapSourceInverse eps g)
      (centerSwapSource eps g) := by
  rintro ⟨x, y⟩
  simp [centerSwapSource, centerSwapSourceInverse]

theorem centerSwapSource_bijective (eps : K) (g : K[X]) :
    Function.Bijective (centerSwapSource eps g) :=
  ⟨(centerSwapSourceInverse_left eps g).injective,
    (centerSwapSourceInverse_right eps g).surjective⟩

/-- The inverse polynomial translation to `centerSubstitution`.-/
def uncenterSubstitution (eps : K) (g : K[X]) : K[X][Y] :=
  Y + C (halfLinear eps g)

theorem centerSubstitution_comp_uncenterSubstitution (eps : K) (g : K[X]) :
    (centerSubstitution eps g).comp (uncenterSubstitution eps g) = Y := by
  simp [centerSubstitution, uncenterSubstitution]

theorem uncenterSubstitution_comp_centerSubstitution (eps : K) (g : K[X]) :
    (uncenterSubstitution eps g).comp (centerSubstitution eps g) = Y := by
  simp [centerSubstitution, uncenterSubstitution]

/-- Evaluation of the original polynomial map.-/
def quadraticCoordinateMap (P : K[X][Y]) (eps : K) (g f : K[X])
    (p : K × K) : K × K :=
  (P.evalEval p.1 p.2, (quadraticCoordinate eps g f).evalEval p.1 p.2)

/-- The target shear appearing in the original-coordinate normal form.-/
def normalFormTargetMap (G : K[X]) (lambda : K) (p : K × K) : K × K :=
  (G.eval p.2 + lambda * p.1, p.2)

/-- Explicit inverse of `normalFormTargetMap`.-/
def normalFormTargetInverse (G : K[X]) (lambda : K)
    (p : K × K) : K × K :=
  ((p.1 - G.eval p.2) / lambda, p.2)

theorem normalFormTargetInverse_left {G : K[X]} {lambda : K}
    (hlambda : lambda ≠ 0) :
    Function.LeftInverse (normalFormTargetInverse G lambda)
      (normalFormTargetMap G lambda) := by
  rintro ⟨s, q⟩
  simp [normalFormTargetInverse, normalFormTargetMap]
  field_simp

theorem normalFormTargetInverse_right {G : K[X]} {lambda : K}
    (hlambda : lambda ≠ 0) :
    Function.RightInverse (normalFormTargetInverse G lambda)
      (normalFormTargetMap G lambda) := by
  rintro ⟨u, v⟩
  simp [normalFormTargetInverse, normalFormTargetMap]
  field_simp
  ring

theorem quadraticCoordinateMap_eq_normalFormTargetMap
    {P : K[X][Y]} {eps lambda : K} {g f G : K[X]}
    (hP : P = (G.map C).comp (quadraticCoordinate eps g f) +
      CC lambda * criticalLinear eps g) :
    quadraticCoordinateMap P eps g f =
      normalFormTargetMap G lambda ∘ coordinatePairMap eps g f := by
  funext p
  rcases p with ⟨x, y⟩
  apply Prod.ext
  · simp [quadraticCoordinateMap, normalFormTargetMap, coordinatePairMap,
      hP, evalEval_comp, evalEval_map_C]
  · rfl

/-- The inverse displayed by the original-coordinate normal form.-/
def constantLeadingQuadraticInverse (eps A B lambda : K) (g G : K[X])
    (p : K × K) : K × K :=
  coordinatePairInverse eps A B g (normalFormTargetInverse G lambda p)

theorem constantLeadingQuadraticInverse_left [CharZero K]
    {P : K[X][Y]} {eps A B lambda : K} {g f G : K[X]}
    (heps : eps ≠ 0) (hA : A ≠ 0) (hlambda : lambda ≠ 0)
    (hDelta : discriminant eps g f = C A * X + C B)
    (hP : P = (G.map C).comp (quadraticCoordinate eps g f) +
      CC lambda * criticalLinear eps g) :
    Function.LeftInverse (constantLeadingQuadraticInverse eps A B lambda g G)
      (quadraticCoordinateMap P eps g f) := by
  intro p
  have hmap := quadraticCoordinateMap_eq_normalFormTargetMap hP
  change coordinatePairInverse eps A B g
      (normalFormTargetInverse G lambda (quadraticCoordinateMap P eps g f p)) = p
  rw [congrFun hmap p]
  simp only [Function.comp_apply]
  rw [normalFormTargetInverse_left hlambda]
  exact coordinatePairInverse_left heps hA hDelta p

theorem constantLeadingQuadraticInverse_right [CharZero K]
    {P : K[X][Y]} {eps A B lambda : K} {g f G : K[X]}
    (heps : eps ≠ 0) (hA : A ≠ 0) (hlambda : lambda ≠ 0)
    (hDelta : discriminant eps g f = C A * X + C B)
    (hP : P = (G.map C).comp (quadraticCoordinate eps g f) +
      CC lambda * criticalLinear eps g) :
    Function.RightInverse (constantLeadingQuadraticInverse eps A B lambda g G)
      (quadraticCoordinateMap P eps g f) := by
  intro p
  have hmap := quadraticCoordinateMap_eq_normalFormTargetMap hP
  rw [congrFun hmap
    (constantLeadingQuadraticInverse eps A B lambda g G p)]
  change normalFormTargetMap G lambda
      (coordinatePairMap eps g f
        (coordinatePairInverse eps A B g
          (normalFormTargetInverse G lambda p))) = p
  rw [coordinatePairInverse_right heps hA hDelta]
  exact normalFormTargetInverse_right hlambda p

theorem transformedMap_eq [CharZero K]
    {P : K[X][Y]} {eps A B : K} {g f : K[X]}
    (heps : eps ≠ 0)
    (hDelta : discriminant eps g f = C A * X + C B) :
    affineCoordinateMap
        (Bivariate.swap (P.comp (centerSubstitution eps g)))
        (C (-((4 * eps)⁻¹ * A)))
        (C eps * X ^ 2 + C (-((4 * eps)⁻¹ * B))) =
      quadraticCoordinateMap P eps g f ∘ centerSwapSource eps g := by
  funext p
  rcases p with ⟨u, v⟩
  have hQ :=
    swap_quadraticCoordinate_comp_centerSubstitution heps hDelta
  apply Prod.ext
  · simp [affineCoordinateMap, quadraticCoordinateMap, centerSwapSource,
      evalEval_swap, evalEval_comp]
  · change
      (affineCoordinate (C (-((4 * eps)⁻¹ * A)))
          (C eps * X ^ 2 + C (-((4 * eps)⁻¹ * B)))).evalEval u v =
        (quadraticCoordinate eps g f).evalEval v
          (u - (halfLinear eps g).eval v)
    rw [← hQ, evalEval_swap, evalEval_comp,
      evalEval_centerSubstitution]

/-- A plane Keller map is bijective when one coordinate is quadratic in `y`
with nonzero constant leading coefficient.  There is no degree restriction on
the other coordinate.-/
theorem quadraticCoordinate_bijective [CharZero K]
    {P : K[X][Y]} {eps k : K} {g f : K[X]}
    (heps : eps ≠ 0) (hk : k ≠ 0)
    (hjac : jacobian P (quadraticCoordinate eps g f) = CC k) :
    Function.Bijective (quadraticCoordinateMap P eps g f) := by
  obtain ⟨rho, A, B, _hrho, hA, _hrhoA, _hpy, hDelta⟩ :=
    affine_discriminant heps hk hjac
  have hfour : (4 : K) ≠ 0 := by norm_num
  have hslopeScalar : -((4 * eps)⁻¹ * A) ≠ 0 := by
    exact neg_ne_zero.mpr
      (mul_ne_zero (inv_ne_zero (mul_ne_zero hfour heps)) hA)
  have hslope : C (-((4 * eps)⁻¹ * A)) ≠ (0 : K[X]) :=
    C_ne_zero.mpr hslopeScalar
  have hQ :=
    swap_quadraticCoordinate_comp_centerSubstitution heps hDelta
  have hJ :
      jacobian (Bivariate.swap (P.comp (centerSubstitution eps g)))
          (affineCoordinate (C (-((4 * eps)⁻¹ * A)))
            (C eps * X ^ 2 + C (-((4 * eps)⁻¹ * B)))) = CC (-k) := by
    rw [← hQ]
    exact jacobian_swap_comp_centerSubstitution g hjac
  have htransformed : Function.Bijective
      (affineCoordinateMap
        (Bivariate.swap (P.comp (centerSubstitution eps g)))
        (C (-((4 * eps)⁻¹ * A)))
        (C eps * X ^ 2 + C (-((4 * eps)⁻¹ * B)))) :=
    nonzeroSlope_bijective (neg_ne_zero.mpr hk) hslope hJ
  have hmap := transformedMap_eq (P := P) heps hDelta
  have hcomposite : Function.Bijective
      (quadraticCoordinateMap P eps g f ∘ centerSwapSource eps g) := by
    rw [← hmap]
    exact htransformed
  have hsource := centerSwapSource_bijective eps g
  constructor
  · intro a b hab
    obtain ⟨u, rfl⟩ := hsource.2 a
    obtain ⟨v, rfl⟩ := hsource.2 b
    exact congrArg (centerSwapSource eps g) (hcomposite.1 hab)
  · intro z
    obtain ⟨u, hu⟩ := hcomposite.2 z
    exact ⟨centerSwapSource eps g u, hu⟩

/-- Structural normal form in the centered-and-swapped chart used in the
bijectivity proof.-/
theorem constantLeadingQuadratic_normal_form [CharZero K]
    {P : K[X][Y]} {eps k : K} {g f : K[X]}
    (heps : eps ≠ 0) (hk : k ≠ 0)
    (hjac : jacobian P (quadraticCoordinate eps g f) = CC k) :
    ∃ A B : K, ∃ G : K[X], ∃ alpha beta : K,
      A ≠ 0 ∧
      discriminant eps g f = C A * X + C B ∧
      alpha ≠ 0 ∧
      alpha * (-((4 * eps)⁻¹ * A)) = -k ∧
      Bivariate.swap (P.comp (centerSubstitution eps g)) =
        (G.map C).comp
            (Bivariate.swap
              ((quadraticCoordinate eps g f).comp
                (centerSubstitution eps g))) +
          C (C alpha * X + C beta) := by
  obtain ⟨rho, A, B, _hrho, hA, _hrhoA, _hpy, hDelta⟩ :=
    affine_discriminant heps hk hjac
  have hfour : (4 : K) ≠ 0 := by norm_num
  have hslopeScalar : -((4 * eps)⁻¹ * A) ≠ 0 := by
    exact neg_ne_zero.mpr
      (mul_ne_zero (inv_ne_zero (mul_ne_zero hfour heps)) hA)
  have hslope : C (-((4 * eps)⁻¹ * A)) ≠ (0 : K[X]) :=
    C_ne_zero.mpr hslopeScalar
  have hQ :=
    swap_quadraticCoordinate_comp_centerSubstitution heps hDelta
  have hJ :
      jacobian (Bivariate.swap (P.comp (centerSubstitution eps g)))
          (affineCoordinate (C (-((4 * eps)⁻¹ * A)))
            (C eps * X ^ 2 + C (-((4 * eps)⁻¹ * B)))) = CC (-k) := by
    rw [← hQ]
    exact jacobian_swap_comp_centerSubstitution g hjac
  obtain ⟨G, alpha, beta, delta, _hdelta, halpha, halphadelta,
      hslopeDelta, hP⟩ :=
    nonzeroSlope_normal_form (neg_ne_zero.mpr hk) hslope hJ
  have hdelta : -((4 * eps)⁻¹ * A) = delta :=
    C_injective hslopeDelta
  refine ⟨A, B, G, alpha, beta, hA, hDelta, halpha, ?_, ?_⟩
  · rw [hdelta]
    exact halphadelta
  · rw [hQ]
    exact hP

/-- Original-coordinate normal form.  The additive constant from the affine
chart has been absorbed into `G`.-/
theorem constantLeadingQuadratic_original_normal_form [CharZero K]
    {P : K[X][Y]} {eps k : K} {g f : K[X]}
    (heps : eps ≠ 0) (hk : k ≠ 0)
    (hjac : jacobian P (quadraticCoordinate eps g f) = CC k) :
    ∃ A B lambda : K, ∃ G : K[X],
      A ≠ 0 ∧ lambda ≠ 0 ∧
      discriminant eps g f = C A * X + C B ∧
      lambda * A / 2 = k ∧
      P = (G.map C).comp (quadraticCoordinate eps g f) +
        CC lambda * criticalLinear eps g := by
  obtain ⟨A, B, G, alpha, beta, hA, hDelta, halpha, halphaSlope,
      hcenteredSwap⟩ :=
    constantLeadingQuadratic_normal_form heps hk hjac
  have hlinearSwap :
      Bivariate.swap (C (C alpha * X + C beta)) =
        CC alpha * Y + CC beta := by
    rw [Bivariate.swap_C]
    simp
  have hcentered :
      P.comp (centerSubstitution eps g) =
        (G.map C).comp
            ((quadraticCoordinate eps g f).comp
              (centerSubstitution eps g)) +
          (CC alpha * Y + CC beta) := by
    have h := congrArg Bivariate.swap hcenteredSwap
    rw [Bivariate.swap_swap_apply, map_add, swap_map_comp,
      Bivariate.swap_swap_apply, hlinearSwap] at h
    exact h
  have horiginal :
      P = (G.map C).comp (quadraticCoordinate eps g f) +
          (CC alpha * uncenterSubstitution eps g + CC beta) := by
    have h := congrArg
      (fun R : K[X][Y] => R.comp (uncenterSubstitution eps g)) hcentered
    simpa only [add_comp, mul_comp, X_comp, C_comp, comp_assoc,
      centerSubstitution_comp_uncenterSubstitution, comp_X] using h
  let lambda := alpha * (2 * eps)⁻¹
  let G' := G + C beta
  have htwo : (2 : K) ≠ 0 := by norm_num
  have htwoeps : 2 * eps ≠ 0 := mul_ne_zero htwo heps
  have hlambda : lambda ≠ 0 :=
    mul_ne_zero halpha (inv_ne_zero htwoeps)
  have hlambdaCoeff : lambda * (2 * eps) = alpha := by
    dsimp [lambda]
    field_simp
  have hlambdaCoeffCC :=
    congrArg (fun z : K => (CC z : K[X][Y])) hlambdaCoeff
  simp only [CC_mul_scalar] at hlambdaCoeffCC
  have hlambdaDef : CC lambda = CC alpha * CC ((2 * eps)⁻¹) := by
    dsimp [lambda]
    rw [CC_mul_scalar]
  have hlambdaLinear :
      CC alpha * uncenterSubstitution eps g =
        CC lambda * criticalLinear eps g := by
    simp only [uncenterSubstitution, halfLinear, criticalLinear, mul_add,
      C_mul]
    simp only [CC_mul_scalar]
    linear_combination -Y * hlambdaCoeffCC - C g * hlambdaDef
  have hlambdaA : lambda * A / 2 = k := by
    dsimp [lambda]
    field_simp at halphaSlope ⊢
    linear_combination -halphaSlope
  refine ⟨A, B, lambda, G', hA, hlambda, hDelta, hlambdaA, ?_⟩
  calc
    P = (G.map C).comp (quadraticCoordinate eps g f) +
        (CC alpha * uncenterSubstitution eps g + CC beta) := horiginal
    _ = ((G + C beta).map C).comp (quadraticCoordinate eps g f) +
        CC alpha * uncenterSubstitution eps g := by
      simp [Polynomial.map_add, add_comp]
      ring
    _ = (G'.map C).comp (quadraticCoordinate eps g f) +
        CC lambda * criticalLinear eps g := by
      rw [hlambdaLinear]

/-- Alias emphasizing the geometric hypothesis rather than the chosen
polynomial notation.-/
theorem constantLeadingQuadratic_bijective [CharZero K]
    {P : K[X][Y]} {eps k : K} {g f : K[X]}
    (heps : eps ≠ 0) (hk : k ≠ 0)
    (hjac : jacobian P (quadraticCoordinate eps g f) = CC k) :
    Function.Bijective (quadraticCoordinateMap P eps g f) :=
  quadraticCoordinate_bijective heps hk hjac

theorem constantLeadingQuadratic_injective [CharZero K]
    {P : K[X][Y]} {eps k : K} {g f : K[X]}
    (heps : eps ≠ 0) (hk : k ≠ 0)
    (hjac : jacobian P (quadraticCoordinate eps g f) = CC k) :
    Function.Injective (quadraticCoordinateMap P eps g f) :=
  (constantLeadingQuadratic_bijective heps hk hjac).1

end JacobianTwo.ConstantLeadingQuadratic
