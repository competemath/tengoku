/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
import Tengoku.Seed.RingTheory.Derivation.MapCoeffs
import Tengoku.Seed.Tactic.LinearCombination

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Coefficient recurrence for a centered quadratic coordinate

This file isolates the coefficient calculation used after passing to the
fraction field in the variable-leading quadratic case.  Let `D` be a
derivation of a characteristic-zero field `L`, and regard `B` as a polynomial
in an outer indeterminate `Q`.  From

`2 * (Q - F) * D(B) - D(F) * B = C`

we extract the leading-coefficient equation, the full downward recurrence,
and the terminal constant-coefficient equation.  Here `D(B)` means that `D`
is applied coefficientwise; the outer indeterminate is held constant.
-/

noncomputable section

open Polynomial

namespace JacobianTwo.QuadraticRecurrence

variable {R L : Type*} [CommRing R] [Field L] [Algebra R L]

/-- Apply a derivation to the coefficients of a polynomial while holding its
indeterminate constant.-/
def coefficientwiseDerivative (D : Derivation R L L) : Derivation R L[X] L[X] :=
  PolynomialModule.equivPolynomialSelf.compDer D.mapCoeffs

@[simp]
theorem coeff_coefficientwiseDerivative (D : Derivation R L L) (B : L[X]) (j : ℕ) :
    (coefficientwiseDerivative D B).coeff j = D (B.coeff j) :=
  rfl

/-- The polynomial whose coefficient equations encode the quadratic
recurrence.  Its indeterminate represents the outer variable `Q`.-/
def recurrencePolynomial (D : Derivation R L L) (F : L) (B : L[X]) : L[X] :=
  C 2 * ((X - C F) * coefficientwiseDerivative D B) - C (D F) * B

theorem coeff_succ_recurrencePolynomial (D : Derivation R L L) (F : L)
    (B : L[X]) (j : ℕ) :
    (recurrencePolynomial D F B).coeff (j + 1) =
      2 * (D (B.coeff j) - F * D (B.coeff (j + 1))) -
        D F * B.coeff (j + 1) := by
  simp [recurrencePolynomial, sub_mul]

theorem coeff_zero_recurrencePolynomial (D : Derivation R L L) (F : L)
    (B : L[X]) :
    (recurrencePolynomial D F B).coeff 0 =
      -2 * F * D (B.coeff 0) - D F * B.coeff 0 := by
  simp [recurrencePolynomial]
  ring

/-- The coefficient of highest degree in `B` is constant for `D`.

This statement remains meaningful when `B = 0`: then `natDegree B = 0` and
the asserted coefficient is zero.-/
theorem top_coefficient_derivative_eq_zero [CharZero L]
    (D : Derivation R L L) (F C₀ : L)
    (B : L[X]) (h : recurrencePolynomial D F B = C C₀) :
    D (B.coeff B.natDegree) = 0 := by
  have htop := congrArg (fun p : L[X] ↦ p.coeff (B.natDegree + 1)) h
  rw [coeff_succ_recurrencePolynomial] at htop
  simp only [coeff_natDegree_succ_eq_zero, map_zero, mul_zero, sub_zero,
    coeff_C, ite_eq_right (Nat.ne_of_gt (Nat.zero_lt_succ B.natDegree))] at htop
  exact (mul_eq_zero.mp htop).resolve_left two_ne_zero

/-- Every positive-degree coefficient equation yields the downward recurrence

`D(b_j) = F * D(b_(j+1)) + (D(F) / 2) * b_(j+1)`.

Writing the positive index as `j + 1` makes the formula total: coefficients
above the degree of `B` are automatically zero.-/
theorem coefficient_recurrence [CharZero L]
    (D : Derivation R L L) (F C₀ : L) (B : L[X])
    (h : recurrencePolynomial D F B = C C₀) (j : ℕ) :
    D (B.coeff j) =
      F * D (B.coeff (j + 1)) + (D F / 2) * B.coeff (j + 1) := by
  have hj := congrArg (fun p : L[X] ↦ p.coeff (j + 1)) h
  rw [coeff_succ_recurrencePolynomial] at hj
  simp only [coeff_C, ite_eq_right (Nat.ne_of_gt (Nat.zero_lt_succ j))] at hj
  linear_combination (1 / 2 : L) * hj

/-- The same recurrence with the indexing convention `b_(j-1)` used in the
quadratic-reduction argument.-/
theorem coefficient_recurrence_of_pos [CharZero L]
    (D : Derivation R L L) (F C₀ : L) (B : L[X])
    (h : recurrencePolynomial D F B = C C₀) (j : ℕ) (hj : 0 < j) :
    D (B.coeff (j - 1)) = F * D (B.coeff j) + (D F / 2) * B.coeff j := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
  simpa using coefficient_recurrence D F C₀ B h i

/-- The constant coefficient is the only coefficient that sees the constant
right-hand side.-/
theorem constant_coefficient_equation (D : Derivation R L L) (F C₀ : L)
    (B : L[X]) (h : recurrencePolynomial D F B = C C₀) :
    -2 * F * D (B.coeff 0) - D F * B.coeff 0 = C₀ := by
  have hzero := congrArg (fun p : L[X] ↦ p.coeff 0) h
  rw [coeff_zero_recurrencePolynomial] at hzero
  simpa using hzero

/-- The complete coefficient package extracted from the centered quadratic
identity.-/
theorem recurrence_package [CharZero L]
    (D : Derivation R L L) (F C₀ : L) (B : L[X])
    (h : recurrencePolynomial D F B = C C₀) :
    D (B.coeff B.natDegree) = 0 ∧
      (∀ j : ℕ, D (B.coeff j) =
        F * D (B.coeff (j + 1)) + (D F / 2) * B.coeff (j + 1)) ∧
      -2 * F * D (B.coeff 0) - D F * B.coeff 0 = C₀ :=
  ⟨top_coefficient_derivative_eq_zero D F C₀ B h,
    fun j ↦ coefficient_recurrence D F C₀ B h j,
    constant_coefficient_equation D F C₀ B h⟩

end JacobianTwo.QuadraticRecurrence
