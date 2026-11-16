/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
import Tengoku.JacobianTwo.JacobianTwo.Basic
import Tengoku.Seed.Algebra.MvPolynomial.CommRing
import Tengoku.Seed.Data.Complex.Basic
import Tengoku.Seed.Tactic.FinCases
import Tengoku.Seed.Tactic.NormNum
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The announced three-dimensional counterexample

This file transcribes the polynomial map announced by Levent Alpöge on
2026-07-20 UTC (2026-07-19 Pacific) and proves the two finite certificates that
matter: its formal Jacobian determinant is the nonzero constant `-2`, and three
distinct points of `ℂ³` have the same image.

The coordinate polynomials are defined over `ℤ`, exactly as announced. They are
then evaluated in an arbitrary commutative ring through `Int.castRingHom`.

## Main results

- `formalJacobian_det`: the determinant of the formal Jacobian is the constant
  polynomial `-2`.
- `jacobianAt_det`: after evaluation in any commutative ring, the determinant is
  still `-2` at every point.
- `three_distinct_preimages`: the full exact fiber certificate from the
  screenshot.
- `complex_not_injective`: the induced polynomial map on `ℂ³` is not injective.
-/

noncomputable section

namespace JacobianTwo.Counterexample

abbrev Coord := Fin 3
abbrev Poly := MvPolynomial Coord ℤ

open MvPolynomial

private def x : Poly := X 0
private def y : Poly := X 1
private def z : Poly := X 2
private def c (n : ℕ) : Poly := C (n : ℤ)

/-- The three integer-coefficient coordinate polynomials displayed in the
announcement.-/
def announcedMap : PolynomialMap 3 ℤ := ![
  (1 + x * y) ^ 3 * z + y ^ 2 * (1 + x * y) * (c 4 + c 3 * x * y),
  y + c 3 * x * (1 + x * y) ^ 2 * z + c 3 * x * y ^ 2 * (c 4 + c 3 * x * y),
  c 2 * x - c 3 * x ^ 2 * y - x ^ 3 * z
]

/-- The formal Jacobian matrix of the announced map.-/
def jacobian : Matrix Coord Coord Poly := formalJacobian announcedMap

set_option maxRecDepth 100000 in
/-- The determinant of the formal Jacobian is identically `-2`.-/
theorem formalJacobian_det : jacobian.det = C (-2 : ℤ) := by
  rw [Matrix.det_fin_three]
  simp only [jacobian, formalJacobian, announcedMap,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  simp only [x, y, z, c, map_add, map_sub, Derivation.leibniz,
    Derivation.leibniz_pow, pderiv_C, pderiv_one, pderiv_X, Pi.single_apply]
  simp
  ring

/-- Evaluation of the integer-coefficient map in a commutative ring.-/
def polynomialMap {R : Type*} [CommRing R] (p : Coord → R) : Coord → R :=
  fun i ↦ eval₂ (Int.castRingHom R) p (announcedMap i)

/-- The pointwise formal Jacobian after evaluating its integer coefficients and
variables in a commutative ring.-/
def jacobianAt {R : Type*} [CommRing R] (p : Coord → R) : Matrix Coord Coord R :=
  (eval₂Hom (Int.castRingHom R) p).mapMatrix jacobian

/-- The determinant remains `-2` at every point after base change. In
particular, this applies to every point of `ℂ³`.-/
theorem jacobianAt_det {R : Type*} [CommRing R] (p : Coord → R) :
    (jacobianAt p).det = (-2 : R) := by
  rw [jacobianAt, ← RingHom.map_det, formalJacobian_det]
  simp

/-- The displayed map on `ℂ³`.-/
abbrev complexMap : (Coord → ℂ) → (Coord → ℂ) := polynomialMap

/-- The point on the flat sheet in the displayed fiber.-/
def p₀ : Coord → ℂ := ![0, 0, -(1 / 4)]

/-- The first point on the curved sheet in the displayed fiber.-/
def p₁ : Coord → ℂ := ![1, -(3 / 2), 13 / 2]

/-- The second point on the curved sheet in the displayed fiber.-/
def p₂ : Coord → ℂ := ![-1, 3 / 2, 13 / 2]

/-- The common target shown in the screenshot.-/
def target : Coord → ℂ := ![-(1 / 4), 0, 0]

/-- Pointwise expansion of the integer-coefficient definition into the formula
displayed in the screenshot.-/
theorem complexMap_formula (p : Coord → ℂ) : complexMap p = ![
    (1 + p 0 * p 1) ^ 3 * p 2 + p 1 ^ 2 * (1 + p 0 * p 1) * (4 + 3 * p 0 * p 1),
    p 1 + 3 * p 0 * (1 + p 0 * p 1) ^ 2 * p 2 +
      3 * p 0 * p 1 ^ 2 * (4 + 3 * p 0 * p 1),
    2 * p 0 - 3 * p 0 ^ 2 * p 1 - p 0 ^ 3 * p 2
  ] := by
  funext i
  fin_cases i <;>
    simp [complexMap, polynomialMap, announcedMap, x, y, z, c]

theorem map_p₀ : complexMap p₀ = target := by
  rw [complexMap_formula]
  funext i
  fin_cases i <;>
    simp [p₀, target, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

theorem map_p₁ : complexMap p₁ = target := by
  rw [complexMap_formula]
  funext i
  fin_cases i <;>
    simp [p₁, target, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      norm_num

theorem map_p₂ : complexMap p₂ = target := by
  rw [complexMap_formula]
  funext i
  fin_cases i <;>
    simp [p₂, target, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      norm_num

/-- The complete exact collision certificate from the screenshot.-/
theorem three_distinct_preimages :
    p₀ ≠ p₁ ∧ p₀ ≠ p₂ ∧ p₁ ≠ p₂ ∧
      complexMap p₀ = target ∧ complexMap p₁ = target ∧ complexMap p₂ = target := by
  refine ⟨?_, ?_, ?_, map_p₀, map_p₁, map_p₂⟩
  all_goals
    intro h
    have h₀ := congrFun h 0
    norm_num [p₀, p₁, p₂] at h₀

/-- The announced polynomial map on `ℂ³` is not injective.-/
theorem complex_not_injective : ¬Function.Injective complexMap := by
  intro h
  exact three_distinct_preimages.1 (h (map_p₀.trans map_p₁.symm))

end JacobianTwo.Counterexample
