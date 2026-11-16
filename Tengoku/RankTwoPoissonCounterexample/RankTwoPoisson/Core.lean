import Tengoku.RankTwoPoissonCounterexample.RankTwoPoisson.Definitions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Three-variable core and coefficient certificates

This file formalizes the determinant-one three-variable core and the three
coefficient identities used in the manuscript's two-form proof.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace RankTwoPoisson
namespace Core

noncomputable section

open MvPolynomial

abbrev CoreVar := Fin 3
abbrev CoreP := MvPolynomial CoreVar ℚ

def crat (r : ℚ) : CoreP := C r

def Xc : CoreP := X 0
def Yc : CoreP := X 1
def Wc : CoreP := X 2

def U : CoreP := Xc * Yc

/-- The normalized three-variable core coordinate `R`.-/
def r : CoreP :=
  crat 2 * Xc - crat 3 * Xc ^ 2 * Yc - Xc ^ 3 * Wc

/-- The normalized three-variable core coordinate `S`.-/
def s : CoreP :=
  Yc
    + crat 3 * Xc * (crat 1 + U) ^ 2 * Wc
    + crat 3 * Xc * Yc ^ 2 * (crat 4 + crat 3 * U)

/-- The normalized three-variable core coordinate `T`.-/
def t : CoreP :=
  crat (-1 / 2) *
    ((crat 1 + U) ^ 3 * Wc
      + Yc ^ 2 * (crat 1 + U) * (crat 4 + crat 3 * U))

/-- The three-variable Hamiltonian correction.-/
def h : CoreP :=
    crat (1 / 20) * Yc ^ 4 *
      (crat 18 * U ^ 2 + crat 78 * U + crat 125)
  + crat (3 / 10) * Wc * Yc ^ 2 *
      (U ^ 3 + crat 5 * U ^ 2 + crat 10 * U - crat 5)
  - crat (1 / 6) * Wc ^ 2 * (crat 9 * U + crat 2)
  - crat (1 / 6) * Xc ^ 2 * Wc ^ 3

def cpartial (i : CoreVar) (f : CoreP) : CoreP := MvPolynomial.pderiv i f

/-- Coefficient of `dX_i ∧ dX_j` in `df ∧ dg`.-/
def wedgeCoeff (f g : CoreP) (i j : CoreVar) : CoreP :=
  cpartial i f * cpartial j g - cpartial j f * cpartial i g

/-- `Q = Y + XW/3` in the source-coordinate computation.-/
def Q3 : CoreP := Yc + crat (1 / 3) * Xc * Wc

/-- Coefficient of `dX ∧ dY` in the residual two-form.-/
def A1 : CoreP := crat (9 / 2) * Q3 * (Wc + crat 21 * Q3 ^ 2)

/-- Coefficient of `dX ∧ dW` in the residual two-form.-/
def A2 : CoreP :=
    crat 3 * Q3 ^ 2
  + crat (1 / 6) * Wc * (crat 1 + crat 3 * Xc * Q3)
  + crat (3 / 2) * Xc * Q3 * (Wc + crat 21 * Q3 ^ 2)

/-- Coefficient of `dY ∧ dW` in the residual two-form.-/
def A3 : CoreP := crat (1 / 2) * (crat 1 + crat 3 * Xc * Q3)

private theorem coeff_XY :
    wedgeCoeff r h 0 1 + wedgeCoeff t s 0 1 = A1 := by
  apply MvPolynomial.funext
  intro v
  simp [wedgeCoeff, cpartial, r, h, t, s, A1, Q3, U, crat, Xc, Yc, Wc,
    MvPolynomial.pderiv_C, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow] <;>
    ring_nf

private theorem coeff_XW :
    wedgeCoeff r h 0 2 + wedgeCoeff t s 0 2 = A2 := by
  apply MvPolynomial.funext
  intro v
  simp [wedgeCoeff, cpartial, r, h, t, s, A2, Q3, U, crat, Xc, Yc, Wc,
    MvPolynomial.pderiv_C, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow] <;>
    ring_nf

private theorem coeff_YW :
    wedgeCoeff r h 1 2 + wedgeCoeff t s 1 2 = A3 := by
  apply MvPolynomial.funext
  intro v
  simp [wedgeCoeff, cpartial, r, h, t, s, A3, Q3, U, crat, Xc, Yc, Wc,
    MvPolynomial.pderiv_C, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow] <;>
    ring_nf

/-- The three coefficient identities constituting the manuscript's two-form certificate.-/
theorem coefficient_identity :
    (wedgeCoeff r h 0 1 + wedgeCoeff t s 0 1 = A1) ∧
    (wedgeCoeff r h 0 2 + wedgeCoeff t s 0 2 = A2) ∧
    (wedgeCoeff r h 1 2 + wedgeCoeff t s 1 2 = A3) :=
  ⟨coeff_XY, coeff_XW, coeff_YW⟩

/-- The determinant of the Jacobian with rows `∇f, ∇g, ∇k`.-/
def jac3 (f g k : CoreP) : CoreP :=
    cpartial 0 f * (cpartial 1 g * cpartial 2 k - cpartial 2 g * cpartial 1 k)
  - cpartial 1 f * (cpartial 0 g * cpartial 2 k - cpartial 2 g * cpartial 0 k)
  + cpartial 2 f * (cpartial 0 g * cpartial 1 k - cpartial 1 g * cpartial 0 k)

/-- The three rational points in the displayed core collision.-/
def corePoint0 : CoreVar → ℚ := ![0, 0, -1 / 4]
def corePoint1 : CoreVar → ℚ := ![1, -3 / 2, 13 / 2]
def corePoint2 : CoreVar → ℚ := ![-1, 3 / 2, 13 / 2]

def coreTarget : CoreVar → ℚ := ![0, 1 / 8, 0]

/-- Evaluate the core tuple `(r,t,s)` at a rational point.-/
def coreMap (v : CoreVar → ℚ) : CoreVar → ℚ :=
  ![MvPolynomial.eval v r, MvPolynomial.eval v t, MvPolynomial.eval v s]

/-- First point in the core collision.-/
theorem corePoint0_image : coreMap corePoint0 = coreTarget := by
  funext i
  fin_cases i <;>
    simp [coreMap, corePoint0, coreTarget, r, t, s, U, crat, Xc, Yc, Wc] <;>
    norm_num

/-- Second point in the core collision.-/
theorem corePoint1_image : coreMap corePoint1 = coreTarget := by
  funext i
  fin_cases i <;>
    simp [coreMap, corePoint1, coreTarget, r, t, s, U, crat, Xc, Yc, Wc] <;>
    norm_num

/-- Third point in the core collision.-/
theorem corePoint2_image : coreMap corePoint2 = coreTarget := by
  funext i
  fin_cases i <;>
    simp [coreMap, corePoint2, coreTarget, r, t, s, U, crat, Xc, Yc, Wc] <;>
    norm_num

end
end Core
end RankTwoPoisson
