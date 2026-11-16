import Tengoku.RankTwoPoissonCounterexample.RankTwoPoisson.Definitions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Polynomial source coordinates

This file formalizes the explicit inverse formulas for the polynomial source
coordinate system `(x,y,β,D₀)`.  To avoid introducing a second four-variable
polynomial type, the symbols `(x,q,p,z)` below temporarily play the roles
`(X,Y,W,E₀)` from the manuscript's inverse calculation.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace RankTwoPoisson
namespace SourceCoordinates

open MvPolynomial

noncomputable section

/-- `Q = Y + XW/3`, represented in the ambient four-variable polynomial ring.-/
def Qs : P := q + rat (1 / 3) * x * p

/-- `A = 1 - 3XQ`.-/
def As : P := 1 - 3 * x * Qs

/-- `C = (1 + 3XQ)/2`.-/
def Cs : P := rat (1 / 2) * (1 + 3 * x * Qs)

/-- `M = W + 9Q²`.-/
def Ms : P := p + 9 * Qs ^ 2

/-- The inverse formula for the original variable `p`.-/
def pInv : P := 3 * Qs ^ 2 * Ms + 2 * As * z

/-- The inverse formula for the original variable `z`.-/
def zInv : P := Cs * Ms - 3 * x ^ 2 * z

/-- Recompute `β` after applying the proposed inverse.-/
def betaBack : P :=
  3 * x ^ 2 * pInv + 2 * (1 - 3 * x * Qs) * zInv - 9 * Qs ^ 2

/-- Recompute `y` after applying the proposed inverse.-/
def yBack : P := Qs - rat (1 / 3) * x * betaBack

/-- Recompute `D₀` after applying the proposed inverse.-/
def D0Back : P :=
  rat (1 / 2) * (1 + 3 * x * Qs) * pInv - 3 * Qs ^ 2 * zInv

/-- The inverse formulas recover the independent coordinate `W`.
@isnad1 id=eq.0h0v.s2.e0f3c6156b68 from=translated src=- shape=54c8eceb vocab=088fbdb6
-/
theorem betaBack_eq : betaBack = p := by
  apply MvPolynomial.funext
  intro v
  simp [betaBack, pInv, zInv, Qs, As, Cs, Ms, rat, x, q, p, z] <;> ring

/-- The inverse formulas recover the independent coordinate `Y`.
@isnad1 id=eq.0h0v.s2.15413475e6e9 from=translated src=- shape=54c8eceb vocab=9c7bcf2e
-/
theorem yBack_eq : yBack = q := by
  rw [yBack, betaBack_eq]
  apply MvPolynomial.funext
  intro v
  simp [Qs, rat, x, q, p] <;> ring

/-- The inverse formulas recover the independent coordinate `E₀`.
@isnad1 id=eq.0h0v.s2.1e7f0ec9d633 from=translated src=- shape=54c8eceb vocab=79464735
-/
theorem D0Back_eq : D0Back = z := by
  apply MvPolynomial.funext
  intro v
  simp [D0Back, pInv, zInv, Qs, As, Cs, Ms, rat, x, q, p, z] <;> ring

/-!
The preceding identities check the composite "new coordinates, inverse formulas,
then source coordinates".  The next identities check the opposite composite in
the original variables.
-/

/-- Reconstruct `q` from the original source coordinates.-/
def Qorig : P := y + rat (1 / 3) * x * beta

/-- Reconstruct the linear coordinate `M = β + 9Q²`.-/
def Morig : P := beta + 9 * Qorig ^ 2

/-- Recover the original `p` from `(x,y,β,D₀)`.-/
def pRecovered : P :=
  3 * Qorig ^ 2 * Morig + 2 * (1 - 3 * x * Qorig) * D0

/-- Recover the original `z` from `(x,y,β,D₀)`.-/
def zRecovered : P :=
  rat (1 / 2) * (1 + 3 * x * Qorig) * Morig - 3 * x ^ 2 * D0

/-- The reconstructed coordinate `Q` is the original `q`.
@isnad1 id=eq.0h0v.s2.4ec28dded516 from=translated src=- shape=54c8eceb vocab=022751f4
-/
theorem Qorig_eq : Qorig = q := by
  apply MvPolynomial.funext
  intro v
  simp [Qorig, y, rat, x, q] <;> ring

/-- The opposite composite recovers the original `p`.
@isnad1 id=eq.0h0v.s2.22a7ecb6a3e0 from=translated src=- shape=54c8eceb vocab=33ffb1f4
-/
theorem pRecovered_eq : pRecovered = p := by
  apply MvPolynomial.funext
  intro v
  simp [pRecovered, Morig, Qorig, D0, y, beta, B, a,
    rat, x, q, p, z] <;> ring

/-- The opposite composite recovers the original `z`.
@isnad1 id=eq.0h0v.s2.ef6d82430229 from=translated src=- shape=54c8eceb vocab=d176be1f
-/
theorem zRecovered_eq : zRecovered = z := by
  apply MvPolynomial.funext
  intro v
  simp [zRecovered, Morig, Qorig, D0, y, beta, B, a,
    rat, x, q, p, z] <;> ring

end
end SourceCoordinates
end RankTwoPoisson
