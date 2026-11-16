import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The explicit rank-two Poisson construction

This file transcribes the four polynomial variables and the explicit polynomials
from *An Explicit Counterexample to the Rank-Two Poisson Conjecture*.

The displayed polynomials have coefficients in `ℚ`. `CharacteristicZero`
extends the construction to every field of characteristic zero.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace RankTwoPoisson

noncomputable section

open MvPolynomial

/-- Variables are ordered `(x,q,p,z)`.-/
abbrev Var := Fin 4

/-- The polynomial algebra `ℚ[x,q,p,z]`.-/
abbrev P := MvPolynomial Var ℚ

/-- Embed a rational coefficient as a constant polynomial.-/
def rat (r : ℚ) : P := C r

/-- The four polynomial generators, in the order `(x,q,p,z)`.-/
def x : P := X 0
def q : P := X 1
def p : P := X 2
def z : P := X 3

/-- `a = 1 - 3xq`.-/
def a : P := rat 1 - rat 3 * x * q

/-- `B = 3x²p + 2az`.-/
def B : P := rat 3 * x ^ 2 * p + rat 2 * a * z

/-- The auxiliary source coordinate `β = B - 9q²`.-/
def beta : P := B - rat 9 * q ^ 2

/-- The auxiliary source coordinate `y = q - xβ/3`.-/
def y : P := q - rat (1 / 3) * x * beta

/-- `u = xy`.-/
def u : P := x * y

/-- The first output polynomial.-/
def R : P := rat 2 * x - rat 3 * x ^ 2 * y - x ^ 3 * beta

/-- The fourth output polynomial in the manuscript's `(R,T,D,S)` ordering.-/
def S : P :=
  y
    + rat 3 * x * (rat 1 + u) ^ 2 * beta
    + rat 3 * x * y ^ 2 * (rat 4 + rat 3 * u)

/-- The second output polynomial.-/
def T : P :=
  rat (-1 / 2) *
    ((rat 1 + u) ^ 3 * beta
      + y ^ 2 * (rat 1 + u) * (rat 4 + rat 3 * u))

/-- The uncorrected momentum coordinate.-/
def D0 : P :=
  rat (1 / 2) * (rat 1 + rat 3 * x * q) * p - rat 3 * q ^ 2 * z

/-- The Hamiltonian correction.-/
def H : P :=
    rat (1 / 20) * y ^ 4 *
      (rat 18 * u ^ 2 + rat 78 * u + rat 125)
  + rat (3 / 10) * beta * y ^ 2 *
      (u ^ 3 + rat 5 * u ^ 2 + rat 10 * u - rat 5)
  - rat (1 / 6) * beta ^ 2 * (rat 9 * u + rat 2)
  - rat (1 / 6) * x ^ 2 * beta ^ 3

/-- The corrected third output polynomial.-/
def D : P := D0 + H

/-- Formal polynomial differentiation in the variable indexed by `i`.-/
def polyDeriv (i : Var) (f : P) : P := MvPolynomial.pderiv i f

/--
The canonical Poisson bracket for the ordered generators `(x,q,p,z)`:
`{f,g} = f_p g_x - f_x g_p + f_z g_q - f_q g_z`.-/
def bracket (f g : P) : P :=
    polyDeriv 2 f * polyDeriv 0 g - polyDeriv 0 f * polyDeriv 2 g
  + polyDeriv 3 f * polyDeriv 1 g - polyDeriv 1 f * polyDeriv 3 g

/-- The target generator tuple `(R,T,D,S)`.-/
def output : Var → P := ![R, T, D, S]

/-- The algebra endomorphism obtained by substitution of the four outputs.-/
def Phi : P →ₐ[ℚ] P := MvPolynomial.aeval output

/-- A local formulation of preservation of the canonical Poisson bracket.-/
def IsPoisson (φ : P →ₐ[ℚ] P) : Prop :=
  ∀ f g : P, bracket (φ f) (φ g) = φ (bracket f g)

/-- Being induced by an algebra equivalence.-/
def IsAlgAutomorphism (φ : P →ₐ[ℚ] P) : Prop :=
  ∃ e : P ≃ₐ[ℚ] P, e.toAlgHom = φ

/-- The point map associated with a polynomial algebra endomorphism.-/
def pointMap (φ : P →ₐ[ℚ] P) (v : Var → ℚ) : Var → ℚ :=
  fun i => MvPolynomial.aeval v (φ (X i))

end

end RankTwoPoisson
