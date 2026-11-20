import Tengoku.Seed.Algebra.BigOperators.Field
import Tengoku.Seed.Algebra.Polynomial.Eval.Defs
import Tengoku.Seed.NumberTheory.Cyclotomic.PrimitiveRoots
import Tengoku.Seed.RingTheory.RootsOfUnity.Lemmas
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Basic finite products and sums

Author: Joesph D. Burke III.
-/

noncomputable section

open scoped BigOperators

namespace IwasawaTower

open Finset Polynomial

/-- The finite product `(-q;q)ᵣ = ∏_{j=1}^r (1 + q^j)`.-/
def pochhammer {R : Type*} [CommRing R] (q : R) (r : ℕ) : R :=
  ∏ j ∈ Finset.range r, (1 + q ^ (j + 1))

/-- The polynomial `Aᵣ(X) = ∏_{j=1}^r (1 + X^j)`.-/
def APoly {R : Type*} [CommRing R] (r : ℕ) : R[X] :=
  ∏ j ∈ Finset.range r, (1 + X ^ (j + 1))

/-- The denominator-reversed polynomial
`F_N(X) = ∑_{r=0}^{N-1} X^(r+1) Aᵣ(X)^2`.-/
def FPoly {R : Type*} [CommRing R] (N : ℕ) : R[X] :=
  ∑ r ∈ Finset.range N, X ^ (r + 1) * APoly r ^ 2

/-- The finite cyclotomic mock-theta sum.-/
def T {K : Type*} [Field K] (N : ℕ) (ζ : K) : K :=
  ∑ r ∈ Finset.range N, ζ ^ (r * r) / pochhammer ζ r ^ 2

/-- The denominator-reversed finite sum over an arbitrary commutative ring.-/
def F {R : Type*} [CommRing R] (N : ℕ) (x : R) : R :=
  ∑ r ∈ Finset.range N, x ^ (r + 1) * pochhammer x r ^ 2

@[simp] theorem pochhammer_zero {R : Type*} [CommRing R] (q : R) :
    pochhammer q 0 = 1 := by
  simp [pochhammer]

@[simp] theorem eval_APoly {R : Type*} [CommRing R] (x : R) (r : ℕ) :
    Polynomial.eval x (APoly r) = pochhammer x r := by
  change (Polynomial.evalRingHom x) (APoly r) = pochhammer x r
  simp [APoly, pochhammer]

@[simp] theorem eval_FPoly {R : Type*} [CommRing R] (x : R) (N : ℕ) :
    Polynomial.eval x (FPoly N) = F N x := by
  change (Polynomial.evalRingHom x) (FPoly N) = F N x
  simp [FPoly, F]

end IwasawaTower
