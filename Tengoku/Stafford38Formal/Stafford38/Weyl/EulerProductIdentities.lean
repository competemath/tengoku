module
public import Tengoku.Stafford38Formal.proofs.weyl_pure_power
public import Tengoku.Stafford38Formal.Stafford38.EvolutionaryCertificate

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms eulerPolynomialEval_falling` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms eulerPolynomialEval_rising` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms eval_fallingEulerProduct` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms eval_risingEulerProduct` (it only prints; the queue checks the axioms of every declaration). -/

@[expose] public section

/-! Public Euler-product identities for the Weyl pair calculation.

This module reuses the generic rising/falling calculus in
`Stafford38.EvolutionaryCertificate` and exports the explicit polynomial
evaluation identities used by the paper.
-/

namespace Stafford38.Weyl.EulerProductIdentities

noncomputable section

variable {A : Type*} [Ring A] [Algebra ℚ A]

/-- Public names specialize the shared coefficient-ring factorial polynomials.-/
abbrev fallingEulerPolynomial : ℕ → Polynomial ℚ :=
  Stafford38.Evolution.fallingPoly ℚ

abbrev risingEulerPolynomial : ℕ → Polynomial ℚ :=
  Stafford38.Evolution.risingPoly ℚ

/-- The falling polynomial is the product of the Euler factors `X-i`.
@isnad1 id=eq.0h1v.s6.011785769603 from=translated src=- shape=ded08971 vocab=68789b05
-/
theorem fallingEulerPolynomial_eq_prod (n : ℕ) :
    fallingEulerPolynomial n = ∏ i ∈ Finset.range n,
      (Polynomial.X - Polynomial.C (i : ℚ)) := by
  change Stafford38.Evolution.fallingPoly ℚ n = _
  induction n with
  | zero => simp [Stafford38.Evolution.fallingPoly]
  | succ n ih =>
      rw [Stafford38.Evolution.fallingPoly_succ, ih, Finset.prod_range_succ]

/-- The rising polynomial is the product of the Euler factors `X+(i+1)`.
@isnad1 id=eq.0h1v.s6.847a52fb88c5 from=translated src=- shape=4d880e40 vocab=936d8849
-/
theorem risingEulerPolynomial_eq_prod (n : ℕ) :
    risingEulerPolynomial n = ∏ i ∈ Finset.range n,
      (Polynomial.X + Polynomial.C ((i + 1 : ℕ) : ℚ)) := by
  change Stafford38.Evolution.risingPoly ℚ n = _
  induction n with
  | zero => simp [Stafford38.Evolution.risingPoly]
  | succ n ih =>
      rw [Stafford38.Evolution.risingPoly_succ, ih, Finset.prod_range_succ]
      push_cast
      rfl

/-- Evaluation of the explicit falling Euler product gives `x^n * d^n`.
@isnad1 id=eq.1h4v.s7.cb705adc65d8 from=translated src=- shape=7db5e79e vocab=03a07fae
-/
theorem eulerPolynomialEval_falling (x d : A)
    (h : d * x = x * d + 1) (n : ℕ) :
    Stafford.eulerPolynomialEval x d (fallingEulerPolynomial n) = x ^ n * d ^ n := by
  change Polynomial.aeval (Stafford38.Evolution.euler x d)
    (Stafford38.Evolution.fallingPoly ℚ n) = x ^ n * d ^ n
  rw [Stafford38.Evolution.aeval_fallingPoly]
  simpa [Stafford38.Evolution.euler] using
    (Stafford38.Evolution.pow_mul_pow_eq_falling (x := x) (p := d) h n).symm

/-- Evaluation of the explicit rising Euler product gives `d^n * x^n`.
@isnad1 id=eq.1h4v.s7.28527e1d08fb from=translated src=- shape=07b186fb vocab=7bee9f54
-/
theorem eulerPolynomialEval_rising (x d : A)
    (h : d * x = x * d + 1) (n : ℕ) :
    Stafford.eulerPolynomialEval x d (risingEulerPolynomial n) = d ^ n * x ^ n := by
  change Polynomial.aeval (Stafford38.Evolution.euler x d)
    (Stafford38.Evolution.risingPoly ℚ n) = d ^ n * x ^ n
  rw [Stafford38.Evolution.aeval_risingPoly]
  simpa [Stafford38.Evolution.euler] using
    (Stafford38.Evolution.pow_mul_pow_eq_rising (x := x) (p := d) h n).symm

/-- Evaluation of the falling product written with a finite-product sign.
@isnad1 id=eq.1h4v.s8.ae2b61df4bea from=translated src=- shape=b9a56ba4 vocab=7f3d5c20
-/
theorem eval_fallingEulerProduct (x d : A)
    (h : d * x = x * d + 1) (n : ℕ) :
    Stafford.eulerPolynomialEval x d
      (∏ i ∈ Finset.range n, (Polynomial.X - Polynomial.C (i : ℚ))) =
        x ^ n * d ^ n := by
  rw [← fallingEulerPolynomial_eq_prod n]
  exact eulerPolynomialEval_falling x d h n

/-- Evaluation of the rising product written with a finite-product sign.
@isnad1 id=eq.1h4v.s8.0835391ddfd7 from=translated src=- shape=eb7fe0c3 vocab=adc4130f
-/
theorem eval_risingEulerProduct (x d : A)
    (h : d * x = x * d + 1) (n : ℕ) :
    Stafford.eulerPolynomialEval x d
      (∏ i ∈ Finset.range n,
        (Polynomial.X + Polynomial.C ((i + 1 : ℕ) : ℚ))) =
          d ^ n * x ^ n := by
  rw [← risingEulerPolynomial_eq_prod n]
  exact eulerPolynomialEval_rising x d h n

end

end Stafford38.Weyl.EulerProductIdentities
