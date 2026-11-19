import Tengoku.MagicSquaresFieldsLean.MagicSquares.Jacobi.Characters
import Tengoku.Seed.NumberTheory.JacobiSum.Basic
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares

open scoped BigOperators

/-!
# The sharp Weil theorem actually used by the paper

A useful correction to the project architecture: LN97 Theorem 6.53 is a
coarser Stepanov point-count estimate.  It is valuable infrastructure, but
its constant is not the sharp `(r-1) sqrt(q)` estimate used in Sections 5,
7, 12, and 14 of the paper.

The sharp multiplicative-character theorem (the paper's Theorem 5.1 /
LN97 Ch. 5) is obtained from the split L-polynomial representation and
the power-sum lemma, using Theorem 6.53 for the coarse extension-field bounds.

`Weil.SharpQuadratic.sharp_quadratic_weil` now proves the quadratic
interface below in odd characteristic. `Weil.SharpMultiplicative` proves
both arbitrary-character interfaces, including repeated-root products.

This file gives the precise Lean interfaces for split squarefree
polynomials and for products with positive exponents. The latter is needed
for general powers; the squarefree version alone does not cover Section 14.
-/

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Sharp Weil bound for a product of distinct linear factors.

The product is written as `prod_i (x - root_i)`.  Multiplying by a nonzero
constant does not change the norm of a multiplicative-character sum, so this
is the exact form needed for products `prod_i (1 + lambda_i t)`.-/
def HasSplitMultiplicativeWeilBound (F : Type*)
    [Field F] [Fintype F] [DecidableEq F] : Prop :=
  ∀ (r : ℕ) (roots : Fin r → F),
    0 < r →
    Function.Injective roots →
    ∀ chi : MulChar F ℂ, chi ≠ 1 →
      ‖∑ x : F, chi (∏ i : Fin r, (x - roots i))‖
        ≤ (r - 1 : ℕ) * Real.sqrt (Fintype.card F : ℝ)

/-- Quadratic-character specialization of the sharp split Weil target.-/
def HasSplitQuadraticWeilBound (F : Type*)
    [Field F] [Fintype F] [DecidableEq F] : Prop :=
  ∀ (r : ℕ) (roots : Fin r → F),
    0 < r →
    Function.Injective roots →
    ‖∑ x : F,
        ((quadraticChar F
          (∏ i : Fin r, (x - roots i)) : ℤ) : ℂ)‖
      ≤ (r - 1 : ℕ) * Real.sqrt (Fintype.card F : ℝ)

/-- The split Weil bound with multiplicities, as required in Sections 12
and 14. All listed roots actually occur, and at least one multiplicity is
not divisible by the order of the character. In particular the product
cannot be an `orderOf chi`-th power over the algebraic closure.-/
def HasSplitPowerMultiplicativeWeilBound (F : Type*)
    [Field F] [Fintype F] [DecidableEq F] : Prop :=
  ∀ (r : ℕ) (roots : Fin r → F) (exponents : Fin r → ℕ),
    0 < r → Function.Injective roots →
    (∀ i, 0 < exponents i) →
    ∀ chi : MulChar F ℂ, chi ≠ 1 →
      (∃ i, ¬ orderOf chi ∣ exponents i) →
      ‖∑ x : F, chi (∏ i : Fin r, (x - roots i) ^ exponents i)‖
        ≤ (r - 1 : ℕ) * Real.sqrt (Fintype.card F : ℝ)

/-- The exponent form implies the squarefree form by taking all exponents
equal to one. The positivity hypothesis rules out the empty-product
counterexample.
@isnad1 id=hassplit.1h1v.s4.e9d055bda147 from=translated src=- shape=7ddc04c7 vocab=4bdab20f
-/
theorem HasSplitPowerMultiplicativeWeilBound.squarefree
    (h : HasSplitPowerMultiplicativeWeilBound F) :
    HasSplitMultiplicativeWeilBound F := by
  intro r roots hr hinj chi hchi
  have horder : ¬ orderOf chi ∣ 1 := by
    simpa only [Nat.dvd_one, orderOf_eq_one_iff] using hchi
  simpa using h r roots (fun _ => 1) hr hinj (by simp) chi hchi
    ⟨⟨0, hr⟩, horder⟩

/-- Specialization to the nontrivial quadratic character requires odd
characteristic.
@isnad1 id=hassplit.2h1v.s5.e6f2e9afa685 from=translated src=- shape=2221b9e8 vocab=882ba686
-/
theorem HasSplitMultiplicativeWeilBound.quadratic
    (h : HasSplitMultiplicativeWeilBound F) (hodd : ringChar F ≠ 2) :
    HasSplitQuadraticWeilBound F := by
  intro r roots hr hinj
  simpa only [quadraticCharC_apply] using
    h r roots hr hinj (quadraticCharC F) (quadraticCharC_ne_one hodd)

end MagicSquares
