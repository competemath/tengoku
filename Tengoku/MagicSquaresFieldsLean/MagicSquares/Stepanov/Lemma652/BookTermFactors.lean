import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma652.InnerLinear
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma652.FactorLinear
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

open Polynomial

variable {F : Type*} [Field F] [DecidableEq F]

/-!
# Equation (6.24) in the form actually used by LN97

On p. 306, `g` is a power of `f`.  This matters: the book applies
Corollary 6.49 in a way that leaves the factor `g^i` outside the new
polynomial `e_{ijn}`:

    E^(n)(f^M e_ij g^i) = f^(M-n) e_ijn g^i.

The previously compiled exploratory `StepanovLemma652TermFactors`
absorbed `g^i` into the Corollary-6.49 factor.  That is a valid
factorization, but it is not the literal factorization needed for the
degree count in (6.24).  This file corrects that modeling point.

We assume `g = f^s`; in the LN97 application
`s = (q-1)/m`.
-/

/-- The book's `e_{ijn}`, chosen linearly in the original coefficient
vector.  The exponent to which Corollary 6.49 is applied is
`M + s*i`.-/
noncomputable def stepanovBookDerivativeCoeffLinear
    {m u D M : ℕ}
    (f : Polynomial F) (s : ℕ)
    (hf : f ≠ 0)
    (hfdeg : 1 ≤ f.natDegree)
    (n : Fin M)
    (i : Fin m) (j : Fin (u + 1)) :
    StepanovUnknowns F m u D →ₗ[F] Polynomial F :=
  hassePowerFactorLinear
    f (M + s * (i : ℕ)) (n : ℕ)
      (by omega) hf hfdeg
    (stepanovInnerLinear (F := F) i j)

/-- The exponent arithmetic that keeps `g^i = f^(s*i)` outside the
new factor after differentiation.-/
theorem book_factor_exponent
    {M n s i : ℕ}
    (hn : n ≤ M) :
    M + s * i - n = (M - n) + s * i := by
  omega

/-- **LN97 (6.24), literal factorization.**-/
theorem stepanovBookDerivativeCoeff_spec
    {m u D M : ℕ}
    (f : Polynomial F) (s : ℕ)
    (hf : f ≠ 0)
    (hfdeg : 1 ≤ f.natDegree)
    (v : StepanovUnknowns F m u D)
    (n : Fin M)
    (i : Fin m) (j : Fin (u + 1)) :
    (hasseDeriv (n : ℕ))
      (f ^ M *
        stepanovInnerPolynomial v i j *
        (f ^ s) ^ (i : ℕ)) =
      f ^ (M - (n : ℕ)) *
        stepanovBookDerivativeCoeffLinear
          f s hf hfdeg n i j v *
        (f ^ s) ^ (i : ℕ) := by
  have hnM : (n : ℕ) ≤ M := Nat.le_of_lt n.isLt
  have hcore :=
    hassePowerFactorLinear_spec
      (F := F)
      f (M + s * (i : ℕ)) (n : ℕ)
      (by omega) hf hfdeg
      (stepanovInnerLinear (F := F) i j) v
  have hexp :
      M + s * (i : ℕ) - (n : ℕ) =
        (M - (n : ℕ)) + s * (i : ℕ) :=
    book_factor_exponent hnM
  calc
    (hasseDeriv (n : ℕ))
        (f ^ M *
          stepanovInnerPolynomial v i j *
          (f ^ s) ^ (i : ℕ))
        =
      (hasseDeriv (n : ℕ))
        (f ^ (M + s * (i : ℕ)) *
          stepanovInnerPolynomial v i j) := by
            congr 1
            rw [← pow_mul, pow_add]
            ring
    _ =
      f ^ (M + s * (i : ℕ) - (n : ℕ)) *
        stepanovBookDerivativeCoeffLinear
          f s hf hfdeg n i j v := hcore
    _ =
      f ^ (M - (n : ℕ)) *
        stepanovBookDerivativeCoeffLinear
          f s hf hfdeg n i j v *
        (f ^ s) ^ (i : ℕ) := by
          rw [hexp, pow_add, pow_mul]
          ring

/-- The important degree estimate from (6.24): there is no `i*deg g`
term, because `g^i` remains outside `e_{ijn}`.-/
theorem stepanovBookDerivativeCoeff_natDegree_le
    {m u D M : ℕ}
    (f : Polynomial F) (s : ℕ)
    (hf : f ≠ 0)
    (hfdeg : 1 ≤ f.natDegree)
    (v : StepanovUnknowns F m u D)
    (n : Fin M)
    (i : Fin m) (j : Fin (u + 1)) :
    (stepanovBookDerivativeCoeffLinear
      f s hf hfdeg n i j v).natDegree
      ≤ D + (n : ℕ) * (f.natDegree - 1) := by
  exact hassePowerFactorLinear_natDegree_le
    (F := F)
    f (M + s * (i : ℕ)) (n : ℕ) D
    (by omega) hf hfdeg
    (stepanovInnerLinear (F := F) i j) v
    (stepanovInnerPolynomial_natDegree_le v i j)

end LN97
end MagicSquares
