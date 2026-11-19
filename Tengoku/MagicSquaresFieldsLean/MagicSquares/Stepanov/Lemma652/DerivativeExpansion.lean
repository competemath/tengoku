import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma652.BookTermFactors
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Core.Corollary650CardMonomial
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma652.DecodeExpansion
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

open Polynomial
open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-!
# Equation (6.25)

Assume `g = f^s` and `M ≤ q`. Combining the literal (6.24)
factorization with Corollary 6.50 gives

  E^(n)(h)
    = f^(M-n) Σ_i Σ_j e_{ijn} g^i X^(qj),

for every `0 ≤ n < M`.

Version 2 proves the identity term-by-term after expanding both finite
sums. This is less brittle than asking `rw [map_sum]` to decide how far
to descend into the nested sums.
-/

/-- Polynomial identity (6.25), before evaluating at a field element.
@isnad1 id=eq.3h9v.s10.38341c6cf82c from=translated src=- shape=dbaa08f0 vocab=7d90d048
-/
theorem stepanovDerivativeExpansion
    {m u D M : ℕ}
    (f : Polynomial F) (s : ℕ)
    (hf : f ≠ 0)
    (hfdeg : 1 ≤ f.natDegree)
    (hMcard : M ≤ Fintype.card F)
    (v : StepanovUnknowns F m u D)
    (n : Fin M) :
    (hasseDeriv (n : ℕ))
      (stepanovAuxiliary
        (Fintype.card F) M f (f ^ s)
        (stepanovDecode v))
      =
    f ^ (M - (n : ℕ)) *
      (∑ i : Fin m,
        ∑ j : Fin (u + 1),
          stepanovBookDerivativeCoeffLinear
              f s hf hfdeg n i j v *
            (f ^ s) ^ (i : ℕ) *
            (X ^ Fintype.card F : Polynomial F) ^ (j : ℕ)) := by
  have hncard : (n : ℕ) < Fintype.card F :=
    lt_of_lt_of_le n.isLt hMcard

  rw [stepanovAuxiliary_decode_eq_doubleSum]
  simp only [map_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj

  have hfrob :=
    hasseDeriv_mul_cardMonomial
      (F := F) (n : ℕ) hncard
      (f ^ M *
        stepanovInnerPolynomial v i j *
        (f ^ s) ^ (i : ℕ))
      (j : ℕ)

  have hterm :=
    stepanovBookDerivativeCoeff_spec
      (F := F) f s hf hfdeg v n i j

  calc
    (hasseDeriv (n : ℕ))
        (f ^ M *
          stepanovInnerPolynomial v i j *
          (f ^ s) ^ (i : ℕ) *
          (X ^ Fintype.card F : Polynomial F) ^ (j : ℕ))
        =
      (hasseDeriv (n : ℕ))
          (f ^ M *
            stepanovInnerPolynomial v i j *
            (f ^ s) ^ (i : ℕ)) *
        (X ^ Fintype.card F : Polynomial F) ^ (j : ℕ) := hfrob
    _ =
      (f ^ (M - (n : ℕ)) *
          stepanovBookDerivativeCoeffLinear
            f s hf hfdeg n i j v *
          (f ^ s) ^ (i : ℕ)) *
        (X ^ Fintype.card F : Polynomial F) ^ (j : ℕ) := by
          rw [hterm]
    _ =
      f ^ (M - (n : ℕ)) *
        (stepanovBookDerivativeCoeffLinear
            f s hf hfdeg n i j v *
          (f ^ s) ^ (i : ℕ) *
          (X ^ Fintype.card F : Polynomial F) ^ (j : ℕ)) := by
          ring

end LN97
end MagicSquares
