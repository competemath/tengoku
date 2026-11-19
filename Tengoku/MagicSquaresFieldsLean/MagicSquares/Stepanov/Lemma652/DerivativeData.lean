import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma652.Unknowns
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma652.Core
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

open Polynomial
open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-!
# The derivative interface in LN97 Lemma 6.52

Corollaries 6.49 and 6.50 imply that for every derivative order `n<M`
there are polynomials `e_{i,j,n}` depending linearly on the original
unknown coefficients such that, after evaluation at `c`,

  E^(n)(h)(c)
    = f(c)^(M-n) * Σ_i Σ_j e_{i,j,n}(c) g(c)^i (c^q)^j.

The structure below records precisely this statement.
`DerivativeDataConstruct` constructs it from Corollaries 6.49 and 6.50;
`Complete` uses it in the proof of the full Lemma 6.52.
-/

/-- Linear derivative-factor data for the literal Stepanov unknowns.-/
structure StepanovDerivativeData
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (m u D M Emax : ℕ)
    (f g : Polynomial F) where
  eDeriv :
    StepanovUnknowns F m u D →ₗ[F]
      (Fin M → Fin m → Fin (u + 1) → Polynomial F)
  degree_le :
    ∀ v n i j, (eDeriv v n i j).natDegree ≤ Emax
  expansion_eval :
    ∀ v (n : Fin M) (c : F),
      eval c
        ((hasseDeriv (n : ℕ))
          (stepanovAuxiliary
            (Fintype.card F) M f g
            (stepanovDecode v)))
        =
      eval c (f ^ (M - (n : ℕ))) *
        (∑ i : Fin m,
          ∑ j : Fin (u + 1),
            eval c (eDeriv v n i j) *
              (eval c g) ^ (i : ℕ) *
              (c ^ Fintype.card F) ^ (j : ℕ))

end LN97
end MagicSquares
