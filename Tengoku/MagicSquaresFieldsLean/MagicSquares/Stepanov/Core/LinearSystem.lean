import Tengoku.Seed.LinearAlgebra.FiniteDimensional.Lemmas
import Tengoku.Seed.LinearAlgebra.Dimension.Constructions
import Tengoku.Seed.Algebra.Module.Submodule.Lattice
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

/-!
# The homogeneous linear-system step in LN97 Lemma 6.52

On p. 307, Lidl--Niederreiter reach `S` homogeneous linear equations
in `A` unknown coefficients.  The only linear-algebra input needed there is

    S < A  ==>  the homogeneous system has a nonzero solution.

This file packages exactly that statement for coordinate spaces.
-/

variable {F : Type*} [Field F]

/-- If a linear map has fewer output coordinates than input coordinates,
then its kernel contains a nonzero vector.

This is the formal version of the sentence on LN97 p. 307 saying that
`S < A` homogeneous linear equations in `A` coefficients have a
nontrivial solution.-/
theorem exists_ne_zero_mem_ker_of_lt
    {A S : ℕ}
    (hSA : S < A)
    (T : (Fin A → F) →ₗ[F] (Fin S → F)) :
    ∃ v : Fin A → F, v ≠ 0 ∧ T v = 0 := by
  have hdim :
      Module.finrank F (Fin S → F) <
        Module.finrank F (Fin A → F) := by
    simpa only [Module.finrank_fin_fun] using hSA
  have hk : T.ker ≠ (⊥ : Submodule F (Fin A → F)) :=
    LinearMap.ker_ne_bot_of_finrank_lt hdim
  rcases Submodule.exists_mem_ne_zero_of_ne_bot hk with ⟨v, hvker, hvne⟩
  refine ⟨v, hvne, ?_⟩
  simpa only [LinearMap.mem_ker] using hvker

end LN97
end MagicSquares
