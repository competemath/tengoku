import Tengoku.Nlalib.NLAlib.Matrix.Basic.RankFactorization
import Tengoku.Nlalib.NLAlib.Matrix.Spectral.SylvesterQualitative

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Sylvester displacement generators

Low displacement rank is exactly the existence of generators of the requested
width. The definition uses the library's Sylvester linear map.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

/-- The Sylvester displacement rank of `X` with respect to the two operators.-/
def displacementRank {K m n : Type*} [Field K] [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m m K) (B : Matrix n n K)
    (X : Matrix m n K) : ℕ := (sylvesterLinearMap A B X).rank

/-- Sylvester displacement rank at most `r` is equivalent to a generator pair
with `r` columns. This includes zero rank and empty row or column types.
Source: user derivations, displacement generators.
atlas: displacement-rank-def
@isnad1 id=iff.0h7v.s8.6770ff21f401 from=translated src=- shape=a0e6afd5 vocab=181e4092
-/
theorem displacementRank_le_iff_exists_generators {K m n : Type*} [RCLike K]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m K) (B : Matrix n n K) (X : Matrix m n K) (r : ℕ) :
    displacementRank A B X ≤ r ↔
      ∃ (M : Matrix m (Fin r) K) (N : Matrix n (Fin r) K), A * X - X * B = M * Nᴴ :=
  rank_le_iff_exists_mul_conjTranspose (A * X - X * B) r

end NLAlib
