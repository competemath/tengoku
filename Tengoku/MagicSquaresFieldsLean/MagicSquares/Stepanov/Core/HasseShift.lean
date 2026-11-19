import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Core.Hasse

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace MagicSquares
namespace LN97

open Polynomial

variable {K : Type*} [Field K]

/-- Hasse derivatives commute with translation.

This is the formal device that lets us reduce LN97 Corollary 6.48
from `(X - c)^t` to the monomial `X^t`.-/
theorem hasseDeriv_taylor_comm
    (n : ℕ) (c : K) (f : Polynomial K) :
    (hasseDeriv n) ((taylor c) f) =
      (taylor c) ((hasseDeriv n) f) := by
  ext k
  rw [Polynomial.hasseDeriv_coeff]
  rw [Polynomial.taylor_coeff]
  rw [Polynomial.taylor_coeff]
  have hcomp :
      (hasseDeriv k) ((hasseDeriv n) f) =
        (((k + n).choose k • hasseDeriv (k + n)) f) := by
    simpa only [LinearMap.comp_apply] using
      DFunLike.congr_fun (Polynomial.hasseDeriv_comp k n) f
  rw [hcomp]
  simp [Nat.choose_symm_add, nsmul_eq_mul]

/-- LN97 Corollary 6.48.

For `c ∈ K`,
`E^(n)((x-c)^t) = (t choose n) (x-c)^(t-n)`.

This is stated exactly as a polynomial identity, so it is valid in every
characteristic; the binomial coefficient is interpreted in `K`.-/
theorem ln97_6_48
    (c : K) (n t : ℕ) :
    (hasseDeriv n) ((X - C c) ^ t) =
      C (↑(t.choose n) : K) * (X - C c) ^ (t - n) := by
  have hshift :
      (X - C c) ^ t = (taylor (-c)) (X ^ t : Polynomial K) := by
    simp [sub_eq_add_neg]
  rw [hshift, hasseDeriv_taylor_comm]
  rw [← Polynomial.monomial_one_right_eq_X_pow t]
  rw [Polynomial.hasseDeriv_monomial]
  simp [Polynomial.taylor_monomial, sub_eq_add_neg]

/-- The degree loss under a Hasse derivative, used in the estimate following
LN97 Corollary 6.49.  Mathlib already contains this fundamental estimate.-/
theorem hasseDeriv_natDegree_le
    (f : Polynomial K) (n : ℕ) :
    ((hasseDeriv n) f).natDegree ≤ f.natDegree - n := by
  exact Polynomial.natDegree_hasseDeriv_le f n

end LN97
end MagicSquares
