import Tengoku.Seed.Algebra.Polynomial.Taylor
import Tengoku.Seed.Algebra.Polynomial.Div

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

open Polynomial

/-!
# LN97 Chapter 6: hyperderivatives / Hasse derivatives

Lidl--Niederreiter call the maps `E^(n)` on p. 303 "hyperderivatives".
Mathlib's `Polynomial.hasseDeriv n` is exactly the same operator:

  D_n (Σ_j a_j X^j) = Σ_j (j.choose n) a_j X^(j-n).

This file begins the formalization of §§6.47--6.51 of LN97.
-/

variable {K : Type*} [Field K]

/-- LN97 Lemma 6.47 for two factors.

The book states the corresponding formula for an arbitrary finite product.
Mathlib already proves the two-factor Leibniz rule for Hasse derivatives;
the finite-product form can be obtained from this by induction when it is
needed in the proof of LN97 6.49/6.52.
@isnad1 id=eq.0h4v.s10.fce9a60a846c from=translated src=- shape=eceec78c vocab=6e7b4262
-/
theorem ln97_6_47_two_factors
    (n : ℕ) (f g : Polynomial K) :
    (hasseDeriv n) (f * g) =
      ∑ ij ∈ Finset.antidiagonal n,
        (hasseDeriv ij.1) f * (hasseDeriv ij.2) g := by
  exact Polynomial.hasseDeriv_mul n f g

/-- A divisibility form of LN97 Lemma 6.51.

If the first `M` Hasse derivatives vanish at `c`, then `(X - c)^M`
divides `f`.  This statement is valid even when `f = 0`, and is the
cleanest formal version of "c is a root of multiplicity at least M".

Instead of reproducing LN97's coefficient expansion around `c` by hand,
we use mathlib's Taylor operator.  Its `n`th coefficient is exactly the
value at `c` of the `n`th Hasse derivative.
@isnad1 id=dvd.1h4v.s9.9fd2df2c9040 from=translated src=- shape=cdab7f92 vocab=f7e76fc7
-/
theorem ln97_6_51_pow_dvd
    (f : Polynomial K) (c : K) (M : ℕ)
    (hvanish : ∀ n < M, eval c ((hasseDeriv n) f) = 0) :
    (X - C c) ^ M ∣ f := by
  have hcoeff :
      ∀ n < M, ((taylor c) f).coeff n = 0 := by
    intro n hn
    rw [Polynomial.taylor_coeff]
    exact hvanish n hn

  have hdvdTaylor : X ^ M ∣ (taylor c) f := by
    exact Polynomial.X_pow_dvd_iff.mpr hcoeff

  rcases hdvdTaylor with ⟨q, hq⟩
  refine ⟨(taylor (-c)) q, ?_⟩

  have ht := congrArg (fun p : Polynomial K => (taylor (-c)) p) hq

  -- Applying the inverse translation `taylor (-c)` sends
  -- `taylor c f` back to `f`, and sends `X` to `X - C c`.
  simpa [Polynomial.taylor_taylor, Polynomial.taylor_mul,
    Polynomial.taylor_X_pow, sub_eq_add_neg] using ht

/-- LN97 Lemma 6.51 in mathlib's `rootMultiplicity` language.

For a nonzero polynomial, the preceding divisibility statement is
equivalent to saying that the root multiplicity at `c` is at least `M`.
@isnad1 id=le.2h4v.s8.1c86557309e1 from=translated src=- shape=84cd0db5 vocab=c8852fe3
-/
theorem ln97_6_51_rootMultiplicity
    (f : Polynomial K) (c : K) (M : ℕ)
    (hf : f ≠ 0)
    (hvanish : ∀ n < M, eval c ((hasseDeriv n) f) = 0) :
    M ≤ rootMultiplicity c f := by
  apply (Polynomial.le_rootMultiplicity_iff hf).2
  exact ln97_6_51_pow_dvd f c M hvanish

end LN97
end MagicSquares
