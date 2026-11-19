import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Core.PowerDegree
import Tengoku.Seed.Data.Nat.Multiplicity
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

set_option maxHeartbeats 400000

open Polynomial

variable {K : Type*} [Field K]

/-!
# LN97 Corollary 6.50

Lidl--Niederreiter, p. 305:

If `K` has characteristic `p`, `v(x,y)` is a polynomial over `K`,
`s ∈ ℕ`, and

    h(x) = v(x, x^(p^s)),

then for `0 < n < p^s`, the `n`th hyperderivative of `h` is obtained by
taking the `n`th partial hyperderivative of `v` with respect to `x` and
then substituting `y = x^(p^s)`.

We encode a bivariate polynomial `v(x,y)` as

    v : Polynomial (Polynomial K),

where the outer variable is `y` and the coefficients are polynomials in
the inner variable `x`.
-/

/-- Apply the `n`th Hasse derivative in the `x` variable coefficientwise
to a polynomial `v(x,y) ∈ K[x][y]`.-/
noncomputable def partialHasseX
    (n : ℕ) (v : Polynomial (Polynomial K)) :
    Polynomial (Polynomial K) :=
  v.sum fun j a => monomial j ((hasseDeriv n) a)

/-- Substitute `y = X^q` in a polynomial `v(x,y) ∈ K[x][y]`.-/
noncomputable def substYXPow
    (q : ℕ) (v : Polynomial (Polynomial K)) :
    Polynomial K :=
  eval (X ^ q) v

/-- A natural number divisible by the characteristic casts to zero.
@isnad1 id=eq.1h3v.s5.3d543a89723a from=translated src=- shape=c330e99e vocab=d904b55f
-/
theorem natCast_eq_zero_of_char_dvd
    {p a : ℕ} [CharP K p] (hpa : p ∣ a) :
    (a : K) = 0 := by
  rcases hpa with ⟨b, rfl⟩
  rw [Nat.cast_mul, CharP.cast_eq_zero K p, zero_mul]

/-- Every interior binomial coefficient of `p^s` vanishes in
characteristic `p`.
@isnad1 id=eq.3h4v.s6.eab4e3af174f from=translated src=- shape=502a7bf1 vocab=c1132cbd
-/
theorem primePow_choose_cast_eq_zero
    {p s n : ℕ} [CharP K p]
    (hp : Nat.Prime p)
    (hn0 : n ≠ 0)
    (hnq : n ≠ p ^ s) :
    ((p ^ s).choose n : K) = 0 := by
  apply natCast_eq_zero_of_char_dvd (K := K) (p := p)
  exact hp.dvd_choose_pow hn0 hnq

/-- The key calculation in the proof of LN97 6.50:
for `0 < n < p^s`, the `n`th Hasse derivative of `X^(p^s)` is zero.
@isnad1 id=eq.3h4v.s8.d367aebdad9d from=translated src=- shape=ce486897 vocab=4321a8f7
-/
theorem ln97_6_50_X_primePow
    {p s n : ℕ} [CharP K p]
    (hp : Nat.Prime p)
    (hnpos : 0 < n)
    (hnlt : n < p ^ s) :
    (hasseDeriv n) (X ^ (p ^ s) : Polynomial K) = 0 := by
  rw [← Polynomial.monomial_one_right_eq_X_pow]
  rw [Polynomial.hasseDeriv_monomial]
  have hcast :
      ((p ^ s).choose n : K) = 0 :=
    primePow_choose_cast_eq_zero (K := K) hp
      (Nat.ne_of_gt hnpos) (Nat.ne_of_lt hnlt)
  rw [hcast]
  simp

/-- The same vanishing for an arbitrary power of the Frobenius monomial.

For `0 < n < p^s`,

    E^(n)((X^(p^s))^r) = 0.

This is the fact LN97 uses when treating `X^(p^s)` as a new variable
that is constant for hyperderivatives of order below `p^s`.
@isnad1 id=eq.3h5v.s9.373494bea87a from=translated src=- shape=211d2790 vocab=4321a8f7
-/
theorem hasseDeriv_frobeniusMonomial_eq_zero
    {p s n : ℕ} [CharP K p]
    (hp : Nat.Prime p)
    (hnpos : 0 < n)
    (hnlt : n < p ^ s)
    (r : ℕ) :
    (hasseDeriv n) ((X ^ (p ^ s) : Polynomial K) ^ r) = 0 := by
  induction r generalizing n with
  | zero =>
      simpa using Polynomial.hasseDeriv_apply_one (R := K) n hnpos
  | succ r ih =>
      rw [pow_succ, Polynomial.hasseDeriv_mul]
      apply Finset.sum_eq_zero
      intro ij hij
      rcases ij with ⟨i, j⟩
      have hsum : i + j = n := by
        simpa using hij
      by_cases hi0 : i = 0
      · subst i
        have hj : j = n := by omega
        subst j
        rw [Polynomial.hasseDeriv_zero']
        rw [ln97_6_50_X_primePow (K := K) hp hnpos hnlt]
        simp
      · have hipos : 0 < i := Nat.pos_of_ne_zero hi0
        have hile : i ≤ n := by omega
        have hilt : i < p ^ s := lt_of_le_of_lt hile hnlt
        rw [ih (n := i) hipos hilt]
        simp

/-- Multiplying by a polynomial in `X^(p^s)` does not affect Hasse
differentiation of order below `p^s`.

This is the monomial form of the "partial derivative in `x` only"
statement in Corollary 6.50.
@isnad1 id=eq.3h6v.s10.fba7cfcb0a8b from=translated src=- shape=1248f227 vocab=85ae87ae
-/
theorem hasseDeriv_mul_frobeniusMonomial
    {p s n : ℕ} [CharP K p]
    (hp : Nat.Prime p)
    (_hnpos : 0 < n)
    (hnlt : n < p ^ s)
    (w : Polynomial K) (r : ℕ) :
    (hasseDeriv n)
        (w * (X ^ (p ^ s) : Polynomial K) ^ r) =
      (hasseDeriv n) w * (X ^ (p ^ s) : Polynomial K) ^ r := by
  rw [Polynomial.hasseDeriv_mul]
  classical
  have hanti :
      (∑ ij ∈ Finset.antidiagonal n,
        (hasseDeriv ij.1) w *
          (hasseDeriv ij.2) ((X ^ (p ^ s) : Polynomial K) ^ r)) =
      ∑ i ∈ Finset.range n.succ,
        (hasseDeriv i) w *
          (hasseDeriv (n - i)) ((X ^ (p ^ s) : Polynomial K) ^ r) := by
    exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j =>
        (hasseDeriv i) w *
          (hasseDeriv j) ((X ^ (p ^ s) : Polynomial K) ^ r)) n
  rw [hanti]
  have hsingle :
      (∑ i ∈ Finset.range n.succ,
        (hasseDeriv i) w *
          (hasseDeriv (n - i)) ((X ^ (p ^ s) : Polynomial K) ^ r)) =
      (hasseDeriv n) w *
        (hasseDeriv (n - n)) ((X ^ (p ^ s) : Polynomial K) ^ r) := by
    apply Finset.sum_eq_single_of_mem n
      (Finset.mem_range.mpr (Nat.lt_succ_self n))
    intro i hi hin
    have hi_le : i ≤ n := by
      exact Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hi_lt : i < n := lt_of_le_of_ne hi_le hin
    have hjpos : 0 < n - i := Nat.sub_pos_of_lt hi_lt
    have hjlt : n - i < p ^ s := by
      exact lt_of_le_of_lt (Nat.sub_le n i) hnlt
    rw [hasseDeriv_frobeniusMonomial_eq_zero
      (K := K) hp hjpos hjlt r]
    simp
  simpa [Polynomial.hasseDeriv_zero'] using hsingle

/-- Evaluating the coefficientwise partial Hasse derivative gives the
expected coefficient sum.
@isnad1 id=eq.0h4v.s9.808949c68024 from=translated src=- shape=b3169058 vocab=7a35a9b5
-/
theorem eval_partialHasseX
    (n q : ℕ) (v : Polynomial (Polynomial K)) :
    eval (X ^ q) (partialHasseX n v) =
      v.sum fun j a =>
        (hasseDeriv n) a * (X ^ q : Polynomial K) ^ j := by
  rw [partialHasseX]
  simpa using
    (Polynomial.eval_sum v
      (fun j a => monomial j ((hasseDeriv n) a))
      (X ^ q : Polynomial K))

/-- **LN97 Corollary 6.50, complete formal statement.**

Let `K` have prime characteristic `p`, let `v(x,y) ∈ K[x,y]`, put

    h(x) = v(x, x^(p^s)).

For `0 < n < p^s`, the `n`th Hasse derivative of `h` is obtained by
taking the `n`th Hasse derivative in the `x` variable coefficientwise
and then substituting `y = x^(p^s)`:

    E^(n)(v(x, x^(p^s)))
      = (E_x^(n) v)(x, x^(p^s)).
@isnad1 id=eq.3h5v.s8.6d478de3517d from=translated src=- shape=e981c338 vocab=ea82994a
-/
theorem ln97_6_50
    {p s n : ℕ} [CharP K p]
    (hp : Nat.Prime p)
    (hnpos : 0 < n)
    (hnlt : n < p ^ s)
    (v : Polynomial (Polynomial K)) :
    (hasseDeriv n) (substYXPow (p ^ s) v) =
      substYXPow (p ^ s) (partialHasseX n v) := by
  rw [substYXPow, Polynomial.eval_eq_sum]
  rw [substYXPow, eval_partialHasseX]
  rw [Polynomial.sum_def]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact hasseDeriv_mul_frobeniusMonomial
    (K := K) hp hnpos hnlt (v.coeff j) j

end LN97
end MagicSquares
