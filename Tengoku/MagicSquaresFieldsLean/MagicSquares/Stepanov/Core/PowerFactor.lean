import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Core.HasseShift
import Tengoku.Seed.Algebra.BigOperators.Ring.Finset
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

open Polynomial

variable {K : Type*} [Field K]

/-!
# LN97 Corollary 6.49: the power factor

The first assertion of Corollary 6.49 says that for `n ≤ t`,
the `n`th hyperderivative of `w * f^t` is still divisible by
`f^(t-n)`.

We first prove the corresponding statement for `f^t` itself.  This is
the formal version of the observation in LN97 that in every Leibniz
summand at most `n` copies of `f` can receive a positive-order
hyperderivative.
-/

/-- For every `t,n`, taking the `n`th Hasse derivative of `f^t` can
remove at most `n` copies of `f`.

The use of `t - n` makes the statement valid without assuming `n ≤ t`.-/
theorem hasseDeriv_pow_factor_dvd
    (f : Polynomial K) (t n : ℕ) :
    f ^ (t - n) ∣ (hasseDeriv n) (f ^ t) := by
  induction t generalizing n with
  | zero =>
      simp
  | succ t ih =>
      rw [pow_succ, Polynomial.hasseDeriv_mul]
      apply Finset.dvd_sum
      intro ij hij
      rcases ij with ⟨i, j⟩
      have hsum : i + j = n := by
        simpa using hij
      have hIH :
          f ^ (t - i) ∣ (hasseDeriv i) (f ^ t) :=
        ih i
      by_cases hj0 : j = 0
      · subst j
        simp only [add_zero] at hsum
        subst n
        by_cases hi : i ≤ t
        · rcases hIH with ⟨a, ha⟩
          refine ⟨a, ?_⟩
          have hexp :
              t + 1 - i = (t - i) + 1 := by
            omega
          rw [Polynomial.hasseDeriv_zero', ha, hexp, pow_succ]
          ring
        · have hexp : t + 1 - i = 0 := by
            omega
          simp [hexp]
      · have hexp :
            t + 1 - n ≤ t - i := by
          omega
        have hpow :
            f ^ (t + 1 - n) ∣ f ^ (t - i) :=
          pow_dvd_pow f hexp
        rcases hpow with ⟨b, hb⟩
        rcases hIH with ⟨a, ha⟩
        refine ⟨b * a * (hasseDeriv j) f, ?_⟩
        rw [ha, hb]
        ring

/-- The factorization assertion in LN97 Corollary 6.49.

For `n ≤ t` there is a polynomial `w₁` such that

`E^(n)(w f^t) = w₁ f^(t-n)`.

The degree estimate on `w₁` is added in the next step; isolating the
factorization first makes the Stepanov argument substantially easier to
debug in Lean.-/
theorem ln97_6_49_factor
    (w f : Polynomial K) (t n : ℕ) (hnt : n ≤ t) :
    ∃ w₁ : Polynomial K,
      (hasseDeriv n) (w * f ^ t) = w₁ * f ^ (t - n) := by
  have hdvd :
      f ^ (t - n) ∣ (hasseDeriv n) (w * f ^ t) := by
    rw [Polynomial.hasseDeriv_mul]
    apply Finset.dvd_sum
    intro ij hij
    rcases ij with ⟨i, j⟩
    have hsum : i + j = n := by
      simpa using hij
    have hjle : j ≤ n := by
      omega
    have hexp : t - n ≤ t - j := by
      omega
    have hpow :
        f ^ (t - n) ∣ f ^ (t - j) :=
      pow_dvd_pow f hexp
    have hderiv :
        f ^ (t - j) ∣ (hasseDeriv j) (f ^ t) :=
      hasseDeriv_pow_factor_dvd f t j
    have hterm :
        f ^ (t - n) ∣ (hasseDeriv j) (f ^ t) :=
      hpow.trans hderiv
    rcases hterm with ⟨a, ha⟩
    refine ⟨(hasseDeriv i) w * a, ?_⟩
    rw [ha]
    ring
  rcases hdvd with ⟨w₁, hw₁⟩
  refine ⟨w₁, ?_⟩
  rw [hw₁]
  ring

end LN97
end MagicSquares
