import Tengoku.PaperCLean.PaperC.Arithmetic.DyadicPrimeReciprocalSums
import Tengoku.PaperCLean.PaperC.Probability.LargePrimeDependencyGraph

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# An explicit analytic envelope for dependency edges

`LargePrimeDependencyGraph` proves the exact finite reduction

`E_Y ≤ (L+1)² ∑_{Y<p≤3N} (N/p+1)²`.

This module inserts the already certified Chebyshev reciprocal-square bound.
For `Y ≥ 4` we obtain

`E_Y ≤ (L+1)²
  (28 N²/(Y log₂Y) + 6 N²/Y + 3N)`.

The middle term deliberately uses the elementary estimate
`∑_{Y<p≤3N} 1/p ≤ 3N/Y`, rather than formalizing the sharper
`O(log log N)` estimate from the manuscript.  It is weaker than the displayed
bound in Lemma 13.6 but still retains the prime-sensitive
`1/(Y log Y)` term in the reciprocal-square contribution and is a useful
fully explicit finite milestone.
-/

namespace PaperC
namespace DependencyEdgeBound

open scoped BigOperators

open DyadicPrimeReciprocalSums
open LargePrimeDependencyGraph

/-!
Every prime in `(Y,3N]` lies in a deliberately oversized dyadic interval.
The reciprocal-square estimate is uniform in the dyadic exponent, so no
logarithmic rounding is needed.
-/
/--
@isnad1 id=le.1h2v.s5.6ea3b8feec57 from=translated src=- shape=ef736727 vocab=7515b025
-/
theorem largePrimesInRange_subset_dyadicPrimes
    {N Y : ℕ} (hY : 1 ≤ Y) :
    largePrimesInRange Y (3 * N) ⊆
      dyadicPrimes Y (3 * N) := by
  intro p hp
  have hpData := mem_largePrimesInRange.mp hp
  rw [mem_dyadicPrimes]
  refine ⟨hpData.1, hpData.2.1, ?_⟩
  have hpow : 3 * N ≤ 2 ^ (3 * N) :=
    (Nat.lt_two_pow_self (n := 3 * N)).le
  have hscale : 2 ^ (3 * N) ≤ Y * 2 ^ (3 * N) := by
    simpa only [one_mul] using
      Nat.mul_le_mul_right (2 ^ (3 * N)) hY
  exact hpData.2.2.trans (hpow.trans hscale)

/-- Prime-sensitive reciprocal-square sum on the dependency range.
@isnad1 id=le.1h2v.s6.aeb576911ea0 from=translated src=- shape=7e325bcf vocab=49ea6099
-/
theorem sum_inv_sq_largePrimesInRange_le
    {N Y : ℕ} (hY : 4 ≤ Y) :
    (∑ p ∈ largePrimesInRange Y (3 * N),
        1 / (p : ℚ) ^ 2) ≤
      28 / ((Y : ℚ) * (Nat.log 2 Y : ℚ)) := by
  exact sum_inv_sq_subset_dyadicPrimes_le
    Y (3 * N) (largePrimesInRange Y (3 * N)) hY
    (largePrimesInRange_subset_dyadicPrimes (by omega))

/-- There are at most `3N` primes in the numerical support.
@isnad1 id=le.0h2v.s5.16474b114509 from=translated src=- shape=269940ff vocab=43c5679a
-/
theorem card_largePrimesInRange_le
    (N Y : ℕ) :
    (largePrimesInRange Y (3 * N)).card ≤ 3 * N := by
  have hsubset :
      largePrimesInRange Y (3 * N) ⊆
        Finset.Icc 1 (3 * N) := by
    intro p hp
    have hpData := mem_largePrimesInRange.mp hp
    exact Finset.mem_Icc.mpr
      ⟨hpData.1.two_le.trans' (by norm_num), hpData.2.2⟩
  calc
    (largePrimesInRange Y (3 * N)).card ≤
        (Finset.Icc 1 (3 * N)).card :=
      Finset.card_le_card hsubset
    _ ≤ 3 * N := by
      simp [Nat.card_Icc]

/-- Elementary first reciprocal sum, sufficient for a finite `o(N²)` route.
@isnad1 id=le.1h2v.s6.51152b893a8d from=translated src=- shape=6506003f vocab=29d15a19
-/
theorem sum_inv_largePrimesInRange_le
    {N Y : ℕ} (hY : 1 ≤ Y) :
    (∑ p ∈ largePrimesInRange Y (3 * N),
        1 / (p : ℚ)) ≤
      3 * (N : ℚ) / (Y : ℚ) := by
  have hYpos : (0 : ℚ) < (Y : ℚ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hY)
  have hterm :
      ∀ p ∈ largePrimesInRange Y (3 * N),
        1 / (p : ℚ) ≤ 1 / (Y : ℚ) := by
    intro p hp
    apply one_div_le_one_div_of_le hYpos
    exact_mod_cast
      (mem_largePrimesInRange.mp hp).2.1.le
  calc
    (∑ p ∈ largePrimesInRange Y (3 * N),
        1 / (p : ℚ)) ≤
        ∑ _p ∈ largePrimesInRange Y (3 * N),
          1 / (Y : ℚ) :=
      Finset.sum_le_sum hterm
    _ =
        ((largePrimesInRange Y (3 * N)).card : ℚ) /
          (Y : ℚ) := by
      simp [div_eq_mul_inv]
    _ ≤ (3 * N : ℕ) / (Y : ℚ) := by
      apply div_le_div_of_nonneg_right
      · exact_mod_cast card_largePrimesInRange_le N Y
      · exact hYpos.le
    _ = 3 * (N : ℚ) / (Y : ℚ) := by
      push_cast
      ring

/-- Expand the square before applying the three separate prime estimates.
@isnad1 id=eq.0h2v.s7.1621d96f9147 from=translated src=- shape=3879b30b vocab=569c7fd7
-/
theorem sum_div_add_one_sq_eq
    (N Y : ℕ) :
    (∑ p ∈ largePrimesInRange Y (3 * N),
        ((N : ℚ) / (p : ℚ) + 1) ^ 2) =
      (N : ℚ) ^ 2 *
          (∑ p ∈ largePrimesInRange Y (3 * N),
            1 / (p : ℚ) ^ 2) +
        2 * (N : ℚ) *
          (∑ p ∈ largePrimesInRange Y (3 * N),
            1 / (p : ℚ)) +
        (largePrimesInRange Y (3 * N)).card := by
  rw [Finset.mul_sum, Finset.mul_sum]
  rw [Finset.card_eq_sum_ones]
  push_cast
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  ring

/--
Explicit finite prime-sum envelope.  This is a slightly coarser, completely
certified variant of the analytic estimate used in Lemma 13.6.
@isnad1 id=le.1h2v.s7.b3c17bb8fb20 from=translated src=- shape=4db418d0 vocab=8f11bc3b
-/
theorem sum_div_add_one_sq_le
    {N Y : ℕ} (hY : 4 ≤ Y) :
    (∑ p ∈ largePrimesInRange Y (3 * N),
        ((N : ℚ) / (p : ℚ) + 1) ^ 2) ≤
      28 * (N : ℚ) ^ 2 /
          ((Y : ℚ) * (Nat.log 2 Y : ℚ)) +
        6 * (N : ℚ) ^ 2 / (Y : ℚ) +
        3 * (N : ℚ) := by
  have hsquare := sum_inv_sq_largePrimesInRange_le (N := N) hY
  have hfirst :=
    sum_inv_largePrimesInRange_le (N := N) (show 1 ≤ Y by omega)
  have hcardQ :
      ((largePrimesInRange Y (3 * N)).card : ℚ) ≤
        3 * (N : ℚ) := by
    exact_mod_cast card_largePrimesInRange_le N Y
  rw [sum_div_add_one_sq_eq]
  calc
    (N : ℚ) ^ 2 *
          (∑ p ∈ largePrimesInRange Y (3 * N),
            1 / (p : ℚ) ^ 2) +
        2 * (N : ℚ) *
          (∑ p ∈ largePrimesInRange Y (3 * N),
            1 / (p : ℚ)) +
        (largePrimesInRange Y (3 * N)).card ≤
      (N : ℚ) ^ 2 *
          (28 / ((Y : ℚ) * (Nat.log 2 Y : ℚ))) +
        2 * (N : ℚ) *
          (3 * (N : ℚ) / (Y : ℚ)) +
        3 * (N : ℚ) := by
      gcongr
    _ =
      28 * (N : ℚ) ^ 2 /
          ((Y : ℚ) * (Nat.log 2 Y : ℚ)) +
        6 * (N : ℚ) ^ 2 / (Y : ℚ) +
        3 * (N : ℚ) := by
      ring

/--
Finite analytic dependency-edge bound obtained by composing the exact graph
cover with the reciprocal-prime estimates.
@isnad1 id=le.4h3v.s7.7e1d952e4750 from=translated src=- shape=1612497f vocab=8b537a94
-/
theorem card_orderedDependencyEdges_cast_le
    {N L Y : ℕ}
    (hN : 2 ≤ N) (hLN : L ≤ N)
    (hLY : L ≤ Y) (hY : 4 ≤ Y) :
    ((orderedDependencyEdges N L Y).card : ℚ) ≤
      (L + 1 : ℚ) ^ 2 *
        (28 * (N : ℚ) ^ 2 /
            ((Y : ℚ) * (Nat.log 2 Y : ℚ)) +
          6 * (N : ℚ) ^ 2 / (Y : ℚ) +
          3 * (N : ℚ)) := by
  exact
    (card_orderedDependencyEdges_cast_le_prime_sum
      hN hLN hLY).trans
      (mul_le_mul_of_nonneg_left
        (sum_div_add_one_sq_le hY)
        (sq_nonneg (L + 1 : ℚ)))

end DependencyEdgeBound
end PaperC
