/-
Exact coefficient-to-count identities for both sieve weight lists.
New implementation source; not compiled in the assistant environment.
Counts below are actual simultaneous divisibility counts, not expected values.
All finite integer intervals, negative translations, and polynomial zeros are allowed.
-/
import Tengoku.Erdos647.Erdos647Sieve.PrimeSubsetCoefficients
import Tengoku.Erdos647.Erdos647Sieve.PrimeSubsetProducts
import Tengoku.Erdos647.Erdos647Sieve.SieveWeights

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false
open scoped BigOperators

noncomputable section
namespace Erdos647Sieve
open Bonferroni

/-- Actual count of simultaneous prime hits in an arbitrary finite integer set.-/
def subsetHitCount (I : Finset ℤ) (H : ℕ) (S : Finset ℕ) : ℕ := by
  classical
  exact (I.filter (fun n : ℤ => ∀ p ∈ S, (p : ℤ) ∣ windowPolynomial H n)).card

/-- The empty subset imposes no congruence restriction.
@isnad1 id=eq.0h2v.s4.cc3df7981f18 from=translated src=- shape=78f48b55 vocab=c6695184
-/
theorem subsetHitCount_empty (I : Finset ℤ) (H : ℕ) :
    subsetHitCount I H ∅ = I.card := by
  classical
  simp [subsetHitCount]

/-- Conjunction form and product-modulus form agree for distinct prime bases.
@isnad1 id=eq.1h3v.s5.74d6e09d1b2c from=translated src=- shape=8a634ce2 vocab=05cf1aef
-/
theorem subsetHitCount_eq_modulus_count (I : Finset ℤ) (H : ℕ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) :
    subsetHitCount I H S =
      (I.filter (fun n : ℤ => (primeSubsetProduct S : ℤ) ∣ windowPolynomial H n)).card := by
  classical
  unfold subsetHitCount
  apply congrArg Finset.card
  apply Finset.ext
  intro n
  simp only [Finset.mem_filter, primeSubsetProduct_int_dvd_iff S hS]

/-- A product of t-or-zero weights detects the conjunction, including the empty set.
@isnad1 id=eq.0h3v.s6.39f26206516e from=translated src=- shape=10180b1d vocab=86b6d1f3
-/
theorem prod_ite_zero_eq_pow_card (S : Finset ℕ) (P : ℕ → Prop)
    [DecidablePred P] (t : ℝ) :
    (∏ p ∈ S, if P p then t else 0) =
      if (∀ p ∈ S, P p) then t ^ S.card else 0 := by
  by_cases hall : ∀ p ∈ S, P p
  · rw [ite_eq_left hall]
    calc
      (∏ p ∈ S, if P p then t else 0) = ∏ _p ∈ S, t := by
        apply Finset.prod_congr rfl
        intro p hp
        exact ite_eq_left (hall p hp)
      _ = t ^ S.card := Finset.prod_const t
  · rw [ite_eq_right hall]
    push Not at hall
    obtain ⟨p, hp, hnot⟩ := hall
    exact Finset.prod_eq_zero hp (by simp only [ite_eq_right hnot])

/-- Pointwise coefficient as an explicit sum of simultaneous-hit indicators.
@isnad1 id=eq.0h5v.s7.3cc1d3bc1d38 from=translated src=- shape=1413e8f6 vocab=2ebea454
-/
theorem hitWeights_elementary_eq_subset_sum (H : ℕ) (y z : ℝ) (n : ℤ) (q : ℕ) :
    elementary (hitWeights H y z n) q =
      (1 - z) ^ q *
        (∑ S ∈ (selectedPrimes H y).powersetCard q,
          if (∀ p ∈ S, (p : ℤ) ∣ windowPolynomial H n) then (1 : ℝ) else 0) := by
  classical
  unfold hitWeights
  rw [elementary_toList_eq_sum_powersetCard, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  rw [prod_ite_zero_eq_pow_card, (Finset.mem_powersetCard.mp hS).2]
  split_ifs <;> ring

/-- Summing the pointwise coefficient counts actual simultaneous congruences.
No upper estimate or stochastic independence assumption enters this identity.
@isnad1 id=eq.0h5v.s6.3418677b17fa from=translated src=- shape=33dd3e25 vocab=0dddd649
-/
theorem sum_hitWeights_elementary_eq_subset_counts
    (I : Finset ℤ) (H : ℕ) (y z : ℝ) (q : ℕ) :
    (∑ n ∈ I, elementary (hitWeights H y z n) q) =
      (1 - z) ^ q * (∑ S ∈ (selectedPrimes H y).powersetCard q,
        (subsetHitCount I H S : ℝ)) := by
  classical
  simp_rw [hitWeights_elementary_eq_subset_sum]
  rw [← Finset.mul_sum, Finset.sum_comm]
  apply congrArg (fun u : ℝ => (1 - z) ^ q * u)
  apply Finset.sum_congr rfl
  intro S _hS
  simp only [subsetHitCount, ← Finset.sum_filter, Finset.sum_const,
    nsmul_eq_mul, mul_one]

/-- Exact translated-interval version, including X=0 and every A in Z.
@isnad1 id=eq.0h6v.s7.e07f9d34e797 from=translated src=- shape=96408594 vocab=f978ad86
-/
theorem interval_hitWeights_elementary_eq_subset_counts
    (A : ℤ) (X H : ℕ) (y z : ℝ) (q : ℕ) :
    (∑ n ∈ Finset.Icc (A + 1) (A + (X : ℤ)),
        elementary (hitWeights H y z n) q) =
      (1 - z) ^ q * (∑ S ∈ (selectedPrimes H y).powersetCard q,
        (subsetHitCount (Finset.Icc (A + 1) (A + (X : ℤ))) H S : ℝ)) :=
  sum_hitWeights_elementary_eq_subset_counts _ H y z q

/-- Exact mean-coefficient formula. Products are over indices, not weight values.
@isnad1 id=eq.0h4v.s6.6021e282ac5c from=translated src=- shape=1286f4f0 vocab=d69866c3
-/
theorem meanWeights_elementary_eq_subset_sum (H : ℕ) (y z : ℝ) (q : ℕ) :
    elementary (meanWeights H y z) q =
      (1 - z) ^ q * (∑ S ∈ (selectedPrimes H y).powersetCard q,
        ((H : ℝ) ^ q / (primeSubsetProduct S : ℝ))) := by
  classical
  unfold meanWeights
  rw [elementary_toList_eq_sum_powersetCard, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  have hcard : S.card = q := (Finset.mem_powersetCard.mp hS).2
  have hprod : (primeSubsetProduct S : ℝ) = ∏ p ∈ S, (p : ℝ) := by
    simp only [primeSubsetProduct, Nat.cast_prod]
  rw [Finset.prod_div_distrib, Finset.prod_const, ← hprod, hcard, mul_pow]
  ring

/-- Exact discrepancy of one coefficient, with every scale factor retained.
This is an identity; it does not bound the actual counts by their CRT main terms.
@isnad1 id=eq.0h6v.s7.0a4bffb508ff from=translated src=- shape=d7bd8823 vocab=94cf5a0c
-/
theorem coefficient_discrepancy_eq_subset_errors
    (I : Finset ℤ) (X H : ℕ) (y z : ℝ) (q : ℕ) :
    (∑ n ∈ I, elementary (hitWeights H y z n) q) -
        (X : ℝ) * elementary (meanWeights H y z) q =
      (1 - z) ^ q * (∑ S ∈ (selectedPrimes H y).powersetCard q,
        ((subsetHitCount I H S : ℝ) -
          (X : ℝ) * ((H : ℝ) ^ q / (primeSubsetProduct S : ℝ)))) := by
  rw [sum_hitWeights_elementary_eq_subset_counts, meanWeights_elementary_eq_subset_sum]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- Exact signed discrepancy before taking absolute errors.
No evenness, positive translation, or distribution hypothesis is required.
@isnad1 id=eq.0h6v.s7.c19d0e0db9b4 from=translated src=- shape=22170277 vocab=72a57bff
-/
theorem signed_discrepancy_eq_subset_errors
    (I : Finset ℤ) (X H : ℕ) (y z : ℝ) (J : ℕ) :
    (∑ j ∈ Finset.range (J + 1), (-1 : ℝ) ^ j *
      ((∑ n ∈ I, elementary (hitWeights H y z n) j) -
        (X : ℝ) * elementary (meanWeights H y z) j)) =
    ∑ j ∈ Finset.range (J + 1), (-(1 - z)) ^ j *
      (∑ S ∈ (selectedPrimes H y).powersetCard j,
        ((subsetHitCount I H S : ℝ) -
          (X : ℝ) * ((H : ℝ) ^ j / (primeSubsetProduct S : ℝ)))) := by
  apply Finset.sum_congr rfl
  intro j _hj
  rw [coefficient_discrepancy_eq_subset_errors]
  rw [show -(1 - z) = (-1 : ℝ) * (1 - z) by ring, mul_pow]
  ring

end Erdos647Sieve
end
