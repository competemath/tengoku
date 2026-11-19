/-
The uniform arithmetic discrepancy, retaining the full (H*y)^J bound.
New proof source: not compiled in the assistant environment.
The actual CRT counting estimate is imported as a theorem, not assumed as a premise.
-/
import Tengoku.Erdos647.Erdos647Sieve.SubsetCountError
import Tengoku.Erdos647.Erdos647Sieve.RetainedSubsets

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false
open scoped BigOperators

noncomputable section
namespace Erdos647Sieve
open Bonferroni

private theorem nonnegative_pow_le_one (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (q : ℕ) : t ^ q ≤ 1 := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [pow_succ]
    exact (mul_le_mul ih ht1 ht0 (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (by ring)

/-- Every retained weighted error is at most H^J.
@isnad1 id=le.4h7v.s7.c5464a61ddc0 from=translated src=- shape=114d5b9a vocab=b67fefef
-/
theorem retained_weighted_subset_error_le
    (A : ℤ) (X H : ℕ) (y z : ℝ) (J : ℕ)
    (hH : 1 ≤ H) (hz0 : 0 < z) (hz1 : z < 1)
    (S : Finset ℕ) (hS : S ∈ retainedSubsets (selectedPrimes H y) J) :
    |(-(1 - z)) ^ S.card *
      ((subsetHitCount (Finset.Icc (A + 1) (A + (X : ℤ))) H S : ℝ) -
        (X : ℝ) * ((H : ℝ) ^ S.card / (primeSubsetProduct S : ℝ)))| ≤
      (H : ℝ) ^ J := by
  obtain ⟨hSP, hcard⟩ := (mem_retainedSubsets _ S J).mp hS
  have ht0 : 0 ≤ 1 - z := by linarith
  have ht1 : 1 - z ≤ 1 := by linarith
  have hpow0 : 0 ≤ (1 - z) ^ S.card := pow_nonneg ht0 _
  have hpow1 := nonnegative_pow_le_one (1 - z) ht0 ht1 S.card
  have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hH
  rw [abs_mul, abs_pow, abs_neg, abs_of_nonneg ht0]
  calc
    _ ≤ (1 - z) ^ S.card * (H : ℝ) ^ S.card :=
      mul_le_mul_of_nonneg_left (selected_subsetHitCount_error_le A X H y S hSP) hpow0
    _ ≤ 1 * (H : ℝ) ^ S.card :=
      mul_le_mul_of_nonneg_right hpow1 (pow_nonneg (Nat.cast_nonneg H) _)
    _ ≤ (H : ℝ) ^ J := by
      rw [one_mul]
      exact real_pow_mono_of_one_le (H : ℝ) hHr _ _ hcard

/-- The complete signed discrepancy for every truncation degree, even or odd.
Evenness is required later by Bonferroni, not by this absolute-error theorem.
@isnad1 id=le.4h6v.s7.2803f4bcdd3a from=translated src=- shape=9c747d08 vocab=f776dd86
-/
theorem arithmetic_discrepancy_le
    (A : ℤ) (X H : ℕ) (y z : ℝ) (J : ℕ)
    (hH : 1 ≤ H) (hy : (H : ℝ) < y) (hz0 : 0 < z) (hz1 : z < 1) :
    |∑ j ∈ Finset.range (J + 1), (-1 : ℝ) ^ j *
      ((∑ n ∈ Finset.Icc (A + 1) (A + (X : ℤ)),
          elementary (hitWeights H y z n) j) -
        (X : ℝ) * elementary (meanWeights H y z) j)| ≤ ((H : ℝ) * y) ^ J := by
  classical
  let I : Finset ℤ := Finset.Icc (A + 1) (A + (X : ℤ))
  let P : Finset ℕ := selectedPrimes H y
  let f : Finset ℕ → ℝ := fun S => (-(1 - z)) ^ S.card *
    ((subsetHitCount I H S : ℝ) -
      (X : ℝ) * ((H : ℝ) ^ S.card / (primeSubsetProduct S : ℝ)))
  have hflatten :
      (∑ j ∈ Finset.range (J + 1), (-(1 - z)) ^ j *
        (∑ S ∈ P.powersetCard j, ((subsetHitCount I H S : ℝ) -
          (X : ℝ) * ((H : ℝ) ^ j / (primeSubsetProduct S : ℝ))))) =
        ∑ S ∈ retainedSubsets P J, f S := by
    calc
      _ = ∑ j ∈ Finset.range (J + 1), ∑ S ∈ P.powersetCard j, f S := by
        apply Finset.sum_congr rfl
        intro j _hj
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro S hS
        simp only [f, (Finset.mem_powersetCard.mp hS).2]
      _ = _ := sum_powersetCard_le_eq_retained P J f
  change |∑ j ∈ Finset.range (J + 1), (-1 : ℝ) ^ j *
    ((∑ n ∈ I, elementary (hitWeights H y z n) j) -
      (X : ℝ) * elementary (meanWeights H y z) j)| ≤ ((H : ℝ) * y) ^ J
  rw [signed_discrepancy_eq_subset_errors I X H y z J]
  change |∑ j ∈ Finset.range (J + 1), (-(1 - z)) ^ j *
    (∑ S ∈ P.powersetCard j, ((subsetHitCount I H S : ℝ) -
      (X : ℝ) * ((H : ℝ) ^ j / (primeSubsetProduct S : ℝ))))| ≤ ((H : ℝ) * y) ^ J
  rw [hflatten]
  calc
    _ ≤ ∑ S ∈ retainedSubsets P J, |f S| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _S ∈ retainedSubsets P J, (H : ℝ) ^ J := by
      apply Finset.sum_le_sum
      intro S hS
      exact retained_weighted_subset_error_le A X H y z J hH hz0 hz1 S hS
    _ = ((retainedSubsets P J).card : ℝ) * (H : ℝ) ^ J := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ y ^ J * (H : ℝ) ^ J :=
      mul_le_mul_of_nonneg_right (card_retainedSubsets_cast_le H y J hH hy)
        (pow_nonneg (Nat.cast_nonneg H) J)
    _ = ((H : ℝ) * y) ^ J := by rw [mul_pow]; ring

end Erdos647Sieve
end
