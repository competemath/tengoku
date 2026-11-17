import Tengoku.PaperCLean.PaperC.Analysis.ReciprocalSqrtSum
import Tengoku.PaperCLean.PaperC.Arithmetic.DefectCounting

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A smooth Euler-product bound

The estimates here deliberately forget primality.  Any finite set of positive
integers bounded by `H` satisfies the same product bound, hence so does the set
of primes at most `H`.
-/

namespace PaperC

open scoped BigOperators

/-- The finite product of `1 + x` is bounded by the exponential of the sum.
@isnad1 id=le.0h1v.s5.7deb2bd7c62e from=translated src=- shape=96a81069 vocab=71e7f54e
-/
theorem prod_one_add_inv_sqrt_le_exp_sum (s : Finset ℕ) :
    (∏ n ∈ s, (1 + (Real.sqrt n)⁻¹)) ≤
      Real.exp (∑ n ∈ s, (Real.sqrt n)⁻¹) := by
  calc
    (∏ n ∈ s, (1 + (Real.sqrt n)⁻¹))
        ≤ ∏ n ∈ s, Real.exp ((Real.sqrt n)⁻¹) := by
          gcongr with n hn
          simpa [add_comm] using Real.add_one_le_exp ((Real.sqrt n)⁻¹)
    _ = Real.exp (∑ n ∈ s, (Real.sqrt n)⁻¹) := by
      rw [Real.exp_sum]

/--
Every finite `s ⊆ {1, …, H}` satisfies

`∏_{n∈s} (1 + n⁻¹/²) ≤ exp (2 √H)`.
@isnad1 id=le.1h2v.s6.faa1d586c4f9 from=translated src=- shape=1553b227 vocab=8290cdd2
-/
theorem prod_one_add_inv_sqrt_le_exp_two_sqrt
    (H : ℕ) (s : Finset ℕ) (hs : s ⊆ Finset.Icc 1 H) :
    (∏ n ∈ s, (1 + (Real.sqrt n)⁻¹)) ≤
      Real.exp (2 * Real.sqrt H) := by
  refine (prod_one_add_inv_sqrt_le_exp_sum s).trans ?_
  apply Real.exp_le_exp.mpr
  exact (Finset.sum_le_sum_of_subset_of_nonneg hs fun n _ _ ↦
    inv_nonneg.mpr (Real.sqrt_nonneg n)).trans (sum_Icc_inv_sqrt_le H)

/-- The preceding bound in the negative-half-power notation used in Paper C.
@isnad1 id=le.1h2v.s6.aa49402cb890 from=translated src=- shape=6085301f vocab=3c59d54d
-/
theorem prod_one_add_rpow_neg_one_half_le_exp_two_sqrt
    (H : ℕ) (s : Finset ℕ) (hs : s ⊆ Finset.Icc 1 H) :
    (∏ n ∈ s, (1 + (n : ℝ) ^ (-(1 / 2 : ℝ)))) ≤
      Real.exp (2 * Real.sqrt H) := by
  simpa only [rpow_neg_one_half_eq_inv_sqrt _ (Nat.cast_nonneg _)] using
    prod_one_add_inv_sqrt_le_exp_two_sqrt H s hs

/-- The existing small-prime finset is contained in the positive interval.
@isnad1 id=le.0h1v.s4.fe85f70c4d6f from=translated src=- shape=73d95e72 vocab=1ab911ff
-/
lemma DefectCounting.smallPrimesUpTo_subset_Icc (H : ℕ) :
    DefectCounting.smallPrimesUpTo H ⊆ Finset.Icc 1 H := by
  intro p hp
  rw [DefectCounting.mem_smallPrimesUpTo] at hp
  exact Finset.mem_Icc.mpr ⟨hp.1.two_le.trans' (by norm_num), hp.2⟩

/--
Prime-specialized Euler-product estimate, requiring no prime number theorem:

`∏_{p≤H, p prime} (1 + p⁻¹/²) ≤ exp (2 √H)`.
@isnad1 id=le.0h1v.s5.7b9417a65cfa from=translated src=- shape=68b35e65 vocab=919cc770
-/
theorem prod_smallPrimesUpTo_one_add_inv_sqrt_le (H : ℕ) :
    (∏ p ∈ DefectCounting.smallPrimesUpTo H, (1 + (Real.sqrt p)⁻¹)) ≤
      Real.exp (2 * Real.sqrt H) :=
  prod_one_add_inv_sqrt_le_exp_two_sqrt H (DefectCounting.smallPrimesUpTo H)
    (DefectCounting.smallPrimesUpTo_subset_Icc H)

/-- Prime-specialized form in negative-half-power notation.
@isnad1 id=le.0h1v.s6.c0fd84e5e643 from=translated src=- shape=611ac974 vocab=9441e84f
-/
theorem prod_smallPrimesUpTo_one_add_rpow_neg_one_half_le (H : ℕ) :
    (∏ p ∈ DefectCounting.smallPrimesUpTo H,
        (1 + (p : ℝ) ^ (-(1 / 2 : ℝ)))) ≤
      Real.exp (2 * Real.sqrt H) := by
  simpa only [rpow_neg_one_half_eq_inv_sqrt _ (Nat.cast_nonneg _)] using
    prod_smallPrimesUpTo_one_add_inv_sqrt_le H

end PaperC
