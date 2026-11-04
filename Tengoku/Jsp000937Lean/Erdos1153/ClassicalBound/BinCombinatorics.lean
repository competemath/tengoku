import Tengoku.Jsp000937Lean.Erdos1153.ClassicalBound.EnergyBins

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite combinatorics for a bin decomposition

This file contains the two finite estimates needed after a geometric
partition into K bins.

First, a collection of at most K sparse bins, each carrying at most
n / K^2 points in the real-valued sense, carries total mass at most
n / K.  The formulation uses casts to the reals and therefore makes no
false assertion about natural-number floors.

Second, Engel's form of Cauchy--Schwarz combines bin masses with positive
local scales:

    sum_s a_s m_s^2 / h_s
      >= (sum_s m_s)^2 / sum_s (h_s / a_s).

No geometric construction of the bins or asymptotic choice of K occurs
here.
-/

namespace Erdos1153
namespace ClassicalBound

noncomputable section

/-- Any selected family of bins has cardinality at most the total number
of bins.
@isnad1 id=le.0h2v.s3.a6cc413f02ab from=translated src=- shape=df17f8d0 vocab=c788f210
-/
lemma card_finset_fin_le (K : ℕ) (bins : Finset (Fin K)) :
    bins.card ≤ K := by
  simpa using Finset.card_le_card (Finset.subset_univ bins)

/-- Real-valued sparse-bin mass estimate.

The non-strict pointwise hypothesis is intentionally the weakest useful
one.  A strict sparse threshold immediately implies it.
@isnad1 id=le.2h4v.s6.a6ac284796fc from=translated src=- shape=fcc3fe01 vocab=6f58d943
-/
theorem sum_sparseCounts_le_div {K n : ℕ} (hK : 0 < K)
    (count : Fin K → ℕ) (sparse : Finset (Fin K))
    (hsparse : ∀ s ∈ sparse,
      (count s : ℝ) ≤ (n : ℝ) / (K : ℝ) ^ 2) :
    (∑ s ∈ sparse, (count s : ℝ)) ≤ (n : ℝ) / (K : ℝ) := by
  have hthreshold : 0 ≤ (n : ℝ) / (K : ℝ) ^ 2 := by positivity
  calc
    (∑ s ∈ sparse, (count s : ℝ)) ≤
        ∑ _s ∈ sparse, (n : ℝ) / (K : ℝ) ^ 2 := by
      exact Finset.sum_le_sum hsparse
    _ = (sparse.card : ℝ) * ((n : ℝ) / (K : ℝ) ^ 2) := by
      simp
    _ ≤ (K : ℝ) * ((n : ℝ) / (K : ℝ) ^ 2) := by
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast card_finset_fin_le K sparse) hthreshold
    _ = (n : ℝ) / (K : ℝ) := by
      have hK0 : (K : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hK)
      field_simp

/-- Strict sparse thresholds imply the non-strict total-mass estimate.
@isnad1 id=le.2h4v.s6.a8bb22ddf134 from=translated src=- shape=00ad0e3a vocab=6f58d943
-/
theorem sum_strictSparseCounts_le_div {K n : ℕ} (hK : 0 < K)
    (count : Fin K → ℕ) (sparse : Finset (Fin K))
    (hsparse : ∀ s ∈ sparse,
      (count s : ℝ) < (n : ℝ) / (K : ℝ) ^ 2) :
    (∑ s ∈ sparse, (count s : ℝ)) ≤ (n : ℝ) / (K : ℝ) :=
  sum_sparseCounts_le_div hK count sparse
    (fun s hs ↦ (hsparse s hs).le)

/-- The real sum of all natural bin counts is the cast of their prescribed
natural total.
@isnad1 id=eq.1h3v.s5.cb255873d345 from=translated src=- shape=a6d1db3f vocab=beac3b7a
-/
lemma sum_count_cast_eq {K n : ℕ} (count : Fin K → ℕ)
    (hsum : ∑ s : Fin K, count s = n) :
    (∑ s : Fin K, (count s : ℝ)) = (n : ℝ) := by
  exact_mod_cast hsum

/-- Complementary dense bins retain at least n - n/K real mass.
@isnad1 id=le.3h4v.s7.6ebf0c0e35c0 from=translated src=- shape=3c845f5a vocab=4dc45af2
-/
theorem sub_div_le_sum_denseCounts {K n : ℕ} (hK : 0 < K)
    (count : Fin K → ℕ) (hsum : ∑ s : Fin K, count s = n)
    (sparse : Finset (Fin K))
    (hsparse : ∀ s ∈ sparse,
      (count s : ℝ) ≤ (n : ℝ) / (K : ℝ) ^ 2) :
    (n : ℝ) - (n : ℝ) / (K : ℝ) ≤
      ∑ s ∈ (Finset.univ \ sparse), (count s : ℝ) := by
  have hsparseMass :=
    sum_sparseCounts_le_div hK count sparse hsparse
  have hpartition :
      (∑ s ∈ sparse, (count s : ℝ)) +
        ∑ s ∈ (Finset.univ \ sparse), (count s : ℝ) =
          ∑ s : Fin K, (count s : ℝ) := by
    rw [add_comm]
    exact Finset.sum_sdiff (Finset.subset_univ sparse)
  rw [sum_count_cast_eq count hsum] at hpartition
  linarith

/-- Strict sparse thresholds give the same complementary dense-mass
bound.
@isnad1 id=le.3h4v.s7.1334c463d849 from=translated src=- shape=771a933c vocab=4dc45af2
-/
theorem sub_div_le_sum_denseCounts_of_strict {K n : ℕ} (hK : 0 < K)
    (count : Fin K → ℕ) (hsum : ∑ s : Fin K, count s = n)
    (sparse : Finset (Fin K))
    (hsparse : ∀ s ∈ sparse,
      (count s : ℝ) < (n : ℝ) / (K : ℝ) ^ 2) :
    (n : ℝ) - (n : ℝ) / (K : ℝ) ≤
      ∑ s ∈ (Finset.univ \ sparse), (count s : ℝ) :=
  sub_div_le_sum_denseCounts hK count hsum sparse
    (fun s hs ↦ (hsparse s hs).le)

/-- Weighted Engel/Cauchy inequality on an arbitrary finite index set.

Both weights are assumed strictly positive so every denominator appearing
in the conclusion and in the Engel reduction is honest.
@isnad1 id=le.2h5v.s7.fdfd680f5ddf from=translated src=- shape=445b7cfe vocab=02999aa4
-/
theorem sq_sum_div_sum_div_le_sum_mul_sq_div
    {ι : Type*} [DecidableEq ι] (bins : Finset ι)
    (mass a h : ι → ℝ)
    (ha : ∀ s ∈ bins, 0 < a s) (hh : ∀ s ∈ bins, 0 < h s) :
    ((∑ s ∈ bins, mass s) ^ 2) /
        (∑ s ∈ bins, h s / a s) ≤
      ∑ s ∈ bins, a s * (mass s) ^ 2 / h s := by
  have hengel := Finset.sq_sum_div_le_sum_sq_div bins mass
    (g := fun s ↦ h s / a s)
    (fun s hs ↦ div_pos (hh s hs) (ha s hs))
  calc
    ((∑ s ∈ bins, mass s) ^ 2) /
        (∑ s ∈ bins, h s / a s) ≤
        ∑ s ∈ bins, (mass s) ^ 2 / (h s / a s) := hengel
    _ = ∑ s ∈ bins, a s * (mass s) ^ 2 / h s := by
      apply Finset.sum_congr rfl
      intro s hs
      have ha0 : a s ≠ 0 := (ha s hs).ne'
      have hh0 : h s ≠ 0 := (hh s hs).ne'
      field_simp

/-- Natural-count specialization of the weighted Engel inequality.
@isnad1 id=le.2h5v.s7.9c9b6eea4420 from=translated src=- shape=df79797e vocab=a00afb4f
-/
theorem sq_sum_natCount_div_sum_div_le_sum_mul_sq_div
    {ι : Type*} [DecidableEq ι] (bins : Finset ι)
    (count : ι → ℕ) (a h : ι → ℝ)
    (ha : ∀ s ∈ bins, 0 < a s) (hh : ∀ s ∈ bins, 0 < h s) :
    ((∑ s ∈ bins, (count s : ℝ)) ^ 2) /
        (∑ s ∈ bins, h s / a s) ≤
      ∑ s ∈ bins, a s * (count s : ℝ) ^ 2 / h s :=
  sq_sum_div_sum_div_le_sum_mul_sq_div bins
    (fun s ↦ (count s : ℝ)) a h ha hh

/-- The form used when all K bins participate and their natural counts sum
to n.
@isnad1 id=le.3h5v.s7.b1994c7fff78 from=translated src=- shape=f5f6b568 vocab=061efeff
-/
theorem sq_total_div_sum_div_le_sum_mul_countSq_div
    {K n : ℕ} (count : Fin K → ℕ)
    (hsum : ∑ s : Fin K, count s = n) (a h : Fin K → ℝ)
    (ha : ∀ s, 0 < a s) (hh : ∀ s, 0 < h s) :
    (n : ℝ) ^ 2 / (∑ s : Fin K, h s / a s) ≤
      ∑ s : Fin K, a s * (count s : ℝ) ^ 2 / h s := by
  have hengel :=
    sq_sum_natCount_div_sum_div_le_sum_mul_sq_div
      (Finset.univ : Finset (Fin K)) count a h
      (fun s _ ↦ ha s) (fun s _ ↦ hh s)
  simpa only [sum_count_cast_eq count hsum] using hengel

end

end ClassicalBound
end Erdos1153
