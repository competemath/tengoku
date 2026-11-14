import Tengoku.Twinprime.TwinPrime.Analytic.Dispersion
import Tengoku.Twinprime.TwinPrime.Analytic.DyadicNatPartition

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exact dyadic partition of the signed bilinear correlation

The dispersion boxes use `(2^i,2^(i+1)]`. Applying the existing left-closed
dyadic cover to `n-1` assigns every integer `n>1` to exactly one such box.
The assumptions `1≤U,V` exclude the factors equal to one. The true cutoff
conditions and the full signed coefficient remain in every selected box.
-/

noncomputable section

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace TwinPrime.Analytic

/-- Possible dispersion boxes, including a harmless boundary of empty boxes.-/
def dispersionBoxIndices (U V X : ℕ) : Finset (ℕ × ℕ) :=
  ((range (dyadicNatDepth (2 * X))).product (range (dyadicNatDepth (2 * X)))).filter
    (fun ij => U ≤ 2 * 2 ^ ij.1 ∧ V ≤ 2 * 2 ^ ij.2 ∧
      2 ^ ij.1 * 2 ^ ij.2 ≤ 2 * X)

theorem mem_dispersionBoxIndices_iff (U V X : ℕ) (ij : ℕ × ℕ) :
    ij ∈ dispersionBoxIndices U V X ↔
      ij.1 < dyadicNatDepth (2 * X) ∧ ij.2 < dyadicNatDepth (2 * X) ∧
      U ≤ 2 * 2 ^ ij.1 ∧ V ≤ 2 * 2 ^ ij.2 ∧ 2 ^ ij.1 * 2 ^ ij.2 ≤ 2 * X := by
  simp only [dispersionBoxIndices, mem_filter, product_eq_sprod, mem_product, mem_range]
  tauto

/-- The right-closed cells cover each relevant factor exactly once,
including powers of two at the upper endpoint of a cell.-/
theorem existsUnique_dispersion_dyadic_index (T n : ℕ) (hn : 1 < n) (hnT : n ≤ T) :
    ∃! i : ℕ, i ∈ range (dyadicNatDepth T) ∧ 2 ^ i < n ∧ n ≤ 2 * 2 ^ i := by
  obtain ⟨i, hi, huniq⟩ := existsUnique_dyadicNatCell T (n - 1)
    (mem_Ioc.mpr ⟨by omega, by omega⟩)
  have himem := mem_Ico.mp hi.2
  change 2 ^ i ≤ n - 1 ∧ n - 1 < 2 ^ (i + 1) at himem
  rw [pow_succ, mul_comm _ 2] at himem
  refine ⟨i, ⟨hi.1, by omega, by omega⟩, ?_⟩
  intro j hj
  apply huniq j
  refine ⟨hj.1, ?_⟩
  change n - 1 ∈ Ico (2 ^ j) (2 ^ (j + 1))
  rw [pow_succ, mul_comm _ 2]
  exact mem_Ico.mpr ⟨by omega, by omega⟩

theorem dispersionBoxIndices_card_le (U V X : ℕ) :
    (dispersionBoxIndices U V X).card ≤ (dyadicNatDepth (2 * X)) ^ 2 := by
  apply (card_filter_le _ _).trans_eq
  simp only [product_eq_sprod, card_product, card_range, pow_two]

/-- Natural side lengths and the true product/cutoff/depth bounds used by
the dispersion estimates on each selected box.-/
theorem dispersionBoxIndices_bounds {U V X : ℕ} {ij : ℕ × ℕ}
    (hij : ij ∈ dispersionBoxIndices U V X) :
    1 ≤ 2 ^ ij.1 ∧ 1 ≤ 2 ^ ij.2 ∧ U ≤ 2 * 2 ^ ij.1 ∧ V ≤ 2 * 2 ^ ij.2 ∧
      2 ^ ij.1 * 2 ^ ij.2 ≤ 2 * X ∧
      ij.1 + 1 ≤ dyadicNatDepth (2 * X) ∧ ij.2 + 1 ≤ dyadicNatDepth (2 * X) := by
  obtain ⟨hi, hj, hU, hV, hprod⟩ := (mem_dispersionBoxIndices_iff U V X ij).mp hij
  exact ⟨Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide)),
    Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide)),
    hU, hV, hprod, hi, hj⟩

/-- Every actual bilinear factor pair belongs to a unique selected box.
The boxes retain the complete signed factor sum, not an absolute majorant.-/
theorem existsUnique_dispersionBox_of_bilinearPairs {U V X : ℕ}
    (hU : 1 ≤ U) (hV : 1 ≤ V) (dr : ℕ × ℕ) (hdr : dr ∈ bilinearPairs U V X) :
    ∃! ij : ℕ × ℕ, ij ∈ dispersionBoxIndices U V X ∧
      2 ^ ij.1 < dr.1 ∧ dr.1 ≤ 2 * 2 ^ ij.1 ∧
      2 ^ ij.2 < dr.2 ∧ dr.2 ≤ 2 * 2 ^ ij.2 := by
  obtain ⟨hpair, hUd, hVr, _, hprod⟩ := mem_filter.mp hdr
  obtain ⟨hd, hr⟩ := mem_product.mp hpair
  obtain ⟨i, hi, huniqI⟩ := existsUnique_dispersion_dyadic_index (2 * X) dr.1
    (by omega) (mem_Icc.mp hd).2
  obtain ⟨j, hj, huniqJ⟩ := existsUnique_dispersion_dyadic_index (2 * X) dr.2
    (by omega) (mem_Icc.mp hr).2
  have hbox : (i, j) ∈ dispersionBoxIndices U V X := by
    apply (mem_dispersionBoxIndices_iff U V X (i, j)).mpr
    dsimp only
    refine ⟨mem_range.mp hi.1, mem_range.mp hj.1, by omega, by omega, ?_⟩
    exact (Nat.mul_le_mul (Nat.le_of_lt hi.2.1) (Nat.le_of_lt hj.2.1)).trans hprod
  refine ⟨(i, j), ⟨hbox, hi.2.1, hi.2.2, hj.2.1, hj.2.2⟩, ?_⟩
  rintro ⟨k, l⟩ ⟨hkl, hkd, hdk, hlr, hrl⟩
  have hmem := (mem_dispersionBoxIndices_iff U V X (k, l)).mp hkl
  have hk : k = i := huniqI k ⟨mem_range.mpr hmem.1, hkd, hdk⟩
  have hl : l = j := huniqJ l ⟨mem_range.mpr hmem.2.1, hlr, hrl⟩
  simp only [hk, hl]

/-- Exact global decomposition into the existing right-closed dispersion
boxes. Factors one vanish under the stated positive cutoffs.-/
theorem bilinearTerm_eq_sum_dispersionBoxes (U V X : ℕ) (hU : 1 ≤ U) (hV : 1 ≤ V) :
    bilinearTerm U V X =
      ∑ ij ∈ dispersionBoxIndices U V X, bilinearBox U V X (2 ^ ij.1) (2 ^ ij.2) := by
  rw [bilinearTerm_eq_pair_sum]
  simp_rw [bilinearBox_eq_filtered_pair_sum, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro dr hdr
  obtain ⟨ij, hij, huniq⟩ := existsUnique_dispersionBox_of_bilinearPairs hU hV dr hdr
  symm
  rw [sum_eq_single ij]
  · simp only [ite_eq_left hij.2]
  · intro kl hkl hne
    apply ite_eq_right
    intro hcell
    exact hne (huniq kl ⟨hkl, hcell⟩)
  · exact fun hnot => False.elim (hnot hij.1)

end TwinPrime.Analytic
