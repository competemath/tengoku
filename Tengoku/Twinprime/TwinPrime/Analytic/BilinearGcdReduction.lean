import Tengoku.Twinprime.TwinPrime.Analytic.DispersionBilinearGcd
import Tengoku.Twinprime.TwinPrime.Analytic.DispersionPartition
import Tengoku.Twinprime.TwinPrime.Analytic.DispersionGcdCutoff

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Removing the large gcd of the original bilinear factors

These are restrictions of the signed `bilinearPairs` sum by `gcd(d,r)`.
The exact dyadic partition and elementary pair sparsity make the large-gcd
restriction sublinear at the logarithmic cutoff. The remaining small-gcd
sum is retained without a cancellation assertion.
-/

noncomputable section

open Finset Filter ArithmeticFunction
open scoped Topology ArithmeticFunction.Moebius

namespace TwinPrime.Analytic

def bilinearSmallGcd (U V X G : ℕ) : ℝ :=
  ∑ dr ∈ (bilinearPairs U V X).filter (fun dr => Nat.gcd dr.1 dr.2 ≤ G),
    (μ dr.1 : ℝ) * vaughanBeta V dr.2 * vonMangoldt (dr.1 * dr.2 + 2)

def bilinearLargeGcd (U V X G : ℕ) : ℝ :=
  ∑ dr ∈ (bilinearPairs U V X).filter (fun dr => G < Nat.gcd dr.1 dr.2),
    (μ dr.1 : ℝ) * vaughanBeta V dr.2 * vonMangoldt (dr.1 * dr.2 + 2)

theorem bilinearTerm_eq_smallGcd_add_largeGcd (U V X G : ℕ) :
    bilinearTerm U V X = bilinearSmallGcd U V X G + bilinearLargeGcd U V X G := by
  rw [bilinearTerm_eq_pair_sum]
  simp only [bilinearSmallGcd, bilinearLargeGcd, sum_filter, ← sum_add_distrib]
  apply sum_congr rfl
  intro dr _
  by_cases hg : Nat.gcd dr.1 dr.2 ≤ G
  · simp [hg, not_lt.mpr hg]
  · simp [hg, lt_of_not_ge hg]

/-- Every restriction of the original factor domain inherits the unique
right-closed dyadic assignment, without modifying its coefficient.-/
theorem sum_bilinearPairs_filter_eq_sum_boxes {A : Type*} [AddCommMonoid A]
    (U V X : ℕ) (hU : 1 ≤ U) (hV : 1 ≤ V)
    (P : ℕ × ℕ → Prop) [DecidablePred P] (f : ℕ × ℕ → A) :
    (∑ dr ∈ (bilinearPairs U V X).filter P, f dr) =
      ∑ ij ∈ dispersionBoxIndices U V X,
        ∑ dr ∈ (bilinearPairs U V X).filter
            (fun dr => (2 ^ ij.1 < dr.1 ∧ dr.1 ≤ 2 * 2 ^ ij.1 ∧
              2 ^ ij.2 < dr.2 ∧ dr.2 ≤ 2 * 2 ^ ij.2) ∧ P dr), f dr := by
  classical
  simp only [sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro dr hdr
  by_cases hP : P dr
  · simp only [hP, and_true, ite_true]
    obtain ⟨ij, hij, huniq⟩ := existsUnique_dispersionBox_of_bilinearPairs hU hV dr hdr
    symm
    rw [sum_eq_single ij]
    · simp only [ite_eq_left hij.2]
    · intro kl hkl hne
      apply ite_eq_right
      intro hcell
      exact hne (huniq kl ⟨hkl, hcell⟩)
    · exact fun hnot => False.elim (hnot hij.1)
  · simp only [hP, and_false, ite_false, sum_const_zero]

theorem bilinearLargeGcd_eq_sum_boxes (U V X G : ℕ) (hU : 1 ≤ U) (hV : 1 ≤ V) :
    bilinearLargeGcd U V X G = ∑ ij ∈ dispersionBoxIndices U V X,
      bilinearBoxLargeGcd U V X (2 ^ ij.1) (2 ^ ij.2) G := by
  simp_rw [bilinearBoxLargeGcd_eq_filtered_pair_sum]
  exact sum_bilinearPairs_filter_eq_sum_boxes U V X hU hV _ _

theorem bilinearSmallGcd_eq_sum_boxes (U V X G : ℕ) (hU : 1 ≤ U) (hV : 1 ≤ V) :
    bilinearSmallGcd U V X G = ∑ ij ∈ dispersionBoxIndices U V X,
      bilinearBoxSmallGcd U V X (2 ^ ij.1) (2 ^ ij.2) G := by
  simp_rw [bilinearBoxSmallGcd_eq_filtered_pair_sum]
  exact sum_bilinearPairs_filter_eq_sum_boxes U V X hU hV _ _

theorem abs_bilinearLargeGcd_le (U V X G : ℕ)
    (hU : 1 ≤ U) (hV : 1 ≤ V) (hG : 1 ≤ G) :
    |bilinearLargeGcd U V X G| ≤
      (dyadicNatDepth (2 * X) : ℝ) ^ 2 *
        (8 * (X : ℝ) * (Real.log (4 * X + 4)) ^ 2 / G) := by
  rw [bilinearLargeGcd_eq_sum_boxes U V X G hU hV]
  calc
    _ ≤ ∑ ij ∈ dispersionBoxIndices U V X,
        |bilinearBoxLargeGcd U V X (2 ^ ij.1) (2 ^ ij.2) G| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ij ∈ dispersionBoxIndices U V X,
        8 * (X : ℝ) * (Real.log (4 * X + 4)) ^ 2 / G := by
      apply sum_le_sum
      intro ij hij
      have hb := dispersionBoxIndices_bounds hij
      exact abs_bilinearBoxLargeGcd_le U V X _ _ G hb.1 hb.2.1 hG hb.2.2.2.2.1
    _ = (dispersionBoxIndices U V X).card *
        (8 * (X : ℝ) * (Real.log (4 * X + 4)) ^ 2 / G) := by simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast dispersionBoxIndices_card_le U V X

theorem abs_bilinearLargeGcd_div_le (U V X G : ℕ)
    (hU : 1 ≤ U) (hV : 1 ≤ V) (hX : 1 ≤ X) (hG : 1 ≤ G) :
    |bilinearLargeGcd U V X G| / X ≤
      (dyadicNatDepth (2 * X) : ℝ) ^ 2 * 8 * (Real.log (4 * X + 4)) ^ 2 / G := by
  have hx : (0 : ℝ) < X := by exact_mod_cast hX
  calc
    _ ≤ ((dyadicNatDepth (2 * X) : ℝ) ^ 2 *
        (8 * (X : ℝ) * (Real.log (4 * X + 4)) ^ 2 / G)) / X :=
      div_le_div_of_nonneg_right (abs_bilinearLargeGcd_le U V X G hU hV hG) hx.le
    _ = _ := by field_simp

/-- The original-factor large-gcd budget decays by six logarithmic powers.-/
theorem bilinearGcdCutoff_family_error_le (X : ℕ) (hX : 128 ≤ X) :
    (dyadicNatDepth (2 * X) : ℝ) ^ 2 * 8 * (Real.log (4 * X + 4)) ^ 2 /
        dispersionGcdCutoff X ≤
      8 * (2 / Real.log 2) ^ 2 / (Real.log (4 * (X : ℝ) + 4)) ^ 6 := by
  let L : ℝ := Real.log (4 * (X : ℝ) + 4)
  have hL : 0 < L := lt_of_lt_of_le (by norm_num) (one_le_dispersion_log X)
  have hG : (0 : ℝ) < dispersionGcdCutoff X := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (one_le_dispersionGcdCutoff X))
  have hD := dyadicNatDepth_two_mul_le_dispersion_log X hX
  have hDsq := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) (dyadicNatDepth (2 * X))) hD 2
  calc
    _ ≤ ((2 / Real.log 2) * L) ^ 2 * 8 * L ^ 2 / dispersionGcdCutoff X := by
      apply div_le_div_of_nonneg_right _ hG.le
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hDsq (by norm_num)) (sq_nonneg L)
    _ ≤ 8 * (2 / Real.log 2) ^ 2 / L ^ 6 := by
      apply (div_le_iff₀ hG).mpr
      have h := mul_le_mul_of_nonneg_left (log_pow_le_dispersionGcdCutoff X)
        (show 0 ≤ 8 * (2 / Real.log 2) ^ 2 / L ^ 6 by positivity)
      have heq : (8 * (2 / Real.log 2) ^ 2 / L ^ 6) * L ^ 10 =
          ((2 / Real.log 2) * L) ^ 2 * 8 * L ^ 2 := by
        field_simp
      exact heq.symm.trans_le h

theorem abs_bilinearLargeGcd_div_le_log (U V X : ℕ)
    (hU : 1 ≤ U) (hV : 1 ≤ V) (hX : 128 ≤ X) :
    |bilinearLargeGcd U V X (dispersionGcdCutoff X)| / X ≤
      8 * (2 / Real.log 2) ^ 2 / (Real.log (4 * (X : ℝ) + 4)) ^ 6 :=
  (abs_bilinearLargeGcd_div_le U V X _ hU hV (by omega)
    (one_le_dispersionGcdCutoff X)).trans (bilinearGcdCutoff_family_error_le X hX)

theorem tendsto_bilinearGcd_log_error :
    Tendsto (fun X : ℕ => 8 * (2 / Real.log 2) ^ 2 /
      (Real.log (4 * (X : ℝ) + 4)) ^ 6) atTop (𝓝 0) := by
  have harg : Tendsto (fun X : ℕ => 4 * (X : ℝ) + 4) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ tendsto_natCast_atTop_atTop
    filter_upwards with X
    have := Nat.cast_nonneg (α := ℝ) X
    linarith
  have hinv := tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp harg)
  simpa only [Function.comp_def, div_eq_mul_inv, inv_pow, zero_pow (by decide : 6 ≠ 0),
    mul_zero] using (hinv.pow 6).const_mul (8 * (2 / Real.log 2) ^ 2)

def primaryBilinearSmallGcd (X : ℕ) : ℝ :=
  bilinearSmallGcd (primaryCutoff X) (primaryCutoff X) X (dispersionGcdCutoff X)

def primaryBilinearLargeGcd (X : ℕ) : ℝ :=
  bilinearLargeGcd (primaryCutoff X) (primaryCutoff X) X (dispersionGcdCutoff X)

theorem primary_bilinear_eq_smallGcd_add_largeGcd (X : ℕ) :
    bilinearTerm (primaryCutoff X) (primaryCutoff X) X =
      primaryBilinearSmallGcd X + primaryBilinearLargeGcd X :=
  bilinearTerm_eq_smallGcd_add_largeGcd _ _ X _

theorem abs_primaryBilinearLargeGcd_div_le_log (X : ℕ) (hX : 128 ≤ X) :
    |primaryBilinearLargeGcd X| / X ≤
      8 * (2 / Real.log 2) ^ 2 / (Real.log (4 * (X : ℝ) + 4)) ^ 6 :=
  abs_bilinearLargeGcd_div_le_log _ _ X
    (primaryCutoff_pos (by omega)) (primaryCutoff_pos (by omega)) hX

theorem tendsto_abs_primaryBilinearLargeGcd_div :
    Tendsto (fun X : ℕ => |primaryBilinearLargeGcd X| / X) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds tendsto_bilinearGcd_log_error
  · filter_upwards with X
    exact div_nonneg (abs_nonneg _) (Nat.cast_nonneg X)
  · filter_upwards [eventually_ge_atTop 128] with X hX
    exact abs_primaryBilinearLargeGcd_div_le_log X hX

theorem tendsto_primaryBilinearLargeGcd_div :
    Tendsto (fun X : ℕ => primaryBilinearLargeGcd X / X) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  simpa only [Function.comp_def, abs_div, Nat.abs_cast] using
    tendsto_abs_primaryBilinearLargeGcd_div

/-- Removing the original-factor large-gcd range changes the normalized
signed bilinear term by a quantity tending to zero.-/
theorem tendsto_primary_bilinear_sub_smallGcd_div :
    Tendsto (fun X : ℕ => (bilinearTerm (primaryCutoff X) (primaryCutoff X) X -
      primaryBilinearSmallGcd X) / X) atTop (𝓝 0) := by
  simpa only [primary_bilinear_eq_smallGcd_add_largeGcd, add_sub_cancel_left] using
    tendsto_primaryBilinearLargeGcd_div

end TwinPrime.Analytic
