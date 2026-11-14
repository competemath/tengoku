import Tengoku.Twinprime.TwinPrime.Analytic.BilinearGcdReduction
import Tengoku.Twinprime.TwinPrime.Analytic.DispersionGcdGlobal
import Tengoku.Twinprime.TwinPrime.Analytic.DispersionActiveBand

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Logarithmic budgets for the thin band of nonzero dispersion boxes

The product interval limits the number of nonzero boxes to a linear function
of the dyadic depth. These numerical bounds account for that entire family.
No cancellation of the remaining signed small-gcd contribution is asserted.
-/

noncomputable section

open Finset Filter

namespace TwinPrime.Analytic

/--
@isnad1 id=le.1h1v.s7.39cd32cc6b37 from=translated src=- shape=f4e23de3 vocab=b21d50e5
-/
theorem dispersionGcdCutoff_linear_family_error_le (X : ℕ) (hX : 128 ≤ X) :
    (3 * dyadicNatDepth (2 * X) : ℝ) *
      Real.sqrt (16 * (Real.log (4 * (X : ℝ) + 4)) ^ 4 / dispersionGcdCutoff X) ≤
        12 * (2 / Real.log 2) / (Real.log (4 * (X : ℝ) + 4)) ^ 2 := by
  let L : ℝ := Real.log (4 * (X : ℝ) + 4)
  have hL : 0 < L := lt_of_lt_of_le (by norm_num) (one_le_dispersion_log X)
  have hD := dyadicNatDepth_two_mul_le_dispersion_log X hX
  calc
    _ ≤ (3 * ((2 / Real.log 2) * L)) * (4 / L ^ 3) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hD (by norm_num))
        (sqrt_dispersionGcdCutoff_error_le X) (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by
      change (3 * ((2 / Real.log 2) * L)) * (4 / L ^ 3) =
        12 * (2 / Real.log 2) / L ^ 2
      field_simp
      ring

/--
@isnad1 id=le.1h1v.s7.d1d6d0d2500c from=translated src=- shape=f985c43c vocab=33f55fac
-/
theorem bilinearGcdCutoff_linear_family_error_le (X : ℕ) (hX : 128 ≤ X) :
    (3 * dyadicNatDepth (2 * X) : ℝ) * 8 * (Real.log (4 * (X : ℝ) + 4)) ^ 2 /
        dispersionGcdCutoff X ≤
      24 * (2 / Real.log 2) / (Real.log (4 * (X : ℝ) + 4)) ^ 7 := by
  let L : ℝ := Real.log (4 * (X : ℝ) + 4)
  have hL : 0 < L := lt_of_lt_of_le (by norm_num) (one_le_dispersion_log X)
  have hG : (0 : ℝ) < dispersionGcdCutoff X := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (one_le_dispersionGcdCutoff X))
  have hD := dyadicNatDepth_two_mul_le_dispersion_log X hX
  calc
    _ ≤ (3 * ((2 / Real.log 2) * L)) * 8 * L ^ 2 / dispersionGcdCutoff X := by
      apply div_le_div_of_nonneg_right _ hG.le
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hD (by norm_num))
          (by norm_num)) (sq_nonneg L)
    _ ≤ 24 * (2 / Real.log 2) / L ^ 7 := by
      apply (div_le_iff₀ hG).mpr
      have h := mul_le_mul_of_nonneg_left (log_pow_le_dispersionGcdCutoff X)
        (show 0 ≤ 24 * (2 / Real.log 2) / L ^ 7 by positivity)
      have heq : (24 * (2 / Real.log 2) / L ^ 7) * L ^ 10 =
          (3 * ((2 / Real.log 2) * L)) * 8 * L ^ 2 := by field_simp; ring
      exact heq.symm.trans_le h

/--
@isnad1 id=le.2h3v.s7.815a103fe348 from=translated src=- shape=0acb6819 vocab=1d6ba3fb
-/
theorem dispersionDiagonalSum_div_le_linear (U V X : ℕ)
    (hU : 1 ≤ U) (hX : 1 ≤ X) :
    dispersionDiagonalSum U V X (dispersionBoxIndices U V X) / X ≤
      (3 * dyadicNatDepth (2 * X) : ℝ) *
        Real.sqrt (8 * (Real.log (4 * X + 4)) ^ 4 / U) := by
  rw [dispersionDiagonalSum_eq_active]
  apply (dispersionDiagonalSum_div_le U V X _ hU hX ?_).trans
  · apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    exact_mod_cast dispersionActiveBoxIndices_card_le U V X
  · intro ij hij
    have hb := dispersionBoxIndices_bounds (dispersionActiveBoxIndices_subset U V X hij)
    exact ⟨hb.2.2.1, hb.2.2.2.2.1⟩

/--
@isnad1 id=le.2h4v.s7.20aef7b66534 from=translated src=- shape=0bbd8bb8 vocab=50e8765a
-/
theorem dispersionLargeGcdSum_div_le_linear (U V X G : ℕ)
    (hX : 1 ≤ X) (hG : 1 ≤ G) :
    dispersionLargeGcdSum U V X G (dispersionBoxIndices U V X) / X ≤
      (3 * dyadicNatDepth (2 * X) : ℝ) *
        Real.sqrt (16 * (Real.log (4 * X + 4)) ^ 4 / G) := by
  rw [dispersionLargeGcdSum_eq_active]
  apply (dispersionLargeGcdSum_div_le U V X G _ hX hG ?_).trans
  · apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    exact_mod_cast dispersionActiveBoxIndices_card_le U V X
  · intro ij hij
    exact (dispersionBoxIndices_bounds (dispersionActiveBoxIndices_subset U V X hij)).2.2.2.2.1

/--
@isnad1 id=le.1h1v.s7.81b8b3cd5eb5 from=translated src=- shape=0052a2df vocab=984ab2a7
-/
theorem primaryDispersionLargeGcd_div_le_log_sq (X : ℕ) (hX : 128 ≤ X) :
    primaryDispersionLargeGcd X / X ≤
      12 * (2 / Real.log 2) / (Real.log (4 * (X : ℝ) + 4)) ^ 2 :=
  (dispersionLargeGcdSum_div_le_linear _ _ X _ (by omega)
    (one_le_dispersionGcdCutoff X)).trans (dispersionGcdCutoff_linear_family_error_le X hX)

/--
@isnad1 id=eq.1h6v.s6.81d1d58ff23e from=translated src=- shape=fd532551 vocab=0c20e319
-/
theorem bilinearBoxLargeGcd_eq_zero_of_not_band (U V X M N G : ℕ)
    (hband : ¬ (X < 4 * (M * N) ∧ M * N < 2 * X)) :
    bilinearBoxLargeGcd U V X M N G = 0 := by
  unfold bilinearBoxLargeGcd
  apply sum_eq_zero
  intro dr hdr
  have hpair := mem_product.mp (mem_filter.mp hdr).1
  rw [dispersionEntry_eq_zero_of_not_band (mem_filter.mp hpair.1).1
    (mem_filter.mp hpair.2).1 hband, mul_zero]

/--
@isnad1 id=eq.2h4v.s6.972a6e8b44d0 from=translated src=- shape=6886f68a vocab=0269836d
-/
theorem bilinearLargeGcd_eq_sum_active_boxes (U V X G : ℕ) (hU : 1 ≤ U) (hV : 1 ≤ V) :
    bilinearLargeGcd U V X G = ∑ ij ∈ dispersionActiveBoxIndices U V X,
      bilinearBoxLargeGcd U V X (2 ^ ij.1) (2 ^ ij.2) G := by
  rw [bilinearLargeGcd_eq_sum_boxes U V X G hU hV]
  apply sum_dispersionBoxIndices_eq_active
  intro ij _ hband
  exact bilinearBoxLargeGcd_eq_zero_of_not_band U V X _ _ G hband

/--
@isnad1 id=le.4h4v.s7.3575da3463da from=translated src=- shape=7574227f vocab=e5525e0e
-/
theorem abs_bilinearLargeGcd_div_le_linear (U V X G : ℕ)
    (hU : 1 ≤ U) (hV : 1 ≤ V) (hX : 1 ≤ X) (hG : 1 ≤ G) :
    |bilinearLargeGcd U V X G| / X ≤
      (3 * dyadicNatDepth (2 * X) : ℝ) * 8 * (Real.log (4 * X + 4)) ^ 2 / G := by
  have hx : (0 : ℝ) < X := by exact_mod_cast hX
  have hmass : |bilinearLargeGcd U V X G| ≤
      (3 * dyadicNatDepth (2 * X) : ℝ) *
        (8 * (X : ℝ) * (Real.log (4 * X + 4)) ^ 2 / G) := by
    rw [bilinearLargeGcd_eq_sum_active_boxes U V X G hU hV]
    calc
      _ ≤ ∑ ij ∈ dispersionActiveBoxIndices U V X,
          |bilinearBoxLargeGcd U V X (2 ^ ij.1) (2 ^ ij.2) G| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ij ∈ dispersionActiveBoxIndices U V X,
          8 * (X : ℝ) * (Real.log (4 * X + 4)) ^ 2 / G := by
        apply sum_le_sum
        intro ij hij
        have hb := dispersionBoxIndices_bounds (dispersionActiveBoxIndices_subset U V X hij)
        exact abs_bilinearBoxLargeGcd_le U V X _ _ G hb.1 hb.2.1 hG hb.2.2.2.2.1
      _ = (dispersionActiveBoxIndices U V X).card *
          (8 * (X : ℝ) * (Real.log (4 * X + 4)) ^ 2 / G) := by simp
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast dispersionActiveBoxIndices_card_le U V X
  calc
    _ ≤ ((3 * dyadicNatDepth (2 * X) : ℝ) *
        (8 * (X : ℝ) * (Real.log (4 * X + 4)) ^ 2 / G)) / X :=
      div_le_div_of_nonneg_right hmass hx.le
    _ = _ := by field_simp

/--
@isnad1 id=le.3h3v.s7.a1a2fbd20078 from=translated src=- shape=ba6a4aee vocab=31935527
-/
theorem abs_bilinearLargeGcd_div_le_log_seven (U V X : ℕ)
    (hU : 1 ≤ U) (hV : 1 ≤ V) (hX : 128 ≤ X) :
    |bilinearLargeGcd U V X (dispersionGcdCutoff X)| / X ≤
      24 * (2 / Real.log 2) / (Real.log (4 * (X : ℝ) + 4)) ^ 7 :=
  (abs_bilinearLargeGcd_div_le_linear U V X _ hU hV (by omega)
    (one_le_dispersionGcdCutoff X)).trans (bilinearGcdCutoff_linear_family_error_le X hX)

/--
@isnad1 id=le.1h1v.s7.d406fa757645 from=translated src=- shape=0b8d5b41 vocab=d13072f5
-/
theorem abs_primaryBilinearLargeGcd_div_le_log_seven (X : ℕ) (hX : 128 ≤ X) :
    |primaryBilinearLargeGcd X| / X ≤
      24 * (2 / Real.log 2) / (Real.log (4 * (X : ℝ) + 4)) ^ 7 :=
  abs_bilinearLargeGcd_div_le_log_seven _ _ X
    (primaryCutoff_pos (by omega)) (primaryCutoff_pos (by omega)) hX

end TwinPrime.Analytic
