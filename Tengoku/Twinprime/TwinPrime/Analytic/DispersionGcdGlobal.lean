import Tengoku.Twinprime.TwinPrime.Analytic.DispersionGlobal
import Tengoku.Twinprime.TwinPrime.Analytic.DispersionLargeGcd
import Tengoku.Twinprime.TwinPrime.Analytic.DispersionGcdCutoff

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Removing the large-gcd off-diagonal from the full dispersion budget

The total large-gcd square-root error is negligible at the logarithmic
cutoff, over the entire active dyadic family. The signed small-gcd part
is kept explicitly. No estimate for that remaining part is asserted.
-/

noncomputable section

open Finset Filter

namespace TwinPrime.Analytic

def dispersionLargeGcdSum (U V X G : ℕ) (s : Finset (ℕ × ℕ)) : ℝ :=
  ∑ ij ∈ s, Real.sqrt (dispersionMass V (2 ^ ij.2) *
    |dispersionOffDiagonalLargeGcd U V X (2 ^ ij.1) (2 ^ ij.2) G|)

def dispersionSmallGcdSum (U V X G : ℕ) (s : Finset (ℕ × ℕ)) : ℝ :=
  ∑ ij ∈ s, Real.sqrt (max (dispersionMass V (2 ^ ij.2) *
    dispersionOffDiagonalSmallGcd U V X (2 ^ ij.1) (2 ^ ij.2) G) 0)

theorem dispersionLargeGcdSum_nonneg (U V X G : ℕ) (s : Finset (ℕ × ℕ)) :
    0 ≤ dispersionLargeGcdSum U V X G s := sum_nonneg fun _ _ => Real.sqrt_nonneg _

theorem dispersionSmallGcdSum_nonneg (U V X G : ℕ) (s : Finset (ℕ × ℕ)) :
    0 ≤ dispersionSmallGcdSum U V X G s := sum_nonneg fun _ _ => Real.sqrt_nonneg _

theorem dispersion_largeGcd_sqrt_div_le (U V X M N G : ℕ)
    (hX : 1 ≤ X) (hM : 1 ≤ M) (hN : 1 ≤ N) (hG : 1 ≤ G)
    (hMN : M * N ≤ 2 * X) :
    Real.sqrt (dispersionMass V N * |dispersionOffDiagonalLargeGcd U V X M N G|) / X ≤
      Real.sqrt (16 * (Real.log (4 * X + 4)) ^ 4 / G) := by
  have hx0 : (0 : ℝ) < X := by exact_mod_cast hX
  have hprod := mul_nonneg (dispersionMass_nonneg V N)
    (abs_nonneg (dispersionOffDiagonalLargeGcd U V X M N G))
  have hb := div_le_div_of_nonneg_right
    (dispersion_mass_mul_abs_largeGcd_le U V X M N G hM hN hG hMN)
    (sq_nonneg (X : ℝ))
  have he : (16 * (X : ℝ) ^ 2 * (Real.log (4 * X + 4)) ^ 4 / G) / (X : ℝ) ^ 2 =
      16 * (Real.log (4 * X + 4)) ^ 4 / G := by field_simp
  rw [he] at hb
  have hs := Real.sqrt_le_sqrt hb
  rwa [Real.sqrt_div hprod, Real.sqrt_sq (Nat.cast_nonneg X)] at hs

theorem dispersionLargeGcdSum_div_le (U V X G : ℕ) (s : Finset (ℕ × ℕ))
    (hX : 1 ≤ X) (hG : 1 ≤ G)
    (hs : ∀ ij ∈ s, 2 ^ ij.1 * 2 ^ ij.2 ≤ 2 * X) :
    dispersionLargeGcdSum U V X G s / X ≤
      s.card * Real.sqrt (16 * (Real.log (4 * X + 4)) ^ 4 / G) := by
  unfold dispersionLargeGcdSum
  rw [sum_div]
  calc
    _ ≤ ∑ _ij ∈ s, Real.sqrt (16 * (Real.log (4 * X + 4)) ^ 4 / G) := by
      apply sum_le_sum
      intro ij hij
      exact dispersion_largeGcd_sqrt_div_le U V X (2 ^ ij.1) (2 ^ ij.2) G hX
        (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide)))
        (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide))) hG (hs ij hij)
    _ = _ := by simp

theorem abs_bilinearBox_le_gcd_dispersion (U V X M N G : ℕ) :
    |bilinearBox U V X M N| ≤
      Real.sqrt (dispersionMass V N * dispersionDiagonal U V X M N) +
      Real.sqrt (dispersionMass V N * |dispersionOffDiagonalLargeGcd U V X M N G|) +
      Real.sqrt (max (dispersionMass V N * dispersionOffDiagonalSmallGcd U V X M N G) 0) := by
  let T := dispersionMass V N
  let D := dispersionDiagonal U V X M N
  let A := dispersionOffDiagonalLargeGcd U V X M N G
  let B := dispersionOffDiagonalSmallGcd U V X M N G
  have hT : 0 ≤ T := dispersionMass_nonneg V N
  have hTD : 0 ≤ T * D := mul_nonneg hT (dispersionDiagonal_nonneg U V X M N)
  have hTA : 0 ≤ T * |A| := mul_nonneg hT (abs_nonneg A)
  have hTB : 0 ≤ max (T * B) 0 := le_max_right _ _
  have hbound := bilinearBox_sq_le_dispersion U V X M N
  rw [dispersionOffDiagonal_eq_small_add_large U V X M N G] at hbound
  change bilinearBox U V X M N ^ 2 ≤ T * (D + (B + A)) at hbound
  have hAle := mul_le_mul_of_nonneg_left (le_abs_self A) hT
  have hBle := le_max_left (T * B) 0
  have hd := Real.sqrt_nonneg (T * D)
  have ha := Real.sqrt_nonneg (T * |A|)
  have hb := Real.sqrt_nonneg (max (T * B) 0)
  have hdsq := Real.sq_sqrt hTD
  have hasq := Real.sq_sqrt hTA
  have hbsq := Real.sq_sqrt hTB
  change |bilinearBox U V X M N| ≤ Real.sqrt (T * D) + Real.sqrt (T * |A|) +
    Real.sqrt (max (T * B) 0)
  nlinarith [sq_abs (bilinearBox U V X M N), abs_nonneg (bilinearBox U V X M N),
    mul_nonneg hd ha, mul_nonneg hd hb, mul_nonneg ha hb]

theorem abs_bilinearTerm_le_gcd_dispersion (U V X G : ℕ) (hU : 1 ≤ U) (hV : 1 ≤ V) :
    |bilinearTerm U V X| ≤
      dispersionDiagonalSum U V X (dispersionBoxIndices U V X) +
      dispersionLargeGcdSum U V X G (dispersionBoxIndices U V X) +
      dispersionSmallGcdSum U V X G (dispersionBoxIndices U V X) := by
  rw [bilinearTerm_eq_sum_dispersionBoxes U V X hU hV]
  apply (abs_sum_le_sum_abs _ _).trans
  unfold dispersionDiagonalSum dispersionLargeGcdSum dispersionSmallGcdSum
  rw [← sum_add_distrib, ← sum_add_distrib]
  exact sum_le_sum fun ij _ => abs_bilinearBox_le_gcd_dispersion U V X (2 ^ ij.1) (2 ^ ij.2) G

def primaryDispersionLargeGcd (X : ℕ) : ℝ :=
  dispersionLargeGcdSum (primaryCutoff X) (primaryCutoff X) X (dispersionGcdCutoff X)
    (dispersionBoxIndices (primaryCutoff X) (primaryCutoff X) X)

def primaryDispersionSmallGcd (X : ℕ) : ℝ :=
  dispersionSmallGcdSum (primaryCutoff X) (primaryCutoff X) X (dispersionGcdCutoff X)
    (dispersionBoxIndices (primaryCutoff X) (primaryCutoff X) X)

/-- The complete large-gcd off-diagonal budget is sublinear at G=ceil(L^10).-/
theorem tendsto_primaryDispersionLargeGcd_div :
    Tendsto (fun X : ℕ => primaryDispersionLargeGcd X / X) atTop (nhds 0) := by
  apply tendsto_div_of_dispersionGcdCutoff_bound
  · exact Eventually.of_forall fun X => dispersionLargeGcdSum_nonneg _ _ X _ _
  · filter_upwards [eventually_ge_atTop 1] with X hX
    apply (dispersionLargeGcdSum_div_le _ _ X _ _ hX (one_le_dispersionGcdCutoff X) ?_).trans
    · apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      exact_mod_cast dispersionBoxIndices_card_le (primaryCutoff X) (primaryCutoff X) X
    · intro ij hij
      exact (dispersionBoxIndices_bounds hij).2.2.2.2.1

theorem neg_primary_gcd_dispersion_le_bilinearTerm (X : ℕ) (hX : 1 ≤ X) :
    -(primaryDispersionDiagonal X + primaryDispersionLargeGcd X + primaryDispersionSmallGcd X) ≤
      bilinearTerm (primaryCutoff X) (primaryCutoff X) X := by
  have hU := primaryCutoff_pos hX
  have hb := abs_bilinearTerm_le_gcd_dispersion _ _ X (dispersionGcdCutoff X) hU hU
  change |bilinearTerm (primaryCutoff X) (primaryCutoff X) X| ≤
    primaryDispersionDiagonal X + primaryDispersionLargeGcd X + primaryDispersionSmallGcd X at hb
  linarith [neg_abs_le (bilinearTerm (primaryCutoff X) (primaryCutoff X) X)]

end TwinPrime.Analytic
