import Tengoku.Twinprime.TwinPrime.Analytic.DispersionAggregate
import Tengoku.Twinprime.TwinPrime.Analytic.DispersionPartition

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Global dispersion budget with its remaining signed correlations explicit

The exact box partition permits summing the full dispersion inequality.
The total diagonal contribution is negligible. The positive part of the
weighted off-diagonal is retained and is not estimated here.
-/

noncomputable section

open Finset Filter

namespace TwinPrime.Analytic

def dispersionOffDiagonalSum (U V X : ℕ) (s : Finset (ℕ × ℕ)) : ℝ :=
  ∑ ij ∈ s, Real.sqrt (max (dispersionMass V (2 ^ ij.2) *
    dispersionOffDiagonal U V X (2 ^ ij.1) (2 ^ ij.2)) 0)

theorem dispersionOffDiagonalSum_nonneg (U V X : ℕ) (s : Finset (ℕ × ℕ)) :
    0 ≤ dispersionOffDiagonalSum U V X s := sum_nonneg fun _ _ => Real.sqrt_nonneg _

theorem abs_bilinearBox_le_diagonal_add_offDiagonal (U V X M N : ℕ) :
    |bilinearBox U V X M N| ≤
      Real.sqrt (dispersionMass V N * dispersionDiagonal U V X M N) +
      Real.sqrt (max (dispersionMass V N * dispersionOffDiagonal U V X M N) 0) := by
  have h := bilinearBox_sq_le_dispersion U V X M N
  rw [mul_add] at h
  have hd := mul_nonneg (dispersionMass_nonneg V N) (dispersionDiagonal_nonneg U V X M N)
  have ho := le_max_right (dispersionMass V N * dispersionOffDiagonal U V X M N) 0
  have hmax := le_max_left (dispersionMass V N * dispersionOffDiagonal U V X M N) 0
  have hdsq := Real.sq_sqrt hd
  have hosq := Real.sq_sqrt ho
  have hdr := Real.sqrt_nonneg (dispersionMass V N * dispersionDiagonal U V X M N)
  have hor := Real.sqrt_nonneg (max (dispersionMass V N * dispersionOffDiagonal U V X M N) 0)
  nlinarith [sq_abs (bilinearBox U V X M N), abs_nonneg (bilinearBox U V X M N),
    mul_nonneg hdr hor]

theorem abs_bilinearTerm_le_dispersion_sums (U V X : ℕ) (hU : 1 ≤ U) (hV : 1 ≤ V) :
    |bilinearTerm U V X| ≤
      dispersionDiagonalSum U V X (dispersionBoxIndices U V X) +
      dispersionOffDiagonalSum U V X (dispersionBoxIndices U V X) := by
  rw [bilinearTerm_eq_sum_dispersionBoxes U V X hU hV]
  apply (abs_sum_le_sum_abs _ _).trans
  unfold dispersionDiagonalSum dispersionOffDiagonalSum
  rw [← sum_add_distrib]
  exact sum_le_sum fun ij _ => abs_bilinearBox_le_diagonal_add_offDiagonal U V X (2 ^ ij.1) (2 ^ ij.2)

theorem neg_dispersion_sums_le_bilinearTerm (U V X : ℕ) (hU : 1 ≤ U) (hV : 1 ≤ V) :
    -(dispersionDiagonalSum U V X (dispersionBoxIndices U V X) +
      dispersionOffDiagonalSum U V X (dispersionBoxIndices U V X)) ≤ bilinearTerm U V X := by
  have hb := abs_bilinearTerm_le_dispersion_sums U V X hU hV
  linarith [neg_abs_le (bilinearTerm U V X)]

def primaryDispersionDiagonal (X : ℕ) : ℝ :=
  dispersionDiagonalSum (primaryCutoff X) (primaryCutoff X) X
    (dispersionBoxIndices (primaryCutoff X) (primaryCutoff X) X)

def primaryDispersionOffDiagonal (X : ℕ) : ℝ :=
  dispersionOffDiagonalSum (primaryCutoff X) (primaryCutoff X) X
    (dispersionBoxIndices (primaryCutoff X) (primaryCutoff X) X)

/-- The diagonal sum over every active box is negligible, even with any
additional fixed power of the logarithm.-/
theorem tendsto_primaryDispersionDiagonal_div_log_pow (k : ℕ) :
    Tendsto (fun X : ℕ => primaryDispersionDiagonal X / X *
      (Real.log (4 * X + 4)) ^ k) atTop (nhds 0) := by
  apply tendsto_primary_dispersion_diagonal_sum
  · exact Eventually.of_forall fun X => dispersionBoxIndices_card_le _ _ X
  · apply Eventually.of_forall
    intro X ij hij
    have hb := dispersionBoxIndices_bounds hij
    exact ⟨hb.2.2.1, hb.2.2.2.2.1⟩

theorem tendsto_primaryDispersionDiagonal_div :
    Tendsto (fun X : ℕ => primaryDispersionDiagonal X / X) atTop (nhds 0) := by
  simpa only [pow_zero, mul_one] using tendsto_primaryDispersionDiagonal_div_log_pow 0

/-- A vanishing off-diagonal budget would imply absolute cancellation of
the actual bilinear term. This hypothesis is not supplied by the diagonal.-/
theorem tendsto_primary_bilinear_div_of_offDiagonal
    (hOff : Tendsto (fun X : ℕ => primaryDispersionOffDiagonal X / X) atTop (nhds 0)) :
    Tendsto (fun X : ℕ => bilinearTerm (primaryCutoff X) (primaryCutoff X) X / X)
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  have hu := tendsto_primaryDispersionDiagonal_div.add hOff
  simp only [zero_add] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · exact Eventually.of_forall fun _ => abs_nonneg _
  · filter_upwards [eventually_ge_atTop 1] with X hX
    dsimp only [Function.comp_def]
    rw [abs_div, abs_of_nonneg (show (0 : ℝ) ≤ (X : ℝ) from Nat.cast_nonneg X)]
    have hU := primaryCutoff_pos hX
    have hb := div_le_div_of_nonneg_right (abs_bilinearTerm_le_dispersion_sums _ _ X hU hU)
      (Nat.cast_nonneg X : (0 : ℝ) ≤ _)
    simpa only [add_div, primaryDispersionDiagonal, primaryDispersionOffDiagonal] using hb

end TwinPrime.Analytic
