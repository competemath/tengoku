import Tengoku.Rankamplificationtotient.RankAmplification.NonsmoothTransferAssembly
import Tengoku.Rankamplificationtotient.RankAmplification.Section5Assembly

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Assembly of the Section 4 reciprocal provider sum This module proves the `x (log y)^2 / y`-shaped reciprocal estimate (4.5), with an explicit upper-endpoint logarithm and constant. -/

namespace RankAmplification

open Finset
open scoped BigOperators Nat.Prime

noncomputable section

/-- The explicit constant multiplying `1 + log P` in the Mertens estimate.-/
def section4MertensFactor (P : ℕ) : ℝ :=
  Real.exp (4 * Real.log 4) * (1 + Real.log P)

theorem section4MertensFactor_nonneg (P : ℕ) :
    0 ≤ section4MertensFactor P := by
  unfold section4MertensFactor
  by_cases hP : P = 0
  · simp [hP, (Real.exp_pos (4 * Real.log 4)).le]
  · exact mul_nonneg (Real.exp_pos _).le
      (add_nonneg zero_le_one (Real.log_nonneg (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hP))))

theorem finiteProviderReciprocalSum_le_endpoint
    {p X P : ℕ} (hp : 3 ≤ p) (hpP : p ≤ P) :
    finiteProviderReciprocalSum p X ≤
      (p : ℝ)⁻¹ * section4MertensFactor P := by
  have hpPos : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hlog : Real.log (p : ℝ) ≤ Real.log (P : ℝ) := by
    exact Real.log_le_log hpPos (by exact_mod_cast hpP)
  calc
    finiteProviderReciprocalSum p X ≤
        (p : ℝ)⁻¹ * (Real.exp (4 * Real.log 4) * (1 + Real.log p)) :=
      finiteProviderReciprocalSum_le_log p X hp
    _ ≤ (p : ℝ)⁻¹ * section4MertensFactor P := by
      unfold section4MertensFactor
      gcongr

theorem smoothProviderPairReciprocalSum_le_endpoint_sq
    {p X P : ℕ} (hp : 3 ≤ p) (hpP : p ≤ P) :
    smoothProviderPairReciprocalSum p X ≤
      (((p : ℝ) ^ 2)⁻¹) * (section4MertensFactor P) ^ 2 := by
  have hfiniteNonneg : 0 ≤ finiteProviderReciprocalSum p X := by
    unfold finiteProviderReciprocalSum
    positivity
  have hendNonneg : 0 ≤ (p : ℝ)⁻¹ * section4MertensFactor P :=
    mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg p)) (section4MertensFactor_nonneg P)
  have hsquare : (finiteProviderReciprocalSum p X) ^ 2 ≤
      ((p : ℝ)⁻¹ * section4MertensFactor P) ^ 2 := by
    nlinarith [finiteProviderReciprocalSum_le_endpoint (X := X) hp hpP]
  calc
    smoothProviderPairReciprocalSum p X ≤
        (finiteProviderReciprocalSum p X) ^ 2 :=
      smoothProviderPairReciprocalSum_le_sq p X
    _ ≤ ((p : ℝ)⁻¹ * section4MertensFactor P) ^ 2 := hsquare
    _ = (((p : ℝ) ^ 2)⁻¹) * (section4MertensFactor P) ^ 2 := by
      rw [mul_pow, inv_pow]

/-- The exact reciprocal portion `Σ₁` in (4.3).-/
def section4ReciprocalSum (x y : ℕ) : ℝ :=
  (x : ℝ) * ∑ p ∈ section5PrimeRange x y,
    smoothProviderPairReciprocalSum p (section5LocalCutoff x y p)

/-- Explicit finite form of (4.5).-/
theorem section4ReciprocalSum_le {x y : ℕ} (hy : 2 ≤ y) (hxy : y ≤ x) :
    section4ReciprocalSum x y ≤
      (x : ℝ) * (section4MertensFactor (section5Ambient x y).sqrt) ^ 2 * (y : ℝ)⁻¹ := by
  have hfactor : 0 ≤ (section4MertensFactor (section5Ambient x y).sqrt) ^ 2 := sq_nonneg _
  calc
    section4ReciprocalSum x y ≤
        (x : ℝ) * ∑ p ∈ section5PrimeRange x y,
          ((((p : ℝ) ^ 2)⁻¹) *
            (section4MertensFactor (section5Ambient x y).sqrt) ^ 2) := by
      unfold section4ReciprocalSum
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg x)
      apply Finset.sum_le_sum
      intro p hp
      have hpData := mem_section5PrimeRange.mp hp
      exact smoothProviderPairReciprocalSum_le_endpoint_sq
        (by omega) hpData.2.1
    _ = (x : ℝ) * (section4MertensFactor (section5Ambient x y).sqrt) ^ 2 *
        ∑ p ∈ section5PrimeRange x y, (((p : ℝ) ^ 2)⁻¹) := by
      have hsum :
          (∑ p ∈ section5PrimeRange x y,
            (((p : ℝ) ^ 2)⁻¹) *
              (section4MertensFactor (section5Ambient x y).sqrt) ^ 2) =
            (∑ p ∈ section5PrimeRange x y, (((p : ℝ) ^ 2)⁻¹)) *
              (section4MertensFactor (section5Ambient x y).sqrt) ^ 2 := by
        rw [Finset.sum_mul]
      rw [hsum]
      ring
    _ ≤ (x : ℝ) * (section4MertensFactor (section5Ambient x y).sqrt) ^ 2 *
        (y : ℝ)⁻¹ := by
      apply mul_le_mul_of_nonneg_left
        (sum_squareSourcePrimeRange_inv_sq_le_inv (by omega)
          (section5_y_le_sqrt_ambient hxy))
      exact mul_nonneg (Nat.cast_nonneg x) hfactor

/-- The outer nonsquare sum is the reciprocal term plus the Section 5 `B₄` census.-/
theorem nonsquare_outer_sum_eq_section4_add_B4 (x y : ℕ) :
    (∑ p ∈ squareSourcePrimeRange y (2 * x * y).sqrt,
      smoothProviderPairMajorant x p ((2 * x * y) / p ^ 2)) =
      section4ReciprocalSum x y + smoothMultiplierB4Sum x y := by
  simpa [section4ReciprocalSum, section5PrimeRange, section5Ambient,
    section5LocalCutoff] using sum_smoothProviderPairMajorant_eq_reciprocal_add_B4 x y

/-- Completely explicit Section 4+5 outer estimate before the eventual saddle verification.-/
theorem nonsquare_outer_sum_le {x y : ℕ} {saving : ℝ}
    (hy : 2 ≤ y) (hxy : y ≤ x)
    (hRankin : HasSection5IntermediateRankinSaving x y saving) :
    (∑ p ∈ squareSourcePrimeRange y (2 * x * y).sqrt,
      smoothProviderPairMajorant x p ((2 * x * y) / p ^ 2)) ≤
      (x : ℝ) * (section4MertensFactor (section5Ambient x y).sqrt) ^ 2 * (y : ℝ)⁻¹ +
        2 * (x : ℝ) * Real.exp (-saving) +
        2 * (x : ℝ) * (1 + Real.log (section5Ambient x y)) * (y : ℝ)⁻¹ := by
  rw [nonsquare_outer_sum_eq_section4_add_B4]
  simpa only [add_assoc] using
    add_le_add (section4ReciprocalSum_le hy hxy)
      (smoothMultiplierB4Sum_le_exp_add_upper (by omega) hxy hRankin)

end

end RankAmplification
