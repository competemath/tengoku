import Tengoku.Twinprime.TwinPrime.Analytic.Dispersion
import Tengoku.Twinprime.TwinPrime.Analytic.BVLogComparisons

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Summing the dispersion diagonal over growing box families

The normalized diagonal bound is uniform in both side lengths. The entire
sum of its square roots is negligible even after any fixed logarithmic
loss, for any admissible family with at most the square of the dyadic depth
many boxes. No off-diagonal estimate is assumed or concluded.
-/

noncomputable section

open Finset Filter

namespace TwinPrime.Analytic

def dispersionDiagonalSum (U V X : ℕ) (s : Finset (ℕ × ℕ)) : ℝ :=
  ∑ ij ∈ s, Real.sqrt (dispersionMass V (2 ^ ij.2) *
    dispersionDiagonal U V X (2 ^ ij.1) (2 ^ ij.2))

/--
@isnad1 id=le.0h4v.s4.4c654df65e80 from=translated src=- shape=f14d7cc0 vocab=dc81345d
-/
theorem dispersionDiagonalSum_nonneg (U V X : ℕ) (s : Finset (ℕ × ℕ)) :
    0 ≤ dispersionDiagonalSum U V X s := sum_nonneg fun _ _ => Real.sqrt_nonneg _

/--
@isnad1 id=le.6h5v.s7.96878ad81b5e from=translated src=- shape=1f3f3d3c vocab=c6c648c9
-/
theorem dispersion_diagonal_sqrt_div_le (U V X M N : ℕ)
    (hU : 1 ≤ U) (hX : 1 ≤ X) (hM : 1 ≤ M) (hN : 1 ≤ N)
    (hUM : U ≤ 2 * M) (hMN : M * N ≤ 2 * X) :
    Real.sqrt (dispersionMass V N * dispersionDiagonal U V X M N) / X ≤
      Real.sqrt (8 * (Real.log (4 * X + 4)) ^ 4 / U) := by
  have h := Real.sqrt_le_sqrt (dispersion_diagonal_div_sq_le U V X M N hU hX hM hN hUM hMN)
  rwa [Real.sqrt_div (mul_nonneg (dispersionMass_nonneg V N)
    (dispersionDiagonal_nonneg U V X M N)), Real.sqrt_sq (Nat.cast_nonneg X)] at h

/--
@isnad1 id=le.3h4v.s8.fbded2b371eb from=translated src=- shape=078f7d96 vocab=83868d8a
-/
theorem dispersionDiagonalSum_div_le (U V X : ℕ) (s : Finset (ℕ × ℕ))
    (hU : 1 ≤ U) (hX : 1 ≤ X)
    (hs : ∀ ij ∈ s, U ≤ 2 * 2 ^ ij.1 ∧ 2 ^ ij.1 * 2 ^ ij.2 ≤ 2 * X) :
    dispersionDiagonalSum U V X s / X ≤
      s.card * Real.sqrt (8 * (Real.log (4 * X + 4)) ^ 4 / U) := by
  unfold dispersionDiagonalSum
  rw [sum_div]
  calc
    _ ≤ ∑ _ij ∈ s, Real.sqrt (8 * (Real.log (4 * X + 4)) ^ 4 / U) := by
      apply sum_le_sum
      intro ij hij
      exact dispersion_diagonal_sqrt_div_le U V X (2 ^ ij.1) (2 ^ ij.2) hU hX
        (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide)))
        (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide)))
        (hs ij hij).1 (hs ij hij).2
    _ = _ := by simp

/-- Uniform control of the complete growing family, not a pointwise limit
with one pair of side lengths fixed in advance.
@isnad1 id=tendsto.2h2v.s8.3c55f16107a5 from=translated src=- shape=cc69df34 vocab=a809a36a
-/
theorem tendsto_primary_dispersion_diagonal_sum (s : ℕ → Finset (ℕ × ℕ)) (k : ℕ)
    (hcard : ∀ᶠ X : ℕ in atTop, (s X).card ≤ (dyadicNatDepth (2 * X)) ^ 2)
    (hrange : ∀ᶠ X : ℕ in atTop, ∀ ij ∈ s X,
      primaryCutoff X ≤ 2 * 2 ^ ij.1 ∧ 2 ^ ij.1 * 2 ^ ij.2 ≤ 2 * X) :
    Tendsto (fun X : ℕ =>
      dispersionDiagonalSum (primaryCutoff X) (primaryCutoff X) X (s X) / X *
        (Real.log (4 * X + 4)) ^ k) atTop (nhds 0) := by
  let a : ℝ := 2 / Real.log 2
  have ha : 0 < a := div_pos (by norm_num) (Real.log_pos (by norm_num))
  have hbase := (tendsto_dispersion_log_pow_div_primaryCutoff (4 + 2 * (k + 2))).const_mul 8
  have hroot := (Real.continuous_sqrt.tendsto 0).comp (by simpa using hbase)
  have hu := hroot.const_mul (a ^ 2)
  simp only [Real.sqrt_zero, mul_zero] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · filter_upwards with X
    have hL : 0 ≤ Real.log (4 * (X : ℝ) + 4) :=
      Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) X; linarith)
    exact mul_nonneg (div_nonneg (dispersionDiagonalSum_nonneg _ _ _ _) (Nat.cast_nonneg X))
      (pow_nonneg hL k)
  · filter_upwards [hcard, hrange, eventually_ge_atTop 128] with X hcardX hrangeX hX
    let L := Real.log (4 * (X : ℝ) + 4)
    have hL : 0 ≤ L := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) X; linarith)
    have hU : 1 ≤ primaryCutoff X := primaryCutoff_pos (by omega)
    have hD : (dyadicNatDepth (2 * X) : ℝ) ≤ a * L := by
      have hd := dyadicNatDepth_le_two_div_log_two_mul_log (2 * X) (by omega)
      apply hd.trans
      apply mul_le_mul_of_nonneg_left _ ha.le
      apply Real.log_le_log (by positivity)
      push_cast
      linarith
    have hcardR : ((s X).card : ℝ) ≤ a ^ 2 * L ^ 2 := by
      have hc : ((s X).card : ℝ) ≤ (dyadicNatDepth (2 * X) : ℝ) ^ 2 := by exact_mod_cast hcardX
      apply hc.trans
      calc
        _ ≤ (a * L) ^ 2 := by gcongr
        _ = _ := by ring
    have hb := dispersionDiagonalSum_div_le (primaryCutoff X) (primaryCutoff X) X (s X)
      hU (by omega) hrangeX
    have he : (a ^ 2 * L ^ 2) * Real.sqrt (8 * L ^ 4 / primaryCutoff X) * L ^ k =
        a ^ 2 * Real.sqrt (8 * (L ^ (4 + 2 * (k + 2)) / primaryCutoff X)) := by
      have hQ : 0 ≤ 8 * L ^ 4 / (primaryCutoff X : ℝ) := by positivity
      rw [show 8 * (L ^ (4 + 2 * (k + 2)) / (primaryCutoff X : ℝ)) =
          (8 * L ^ 4 / (primaryCutoff X : ℝ)) * (L ^ (k + 2)) ^ 2 by
        rw [pow_add, pow_mul]; ring]
      rw [Real.sqrt_mul hQ, Real.sqrt_sq (pow_nonneg hL _), pow_add]
      ring
    change _ ≤ a ^ 2 * Real.sqrt (8 * (L ^ (4 + 2 * (k + 2)) / primaryCutoff X))
    calc
      _ ≤ ((s X).card * Real.sqrt (8 * L ^ 4 / primaryCutoff X)) * L ^ k :=
        mul_le_mul_of_nonneg_right hb (pow_nonneg hL k)
      _ ≤ (a ^ 2 * L ^ 2) * Real.sqrt (8 * L ^ 4 / primaryCutoff X) * L ^ k := by gcongr
      _ = _ := he

end TwinPrime.Analytic
