import Tengoku.Twinprime.TwinPrime.Analytic.CutoffLogarithms

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A quarter-root cutoff for the second Vaughan variable

These floor and growth comparisons keep the product of the fifth-root and
quarter-root cutoffs below the exponent `9/20`. They provide numerical support
for finite cutoff changes and do not assert cancellation of a bilinear sum.
-/

noncomputable section

open Filter

namespace TwinPrime.Analytic

/-- The auxiliary second-variable cutoff `⌊X^(1/4)⌋`.-/
def quarterCutoff (X : ℕ) : ℕ := ⌊(X : ℝ) ^ (1 / 4 : ℝ)⌋₊

theorem quarterCutoff_pos {X : ℕ} (hX : 1 ≤ X) : 0 < quarterCutoff X := by
  apply Nat.floor_pos.mpr
  exact Real.one_le_rpow (by exact_mod_cast hX) (by norm_num)

theorem quarterCutoff_le {X : ℕ} (hX : 1 ≤ X) : quarterCutoff X ≤ X := by
  apply Nat.floor_le_of_le
  exact Real.rpow_le_self_of_one_le (by exact_mod_cast hX) (by norm_num)

theorem quarterCutoff_lt {X : ℕ} (hX : 1 < X) : quarterCutoff X < X := by
  apply (Nat.floor_lt (Real.rpow_nonneg (Nat.cast_nonneg X) _)).mpr
  exact Real.rpow_lt_self_of_one_lt (by exact_mod_cast hX) (by norm_num)

theorem quarterCutoff_mono : Monotone quarterCutoff := by
  intro X Y hXY
  apply Nat.floor_mono
  exact Real.rpow_le_rpow (Nat.cast_nonneg X) (by exact_mod_cast hXY) (by norm_num)

theorem primaryCutoff_le_quarterCutoff {X : ℕ} (hX : 1 ≤ X) :
    primaryCutoff X ≤ quarterCutoff X := by
  apply Nat.floor_mono
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hX) (by norm_num)

theorem tendsto_quarterCutoff : Tendsto quarterCutoff atTop atTop := by
  exact tendsto_nat_floor_atTop.comp
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
      tendsto_natCast_atTop_atTop)

/-- The fourth power of the floored cutoff does not exceed the scale.-/
theorem quarterCutoff_pow_four_le (X : ℕ) : quarterCutoff X ^ 4 ≤ X := by
  have hf : (quarterCutoff X : ℝ) ≤ (X : ℝ) ^ (4 : ℝ)⁻¹ := by
    simpa only [quarterCutoff, one_div] using
      Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg X) (1 / 4 : ℝ))
  have hp := (Real.le_rpow_inv_iff_of_pos (Nat.cast_nonneg (quarterCutoff X))
    (Nat.cast_nonneg X) (show (0 : ℝ) < 4 by norm_num)).mp hf
  have hp' : (quarterCutoff X : ℝ) ^ 4 ≤ (X : ℝ) := by simpa using hp
  exact_mod_cast hp'

/-- The two cutoff exponents add to `9/20`, strictly below one half.-/
theorem primaryCutoff_mul_quarterCutoff_le_rpow (X : ℕ) (hX : 1 ≤ X) :
    (primaryCutoff X : ℝ) * (quarterCutoff X : ℝ) ≤ (X : ℝ) ^ (9 / 20 : ℝ) := by
  have hx : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hU : (primaryCutoff X : ℝ) ≤ (X : ℝ) ^ (1 / 5 : ℝ) :=
    Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg X) _)
  have hW : (quarterCutoff X : ℝ) ≤ (X : ℝ) ^ (1 / 4 : ℝ) :=
    Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg X) _)
  calc
    (primaryCutoff X : ℝ) * (quarterCutoff X : ℝ) ≤
        (X : ℝ) ^ (1 / 5 : ℝ) * (X : ℝ) ^ (1 / 4 : ℝ) :=
      mul_le_mul hU hW (Nat.cast_nonneg _) (Real.rpow_nonneg hx.le _)
    _ = (X : ℝ) ^ (9 / 20 : ℝ) := by rw [← Real.rpow_add hx]; norm_num

theorem primaryCutoff_mul_quarterCutoff_le {X : ℕ} (hX : 1 ≤ X) :
    primaryCutoff X * quarterCutoff X ≤ X := by
  have h := (primaryCutoff_mul_quarterCutoff_le_rpow X hX).trans
    (Real.rpow_le_self_of_one_le (by exact_mod_cast hX) (by norm_num))
  exact_mod_cast h

/-- A uniform logarithmic comparison, including the scale `X = 1`.-/
theorem log_quarterCutoff_add_one_le_five_log_primaryCutoff
    (X : ℕ) (hX : 1 ≤ X) :
    Real.log ((quarterCutoff X : ℝ) + 1) ≤
      5 * Real.log ((primaryCutoff X : ℝ) + 1) := by
  have hnat : quarterCutoff X + 1 ≤ (primaryCutoff X + 1) ^ 5 := by
    have hW := quarterCutoff_le hX
    have hU := primaryCutoff_inverse_bound X
    omega
  have hreal : (quarterCutoff X : ℝ) + 1 ≤ ((primaryCutoff X : ℝ) + 1) ^ 5 := by
    exact_mod_cast hnat
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < quarterCutoff X + 1) hreal
  simpa only [Real.log_pow, Nat.cast_ofNat] using hlog

end TwinPrime.Analytic
