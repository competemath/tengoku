import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Elementary internal cutoffs for the BV mean-value estimate

The eighth-root cutoff uses the explicit threshold `256`. All numerical
inequalities are proved from floor and real-power identities.
-/

noncomputable section

namespace TwinPrime.Analytic

def bvInternalCutoff (T : ℕ) : ℕ := ⌊(T : ℝ) ^ (1 / 8 : ℝ)⌋₊

theorem bvInternalCutoff_two_le (T : ℕ) (hT : 256 ≤ T) : 2 ≤ bvInternalCutoff T := by
  apply Nat.le_floor
  change (2 : ℝ) ≤ (T : ℝ) ^ (1 / 8 : ℝ)
  rw [one_div]
  apply (Real.le_rpow_inv_iff_of_pos (by norm_num) (Nat.cast_nonneg T)
    (show (0 : ℝ) < 8 by norm_num)).mpr
  norm_num
  exact_mod_cast hT

theorem bvInternalCutoff_pos (T : ℕ) (hT : 256 ≤ T) : 0 < bvInternalCutoff T :=
  lt_of_lt_of_le (by norm_num) (bvInternalCutoff_two_le T hT)

theorem bvInternalCutoff_bounds (T : ℕ) (hT : 256 ≤ T) :
    (T : ℝ) ^ (1 / 8 : ℝ) / 2 ≤ (bvInternalCutoff T : ℝ) ∧
      (bvInternalCutoff T : ℝ) ≤ (T : ℝ) ^ (1 / 8 : ℝ) := by
  have hroot : 1 ≤ (T : ℝ) ^ (1 / 8 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast (show 1 ≤ T by omega)) (by norm_num)
  exact ⟨(Nat.div_two_lt_floor hroot).le, Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg T) _)⟩

theorem bvInternalCutoff_sq_le_rpow_quarter (T : ℕ) :
    (bvInternalCutoff T : ℝ) ^ 2 ≤ (T : ℝ) ^ (1 / 4 : ℝ) := by
  have hf : (bvInternalCutoff T : ℝ) ≤ (T : ℝ) ^ (1 / 8 : ℝ) :=
    Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg T) _)
  calc
    _ ≤ ((T : ℝ) ^ (1 / 8 : ℝ)) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hf 2
    _ = _ := by
      rw [← Real.rpow_mul_natCast (Nat.cast_nonneg T)]
      norm_num

theorem bvInternalCutoff_le_sqrt (T : ℕ) (hT : 256 ≤ T) :
    (bvInternalCutoff T : ℝ) ≤ Real.sqrt (T : ℝ) := by
  rw [Real.sqrt_eq_rpow]
  exact (bvInternalCutoff_bounds T hT).2.trans (Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast (show 1 ≤ T by omega)) (by norm_num))

theorem sqrt_rpow_eighth (T : ℕ) :
    Real.sqrt ((T : ℝ) ^ (1 / 8 : ℝ)) = (T : ℝ) ^ (1 / 16 : ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg T)]
  norm_num

theorem bvInternalCutoff_half_reciprocal_sqrt_le (T : ℕ) (hT : 256 ≤ T) :
    1 / Real.sqrt ((bvInternalCutoff T : ℝ) / 2) ≤
      2 * (T : ℝ) ^ (-1 / 16 : ℝ) := by
  have hT0 : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have hf := (bvInternalCutoff_bounds T hT).1
  have hs : (T : ℝ) ^ (1 / 16 : ℝ) / 2 ≤
      Real.sqrt ((bvInternalCutoff T : ℝ) / 2) := by
    calc
      _ = Real.sqrt ((T : ℝ) ^ (1 / 8 : ℝ) / 4) := by
        rw [Real.sqrt_div (Real.rpow_nonneg hT0.le _), sqrt_rpow_eighth]
        norm_num
      _ ≤ _ := Real.sqrt_le_sqrt (by linarith)
  calc
    _ ≤ 1 / ((T : ℝ) ^ (1 / 16 : ℝ) / 2) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hs
    _ = _ := by
      rw [show (-1 / 16 : ℝ) = -(1 / 16 : ℝ) by ring, Real.rpow_neg hT0.le]
      ring

theorem sqrt_modulus_le_rpow_quarter (T R : ℕ)
    (hR : (R : ℝ) ≤ Real.sqrt (T : ℝ)) :
    Real.sqrt (R : ℝ) ≤ (T : ℝ) ^ (1 / 4 : ℝ) := by
  calc
    _ ≤ Real.sqrt (Real.sqrt (T : ℝ)) := Real.sqrt_le_sqrt hR
    _ = _ := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg T)]
      norm_num

theorem bvInternalCutoff_sq_mul_sqrt_modulus_le (T R : ℕ) (hT : 256 ≤ T)
    (hR : (R : ℝ) ≤ Real.sqrt (T : ℝ)) :
    (bvInternalCutoff T : ℝ) ^ 2 * Real.sqrt (R : ℝ) ≤ Real.sqrt (T : ℝ) := by
  have hT0 : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  calc
    _ ≤ (T : ℝ) ^ (1 / 4 : ℝ) * (T : ℝ) ^ (1 / 4 : ℝ) :=
      mul_le_mul (bvInternalCutoff_sq_le_rpow_quarter T) (sqrt_modulus_le_rpow_quarter T R hR)
        (Real.sqrt_nonneg _) (Real.rpow_nonneg hT0.le _)
    _ = _ := by rw [← Real.rpow_add hT0, Real.sqrt_eq_rpow]; norm_num

end TwinPrime.Analytic
