import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Real
import Tengoku.Seed.Algebra.Order.Floor.Ring
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The primary fifth-root cutoff

The cutoff in the proof plan is a natural floor of a real fifth root. These
elementary support lemmas justify the finite decompositions' cutoff conditions;
they supply no prime-correlation estimate.
-/

noncomputable section

namespace TwinPrime.Analytic

/-- The common primary-route choice `U = V = ⌊X^(1/5)⌋`.-/
def primaryCutoff (X : ℕ) : ℕ := ⌊(X : ℝ) ^ (1 / 5 : ℝ)⌋₊

theorem primaryCutoff_pos {X : ℕ} (hX : 1 ≤ X) : 0 < primaryCutoff X := by
  apply Nat.floor_pos.mpr
  exact Real.one_le_rpow (by exact_mod_cast hX) (by norm_num)

theorem primaryCutoff_le {X : ℕ} (hX : 1 ≤ X) : primaryCutoff X ≤ X := by
  apply Nat.floor_le_of_le
  exact Real.rpow_le_self_of_one_le (by exact_mod_cast hX) (by norm_num)

theorem primaryCutoff_lt {X : ℕ} (hX : 1 < X) : primaryCutoff X < X := by
  apply (Nat.floor_lt (Real.rpow_nonneg (Nat.cast_nonneg X) _)).mpr
  exact Real.rpow_lt_self_of_one_lt (by exact_mod_cast hX) (by norm_num)

theorem primaryCutoff_mono : Monotone primaryCutoff := by
  intro X Y hXY
  apply Nat.floor_mono
  exact Real.rpow_le_rpow (Nat.cast_nonneg X) (by exact_mod_cast hXY) (by norm_num)

/-- The fifth power of the floored cutoff stays inside the main scale.-/
theorem primaryCutoff_pow_five_le (X : ℕ) : primaryCutoff X ^ 5 ≤ X := by
  have hf : (primaryCutoff X : ℝ) ≤ (X : ℝ) ^ (5 : ℝ)⁻¹ := by
    simpa only [primaryCutoff, one_div] using
      Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg X) (1 / 5 : ℝ))
  have hp := (Real.le_rpow_inv_iff_of_pos (Nat.cast_nonneg (primaryCutoff X))
    (Nat.cast_nonneg X) (show (0 : ℝ) < 5 by norm_num)).mp hf
  have hp' : (primaryCutoff X : ℝ) ^ 5 ≤ (X : ℝ) := by simpa using hp
  exact_mod_cast hp'

/-- From `X = 32` onward, both primary cutoffs are at least two.-/
theorem primaryCutoff_two_le {X : ℕ} (hX : 32 ≤ X) : 2 ≤ primaryCutoff X := by
  apply Nat.le_floor
  change (2 : ℝ) ≤ (X : ℝ) ^ (1 / 5 : ℝ)
  rw [one_div]
  apply (Real.le_rpow_inv_iff_of_pos (by norm_num) (Nat.cast_nonneg X)
    (show (0 : ℝ) < 5 by norm_num)).mpr
  norm_num
  exact_mod_cast hX

/-- Simultaneous finite support conditions for the primary route.-/
theorem primaryCutoff_support {X : ℕ} (hX : 32 ≤ X) :
    2 ≤ primaryCutoff X ∧ primaryCutoff X < X :=
  ⟨primaryCutoff_two_le hX, primaryCutoff_lt (by omega)⟩

end TwinPrime.Analytic
