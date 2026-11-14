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

/--
@isnad1 id=lt.1h1v.s4.66717c229172 from=translated src=- shape=a8dc2df9 vocab=5587a5cb
-/
theorem primaryCutoff_pos {X : ℕ} (hX : 1 ≤ X) : 0 < primaryCutoff X := by
  apply Nat.floor_pos.mpr
  exact Real.one_le_rpow (by exact_mod_cast hX) (by norm_num)

/--
@isnad1 id=le.1h1v.s4.c5767ea8baf6 from=translated src=- shape=71fa8a4a vocab=79d81963
-/
theorem primaryCutoff_le {X : ℕ} (hX : 1 ≤ X) : primaryCutoff X ≤ X := by
  apply Nat.floor_le_of_le
  exact Real.rpow_le_self_of_one_le (by exact_mod_cast hX) (by norm_num)

/--
@isnad1 id=lt.1h1v.s4.be351a61d23b from=translated src=- shape=71fa8a4a vocab=c98bb17f
-/
theorem primaryCutoff_lt {X : ℕ} (hX : 1 < X) : primaryCutoff X < X := by
  apply (Nat.floor_lt (Real.rpow_nonneg (Nat.cast_nonneg X) _)).mpr
  exact Real.rpow_lt_self_of_one_lt (by exact_mod_cast hX) (by norm_num)

/--
@isnad1 id=monotone.0h0v.s2.f27b42dbe52d from=translated src=- shape=e3d48bcb vocab=a8deb238
-/
theorem primaryCutoff_mono : Monotone primaryCutoff := by
  intro X Y hXY
  apply Nat.floor_mono
  exact Real.rpow_le_rpow (Nat.cast_nonneg X) (by exact_mod_cast hXY) (by norm_num)

/-- The fifth power of the floored cutoff stays inside the main scale.
@isnad1 id=le.0h1v.s4.cb93070d9a94 from=translated src=- shape=d81c1b8c vocab=94fcf2a1
-/
theorem primaryCutoff_pow_five_le (X : ℕ) : primaryCutoff X ^ 5 ≤ X := by
  have hf : (primaryCutoff X : ℝ) ≤ (X : ℝ) ^ (5 : ℝ)⁻¹ := by
    simpa only [primaryCutoff, one_div] using
      Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg X) (1 / 5 : ℝ))
  have hp := (Real.le_rpow_inv_iff_of_pos (Nat.cast_nonneg (primaryCutoff X))
    (Nat.cast_nonneg X) (show (0 : ℝ) < 5 by norm_num)).mp hf
  have hp' : (primaryCutoff X : ℝ) ^ 5 ≤ (X : ℝ) := by simpa using hp
  exact_mod_cast hp'

/-- From `X = 32` onward, both primary cutoffs are at least two.
@isnad1 id=le.1h1v.s4.ba2b125336ab from=translated src=- shape=35bd48ee vocab=79d81963
-/
theorem primaryCutoff_two_le {X : ℕ} (hX : 32 ≤ X) : 2 ≤ primaryCutoff X := by
  apply Nat.le_floor
  change (2 : ℝ) ≤ (X : ℝ) ^ (1 / 5 : ℝ)
  rw [one_div]
  apply (Real.le_rpow_inv_iff_of_pos (by norm_num) (Nat.cast_nonneg X)
    (show (0 : ℝ) < 5 by norm_num)).mpr
  norm_num
  exact_mod_cast hX

/-- Simultaneous finite support conditions for the primary route.
@isnad1 id=and.1h1v.s4.2ec0d1bfa8d2 from=translated src=- shape=12fd83f2 vocab=5587a5cb
-/
theorem primaryCutoff_support {X : ℕ} (hX : 32 ≤ X) :
    2 ≤ primaryCutoff X ∧ primaryCutoff X < X :=
  ⟨primaryCutoff_two_le hX, primaryCutoff_lt (by omega)⟩

end TwinPrime.Analytic
