import Tengoku.Twinprime.TwinPrime.Analytic.ResidueCutoff

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Explicit conductor dependence of the residue cutoff

The numerical cutoff for the budget `1 + 3250 q²` is at most an absolute
constant times `q^40`. Raising this bound to a positive real exponent gives
the denominator comparison used in the quantitative residue estimate.
-/

noncomputable section

namespace TwinPrime.Analytic

def residueConductorConstant : ℝ := 2 * (37044 * 3251) ^ 20

theorem residueConductorConstant_pos : 0 < residueConductorConstant := by
  unfold residueConductorConstant
  positivity

theorem residueCutoff_le_conductor_power (q : ℕ) (hq : 1 ≤ q) :
    (residueCutoff (1 + 3250 * (q : ℝ) ^ 2) : ℝ) ≤
      residueConductorConstant * (q : ℝ) ^ 40 := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq2 : (1 : ℝ) ≤ (q : ℝ) ^ 2 := one_le_pow₀ hqR
  have hC : 1 ≤ 1 + 3250 * (q : ℝ) ^ 2 := by nlinarith [sq_nonneg (q : ℝ)]
  have hbudget : 1 + 3250 * (q : ℝ) ^ 2 ≤ 3251 * (q : ℝ) ^ 2 := by nlinarith
  calc
    _ ≤ 2 * (37044 * (1 + 3250 * (q : ℝ) ^ 2)) ^ 20 :=
      residueCutoff_le_twice_power _ hC
    _ ≤ 2 * (37044 * (3251 * (q : ℝ) ^ 2)) ^ 20 := by
      gcongr
    _ = 2 * (((37044 * 3251) * (q : ℝ) ^ 2) ^ 20) := by rw [mul_assoc]
    _ = _ := by
      rw [mul_pow, ← pow_mul]
      norm_num only [Nat.reduceMul]
      unfold residueConductorConstant
      ring

theorem residue_gap_conductor_bound (q : ℕ) (hq : 1 ≤ q)
    (δ : ℝ) (hδ : 0 < δ) :
    δ / (4 * residueConductorConstant ^ δ * (q : ℝ) ^ (40 * δ)) ≤
      δ / (4 * (residueCutoff (1 + 3250 * (q : ℝ) ^ 2) : ℝ) ^ δ) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hA := residueConductorConstant_pos
  have hC : 1 ≤ 1 + 3250 * (q : ℝ) ^ 2 := by nlinarith [sq_nonneg (q : ℝ)]
  have hN : 0 < (residueCutoff (1 + 3250 * (q : ℝ) ^ 2) : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (show 0 < 1 by omega) (one_le_residueCutoff _ hC))
  have hp : (residueCutoff (1 + 3250 * (q : ℝ) ^ 2) : ℝ) ^ δ ≤
      residueConductorConstant ^ δ * (q : ℝ) ^ (40 * δ) := by
    calc
      _ ≤ (residueConductorConstant * (q : ℝ) ^ 40) ^ δ :=
        Real.rpow_le_rpow hN.le (residueCutoff_le_conductor_power q hq) hδ.le
      _ = _ := by
        rw [Real.mul_rpow hA.le (by positivity), ← Real.rpow_natCast_mul hq0.le]
        norm_num
  apply div_le_div_of_nonneg_left hδ.le (by positivity)
  nlinarith

end TwinPrime.Analytic
