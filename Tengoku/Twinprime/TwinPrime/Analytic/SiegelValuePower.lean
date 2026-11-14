import Tengoku.Twinprime.TwinPrime.Analytic.ResidueConductorBound
import Tengoku.Twinprime.TwinPrime.Analytic.CharacterConvolutionPower

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Power absorption for the auxiliary residue bound

An auxiliary zero gap at most `ε/80` leaves half the exponent available
for the three logarithmic factors. All constants below are explicit and
positive for a fixed positive auxiliary gap and L-value norm.
-/

noncomputable section

namespace TwinPrime.Analytic

def siegelValuePowerConstant (ε δ L : ℝ) : ℝ :=
  δ / (20 * L * residueConductorConstant ^ δ * (1 + 6 / ε) ^ 3)

/--
@isnad1 id=lt.3h3v.s5.b7be25cfcedf from=translated src=- shape=1b4cbc0d vocab=fa3e12ef
-/
theorem siegelValuePowerConstant_pos (ε δ L : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hL : 0 < L) :
    0 < siegelValuePowerConstant ε δ L := by
  unfold siegelValuePowerConstant
  have hA := residueConductorConstant_pos
  positivity

/--
@isnad1 id=le.3h3v.s7.43a9d5edf077 from=translated src=- shape=5f6a228d vocab=e0c65887
-/
theorem rpow_gap_mul_log_cube_le (ε δ Q : ℝ) (hε : 0 < ε)
    (hδε : δ ≤ ε / 80) (hQ : 1 ≤ Q) :
    Q ^ (40 * δ) * (1 + Real.log Q) ^ 3 ≤
      (1 + 6 / ε) ^ 3 * Q ^ ε := by
  have hQ0 : 0 < Q := by linarith
  have hlog : 1 + Real.log Q ≤ (1 + 6 / ε) * Q ^ (ε / 6) := by
    have h := one_add_log_le_one_add_inv_mul_rpow Q (ε / 6) hQ (by positivity)
    convert h using 1
    field_simp
  have hpow : Q ^ (40 * δ) * (Q ^ (ε / 6)) ^ 3 = Q ^ (40 * δ + ε / 2) := by
    rw [← Real.rpow_mul_natCast hQ0.le, ← Real.rpow_add hQ0]
    congr 1
    ring
  calc
    _ ≤ Q ^ (40 * δ) * ((1 + 6 / ε) * Q ^ (ε / 6)) ^ 3 :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by linarith [Real.log_nonneg hQ]) hlog 3) (Real.rpow_nonneg hQ0.le _)
    _ = (1 + 6 / ε) ^ 3 * (Q ^ (40 * δ) * (Q ^ (ε / 6)) ^ 3) := by ring
    _ = (1 + 6 / ε) ^ 3 * Q ^ (40 * δ + ε / 2) := by rw [hpow]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hQ (by linarith)) (by positivity)

/-- The auxiliary lower bound dominates a fixed positive multiple of `Q^-ε`.
@isnad1 id=le.5h4v.s7.e826edc03f91 from=translated src=- shape=5e9fee3f vocab=f1bd8b6d
-/
theorem siegelValuePowerConstant_mul_rpow_le (ε δ L Q : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hL : 0 < L) (hδε : δ ≤ ε / 80) (hQ : 1 ≤ Q) :
    siegelValuePowerConstant ε δ L * Q ^ (-ε) ≤
      δ / (20 * L * residueConductorConstant ^ δ * Q ^ (40 * δ) *
        (1 + Real.log Q) ^ 3) := by
  have hQ0 : 0 < Q := by linarith
  have hA := residueConductorConstant_pos
  have hlog : 0 < 1 + Real.log Q := by linarith [Real.log_nonneg hQ]
  have hbase : 0 < 20 * L * residueConductorConstant ^ δ := by positivity
  calc
    _ = δ / ((20 * L * residueConductorConstant ^ δ) *
        ((1 + 6 / ε) ^ 3 * Q ^ ε)) := by
      unfold siegelValuePowerConstant
      rw [Real.rpow_neg hQ0.le]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ δ / ((20 * L * residueConductorConstant ^ δ) *
        (Q ^ (40 * δ) * (1 + Real.log Q) ^ 3)) := by
      apply div_le_div_of_nonneg_left hδ.le (by positivity)
      exact mul_le_mul_of_nonneg_left (rpow_gap_mul_log_cube_le ε δ Q hε hδε hQ) hbase.le
    _ = _ := by ring

end TwinPrime.Analytic
