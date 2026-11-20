import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.CubeDensityBounds
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Candidate fixed-dimensional path-token constant

The normalized path-token limit equals this positive root. This file defines
the candidate and proves its explicit bounds.
-/

namespace BurningPath

/-- The candidate limit `c_k = (ρ_k/k!)^(1/(k+1))`.-/
noncomputable def pathTokenLimitConstant (k : ℕ) : ℝ :=
  (cubeBulkDensity k / Nat.factorial k) ^ (k + 1 : ℝ)⁻¹

/--
@isnad1 id=lt.1h1v.s4.d80f1ee1acb9 from=translated src=- shape=f8216502 vocab=2f8dda58
-/
theorem pathTokenLimitConstant_pos {k : ℕ} (hk : 2 ≤ k) :
    0 < pathTokenLimitConstant k := by
  unfold pathTokenLimitConstant
  apply Real.rpow_pos_of_pos
  exact div_pos (cubeBulkDensity_pos hk) (by positivity)

/--
@isnad1 id=eq.1h1v.s5.3cf8b5b8c3b0 from=translated src=- shape=0704c581 vocab=e5cc6aea
-/
@[simp]
theorem pathTokenLimitConstant_pow {k : ℕ} (hk : 2 ≤ k) :
    pathTokenLimitConstant k ^ (k + 1) =
      cubeBulkDensity k / Nat.factorial k := by
  simpa [pathTokenLimitConstant] using
    (Real.rpow_inv_natCast_pow
      (x := cubeBulkDensity k / Nat.factorial k) (n := k + 1)
      (div_nonneg (cubeBulkDensity_pos hk).le (by positivity))
      (by omega))

/-- Explicit two-sided bounds for the candidate limit.
@isnad1 id=and.1h1v.s7.f0b4531f8e8c from=translated src=- shape=c7b33d3d vocab=6b3ef680
-/
theorem pathTokenLimitConstant_bounds {k : ℕ} (hk : 2 ≤ k) :
    (((k + 1 : ℝ) / (2 : ℝ) ^ k) ^ (k + 1 : ℝ)⁻¹) ≤
        pathTokenLimitConstant k ∧
      pathTokenLimitConstant k ≤
        ((((k + 1 : ℕ) : ℝ) ^ (k + 1) /
          ((2 : ℝ) ^ k * Nat.factorial k)) ^
            (k + 1 : ℝ)⁻¹) := by
  have hfac : (0 : ℝ) < Nat.factorial k := by positivity
  have hlowerBase :
      (k + 1 : ℝ) / (2 : ℝ) ^ k ≤
        cubeBulkDensity k / Nat.factorial k := by
    rw [le_div_iff₀ hfac]
    have hlower := cubeBulkDensity_lower hk
    calc
      ((k + 1 : ℝ) / (2 : ℝ) ^ k) * Nat.factorial k =
          (Nat.factorial k : ℝ) * (k + 1) / (2 : ℝ) ^ k := by
        ring
      _ ≤ cubeBulkDensity k := hlower
  have hupperBase :
      cubeBulkDensity k / Nat.factorial k ≤
        ((k + 1 : ℕ) : ℝ) ^ (k + 1) /
          ((2 : ℝ) ^ k * Nat.factorial k) := by
    rw [div_le_iff₀ hfac]
    have hupper := cubeBulkDensity_le_explicit k
    have heq :
        (((k + 1 : ℕ) : ℝ) ^ (k + 1) /
            ((2 : ℝ) ^ k * Nat.factorial k)) *
            Nat.factorial k =
          ((k + 1 : ℕ) : ℝ) ^ (k + 1) / (2 : ℝ) ^ k := by
      field_simp
    rw [heq]
    exact hupper
  constructor
  · unfold pathTokenLimitConstant
    exact Real.rpow_le_rpow (by positivity) hlowerBase (by positivity)
  · unfold pathTokenLimitConstant
    exact
      Real.rpow_le_rpow
        (div_nonneg (cubeBulkDensity_pos hk).le hfac.le)
        hupperBase (by positivity)

end BurningPath
