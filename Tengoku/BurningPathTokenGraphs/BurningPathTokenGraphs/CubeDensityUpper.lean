import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.CubeDensityLimit
import Tengoku.Seed.Analysis.SpecificLimits.Basic
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Explicit upper bound for the cube bulk density

This formalizes equation (45).
-/

open Filter
open scoped Topology

namespace BurningPath

/-- The normalized value of the explicit midpoint-grid cover.-/
noncomputable def cubeGridDensityBound (k : ℕ) (L : ℝ) : ℝ :=
  (((k + 1) * cubeGridCount k L ^ k : ℕ) : ℝ) / L ^ k

/-- The grid count divided by `L` tends to `(k+1)/2`.-/
theorem tendsto_cubeGridCount_div (k : ℕ) :
    Tendsto
      (fun L : ℝ ↦ (cubeGridCount k L : ℝ) / L)
      atTop (𝓝 (((k + 1 : ℕ) : ℝ) / 2)) := by
  let a : ℝ := ((k + 1 : ℕ) : ℝ) / 2
  have ha : 0 ≤ a := by positivity
  have hceil :
      Tendsto (fun L : ℝ ↦ (⌈a * L⌉₊ : ℝ) / L)
        atTop (𝓝 a) :=
    tendsto_nat_ceil_mul_div_atTop ha
  apply hceil.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
  have haPos : 0 < a := by positivity
  have hceilPos : 1 ≤ ⌈a * L⌉₊ := by
    have : 0 < a * L := mul_pos haPos (by linarith)
    exact Nat.ceil_pos.mpr this
  simp only [cubeGridCount, a]
  have harg :
      ((k + 1 : ℕ) : ℝ) / 2 * L =
        ((k + 1 : ℕ) : ℝ) * L / 2 := by ring
  rw [harg] at hceilPos ⊢
  rw [max_eq_right hceilPos]

/-- The explicit normalized grid bound has the constant from equation (45).-/
theorem tendsto_cubeGridDensityBound (k : ℕ) :
    Tendsto (cubeGridDensityBound k) atTop
      (𝓝 ((((k + 1 : ℕ) : ℝ) ^ (k + 1)) / 2 ^ k)) := by
  have hbase := (tendsto_cubeGridCount_div k).pow k
  have hmul :
      Tendsto
        (fun L : ℝ ↦
          ((k + 1 : ℕ) : ℝ) *
            (((cubeGridCount k L : ℝ) / L) ^ k))
        atTop
        (𝓝 (((k + 1 : ℕ) : ℝ) *
          ((((k + 1 : ℕ) : ℝ) / 2) ^ k))) :=
    tendsto_const_nhds.mul hbase
  convert hmul using 1
  · funext L
    unfold cubeGridDensityBound
    push_cast
    rw [div_pow]
    ring
  · rw [div_pow, pow_succ']
    norm_num [Nat.cast_add, Nat.cast_one]
    ring

/-- The true density is bounded by the explicit grid density at every positive side length.-/
theorem cubeCoverDensityAt_le_grid {k : ℕ} {L : ℝ} (hL : 0 < L) :
    cubeCoverDensityAt k L ≤ cubeGridDensityBound k L := by
  unfold cubeCoverDensityAt cubeGridDensityBound
  apply div_le_div_of_nonneg_right
  · exact_mod_cast cubeCoverNumber_le_grid (k := k) hL.le
  · exact pow_nonneg hL.le k

/-- Explicit upper bound for the cube bulk density.-/
theorem cubeBulkDensity_le_explicit (k : ℕ) :
    cubeBulkDensity k ≤
      (((k + 1 : ℕ) : ℝ) ^ (k + 1)) / 2 ^ k := by
  apply ge_of_tendsto (tendsto_cubeGridDensityBound k)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
  exact
    (cubeBulkDensity_le_densityAt (by linarith)).trans
      (cubeCoverDensityAt_le_grid (by linarith))

end BurningPath
