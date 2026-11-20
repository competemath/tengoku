import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.CubeFiniteCover
import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.CubeReplication
import Tengoku.Seed.Analysis.SpecificLimits.Basic
import Tengoku.Seed.Order.ConditionallyCompleteLattice.Basic
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Thermodynamic limit for normalized cube covers

This proves that normalized cube-cover counts converge to their variational
infimum. Separate modules establish explicit upper and lower numerical bounds.
-/

open Filter
open scoped Topology

namespace BurningPath

/-- Normalized cover count at side length `L`.-/
noncomputable def cubeCoverDensityAt (k : ℕ) (L : ℝ) : ℝ :=
  (cubeCoverNumber k L : ℝ) / L ^ k

private theorem exists_cubeRankedCover {k : ℕ} {L : ℝ} (hL : 0 ≤ L) :
    ∃ q, 1 ≤ q ∧ HasCubeRankedCover k L q := by
  let q := (k + 1) * cubeGridCount k L ^ k
  refine ⟨q, ?_, hasCubeRankedCover_grid hL⟩
  exact Nat.mul_pos (by omega) (pow_pos (cubeGridCount_pos k L) k)

private theorem cubeDensityValues_nonempty (k : ℕ) :
    {x : ℝ | ∃ L : ℝ, 0 < L ∧ x = cubeCoverDensityAt k L}.Nonempty := by
  exact ⟨cubeCoverDensityAt k 1, 1, by norm_num, rfl⟩

private theorem cubeDensityValues_bddBelow (k : ℕ) :
    BddBelow {x : ℝ | ∃ L : ℝ, 0 < L ∧ x = cubeCoverDensityAt k L} := by
  refine ⟨0, ?_⟩
  rintro x ⟨L, hL, rfl⟩
  exact div_nonneg (by positivity) (pow_nonneg hL.le k)

/-- The bulk infimum is a lower bound for every positive-side density.-/
theorem cubeBulkDensity_le_densityAt {k : ℕ} {L : ℝ} (hL : 0 < L) :
    cubeBulkDensity k ≤ cubeCoverDensityAt k L := by
  rw [cubeBulkDensity]
  apply csInf_le (cubeDensityValues_bddBelow k)
  exact ⟨L, hL, rfl⟩

/-- Every strict upper bound on the infimum is beaten at some positive side length.-/
theorem exists_cubeCoverDensityAt_lt {k : ℕ} {U : ℝ}
    (hU : cubeBulkDensity k < U) :
    ∃ L : ℝ, 0 < L ∧ cubeCoverDensityAt k L < U := by
  rw [cubeBulkDensity] at hU
  obtain ⟨x, ⟨L, hL, rfl⟩, hx⟩ :=
    exists_lt_of_csInf_lt (cubeDensityValues_nonempty k) hU
  exact ⟨L, hL, hx⟩

/-- The ceiling replication factor `⌈L/L₀⌉/(L/L₀)`.-/
noncomputable def cubeReplicationFactor (L₀ L : ℝ) : ℝ :=
  (⌈L / L₀⌉₊ : ℝ) / (L / L₀)

/-- For fixed positive `L₀`, the replication factor tends to one.-/
theorem tendsto_cubeReplicationFactor (L₀ : ℝ) (hL₀ : 0 < L₀) :
    Tendsto (cubeReplicationFactor L₀) atTop (𝓝 1) := by
  have hratio :
      Tendsto (fun L : ℝ ↦ L / L₀) atTop atTop := by
    simpa [div_eq_mul_inv, mul_comm] using
      tendsto_id.const_mul_atTop (inv_pos.mpr hL₀)
  exact tendsto_nat_ceil_div_atTop.comp hratio

/-- Replication bounds a large-side density by a fixed density times the ceiling factor.-/
theorem cubeCoverDensityAt_le_replication {k : ℕ} {L₀ L : ℝ}
    (hL₀ : 0 < L₀) (hL₀L : L₀ ≤ L) :
    cubeCoverDensityAt k L ≤
      cubeCoverDensityAt k L₀ * cubeReplicationFactor L₀ L ^ k := by
  have hL : 0 < L := hL₀.trans_le hL₀L
  have hNat :=
    cubeCoverNumber_le_ceil_mul hL₀ hL₀L
      (exists_cubeRankedCover (k := k) hL₀.le)
  have hcast :
      (cubeCoverNumber k L : ℝ) ≤
        (⌈L / L₀⌉₊ ^ k * cubeCoverNumber k L₀ : ℕ) := by
    exact_mod_cast hNat
  calc
    cubeCoverDensityAt k L ≤
        ((⌈L / L₀⌉₊ ^ k * cubeCoverNumber k L₀ : ℕ) : ℝ) /
          L ^ k := by
      exact div_le_div_of_nonneg_right hcast (pow_nonneg hL.le k)
    _ = cubeCoverDensityAt k L₀ * cubeReplicationFactor L₀ L ^ k := by
      have hfactor :
          cubeReplicationFactor L₀ L =
            (⌈L / L₀⌉₊ : ℝ) * L₀ / L := by
        unfold cubeReplicationFactor
        field_simp [hL.ne', hL₀.ne']
      unfold cubeCoverDensityAt
      rw [hfactor, div_pow, mul_pow]
      push_cast
      field_simp [hL.ne', hL₀.ne', pow_ne_zero]

/-- Normalized cube-cover counts converge to their variational infimum.-/
theorem tendsto_cubeCoverDensityAt (k : ℕ) :
    Tendsto (cubeCoverDensityAt k) atTop (𝓝 (cubeBulkDensity k)) := by
  apply tendsto_order.2
  constructor
  · intro l hl
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
    exact hl.trans_le (cubeBulkDensity_le_densityAt (by linarith))
  · intro U hU
    obtain ⟨L₀, hL₀, hL₀U⟩ := exists_cubeCoverDensityAt_lt hU
    have htend :
        Tendsto
          (fun L ↦
            cubeCoverDensityAt k L₀ * cubeReplicationFactor L₀ L ^ k)
          atTop (𝓝 (cubeCoverDensityAt k L₀)) := by
      simpa using
        tendsto_const_nhds.mul ((tendsto_cubeReplicationFactor L₀ hL₀).pow k)
    filter_upwards
      [eventually_ge_atTop L₀, htend.eventually (Iio_mem_nhds hL₀U)]
      with L hL hfactor
    exact (cubeCoverDensityAt_le_replication hL₀ hL).trans_lt hfactor

/-- The same limit written directly in terms of `cubeCoverNumber`.-/
theorem cubeBulkDensity_eq_limit (k : ℕ) :
    Tendsto
      (fun L ↦ (cubeCoverNumber k L : ℝ) / L ^ k)
      atTop (𝓝 (cubeBulkDensity k)) :=
  tendsto_cubeCoverDensityAt k

end BurningPath
