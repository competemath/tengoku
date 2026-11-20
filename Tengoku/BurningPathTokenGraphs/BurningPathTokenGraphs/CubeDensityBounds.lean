import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.CubeDensityUpper
import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.CubeVolumeLower
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Explicit two-sided bounds for the cube bulk density

This combines the explicit volume lower bound and midpoint-grid upper bound.
-/

namespace BurningPath

/-- The volume lower bound passes to the thermodynamic infimum.
@isnad1 id=le.1h1v.s6.469f8e46b2b8 from=translated src=- shape=f4c2b97e vocab=fa582dd5
-/
theorem cubeBulkDensity_lower {k : ℕ} (hk : 2 ≤ k) :
    ((Nat.factorial k : ℝ) * (k + 1)) / (2 : ℝ) ^ k ≤
      cubeBulkDensity k := by
  rw [cubeBulkDensity]
  apply le_csInf
  · exact
      ⟨(cubeCoverNumber k 1 : ℝ),
        ⟨1, by norm_num, by simp⟩⟩
  · rintro x ⟨L, hL, rfl⟩
    let q := (k + 1) * cubeGridCount k L ^ k
    have hq : 1 ≤ q :=
      Nat.mul_pos (by omega) (pow_pos (cubeGridCount_pos k L) k)
    have hexists :
        ∃ t, 1 ≤ t ∧ HasCubeRankedCover k L t :=
      ⟨q, hq, hasCubeRankedCover_grid hL.le⟩
    obtain ⟨hνpos, hνcover⟩ := cubeCoverNumber_spec hexists
    exact cubeRankedCover_ratio_lower hk hL hνpos hνcover

/-- In particular, the cube bulk density is strictly positive.
@isnad1 id=lt.1h1v.s4.cbf27224da41 from=translated src=- shape=f8216502 vocab=feaa4d36
-/
theorem cubeBulkDensity_pos {k : ℕ} (hk : 2 ≤ k) :
    0 < cubeBulkDensity k := by
  have hlower := cubeBulkDensity_lower hk
  exact lt_of_lt_of_le (by positivity) hlower

/-- Explicit two-sided bounds for the cube bulk density.
@isnad1 id=and.1h1v.s7.2c0f5b043f07 from=translated src=- shape=fddd9545 vocab=fa582dd5
-/
theorem cubeBulkDensity_bounds {k : ℕ} (hk : 2 ≤ k) :
    ((Nat.factorial k : ℝ) * (k + 1)) / (2 : ℝ) ^ k ≤
        cubeBulkDensity k ∧
      cubeBulkDensity k ≤
        (((k + 1 : ℕ) : ℝ) ^ (k + 1)) / (2 : ℝ) ^ k :=
  ⟨cubeBulkDensity_lower hk, cubeBulkDensity_le_explicit k⟩

end BurningPath
