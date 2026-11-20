import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.CubeReplication
import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.FiniteNetCover
import Tengoku.Seed.Algebra.Order.Floor.Ring
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Explicit finite normalized covers of real cubes

This midpoint-grid construction uses `d = 1/(k+1)`.
-/

namespace BurningPath

/-- Number of intervals per coordinate in the midpoint grid.-/
noncomputable def cubeGridCount (k : ℕ) (L : ℝ) : ℕ :=
  max 1 ⌈((k + 1 : ℕ) : ℝ) * L / 2⌉₊

/--
@isnad1 id=le.0h2v.s3.d20f98a50743 from=translated src=- shape=25b8bdde vocab=2853b7a8
-/
theorem cubeGridCount_pos (k : ℕ) (L : ℝ) :
    1 ≤ cubeGridCount k L :=
  le_max_left _ _

/-- The chosen grid intervals have length at most `2/(k+1)`.
@isnad1 id=le.1h2v.s6.bc75b001ff4e from=translated src=- shape=db47e267 vocab=4de80f6d
-/
theorem cubeGrid_mesh_bound {k : ℕ} {L : ℝ} (_hL : 0 ≤ L) :
    L / cubeGridCount k L ≤ 2 / ((k + 1 : ℕ) : ℝ) := by
  let x := (((k + 1 : ℕ) : ℝ) * L / 2)
  have hx : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
  have hceil :
      (⌈x⌉₊ : ℝ) ≤ cubeGridCount k L := by
    exact_mod_cast le_max_right 1 ⌈x⌉₊
  have hm : (0 : ℝ) < cubeGridCount k L := by
    exact_mod_cast cubeGridCount_pos k L
  have hk : (0 : ℝ) < (k + 1 : ℕ) := by positivity
  dsimp [x] at hx
  have hmain :
      (((k + 1 : ℕ) : ℝ) * L / 2) ≤ cubeGridCount k L :=
    hx.trans hceil
  rw [div_le_iff₀ hm]
  rw [show
    2 / (((k + 1 : ℕ) : ℝ)) * cubeGridCount k L =
      (2 * cubeGridCount k L) / (((k + 1 : ℕ) : ℝ)) by ring]
  rw [le_div_iff₀ hk]
  have hmain' :
      (((k + 1 : ℕ) : ℝ) * L) ≤ 2 * cubeGridCount k L := by
    simpa [mul_comm] using
      (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mp hmain
  nlinarith

/--
If `m` intervals per coordinate have mesh at most `2/(k+1)`, their
midpoints give a cover with `(k+1)m^k` normalized ranks.
@isnad1 id=hascuber.3h3v.s6.23e5d6d09d25 from=translated src=- shape=14eed706 vocab=d9c61996
-/
theorem hasCubeRankedCover_midpointGrid {k m : ℕ} {L : ℝ}
    (hm : 1 ≤ m) (hL : 0 ≤ L)
    (hmesh : L / m ≤ 2 / ((k + 1 : ℕ) : ℝ)) :
    HasCubeRankedCover k L ((k + 1) * m ^ k) := by
  classical
  let ell : ℝ := L / m
  let Tile := Fin k → Fin m
  let M := Fintype.card Tile
  let tileEquiv : Tile ≃ Fin M := Fintype.equivFin Tile
  let net : Fin M → (Fin k → ℝ) :=
    fun a i ↦ (tileEquiv.symm a i).val * ell + ell / 2
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hell : 0 ≤ ell := div_nonneg hL hmR.le
  have hmell : (m : ℝ) * ell = L := by
    dsimp [ell]
    field_simp
  have hMpos : 1 ≤ M := by
    apply Fintype.card_pos_iff.mpr
    exact ⟨fun _ ↦ ⟨0, by omega⟩⟩
  have hnetLegal : ∀ a, net a ∈ realCube k L := by
    intro a i
    have hai := (tileEquiv.symm a i).isLt
    simp only [net]
    constructor
    · positivity
    · have hendpoint :
          (((tileEquiv.symm a i).val + 1 : ℕ) : ℝ) * ell ≤
            (m : ℝ) * ell := by
        gcongr
        exact_mod_cast Nat.add_one_le_iff.mpr hai
      push_cast at hendpoint
      rw [hmell] at hendpoint
      nlinarith
  have hnetCover :
      ∀ x ∈ realCube k L, ∃ a, realL1Dist x (net a) ≤
        (k : ℝ) / (k + 1) := by
    intro x hx
    have htile :
        ∀ i, ∃ a : Fin m,
          (a.val : ℝ) * ell ≤ x i ∧
            x i ≤ (a.val + 1 : ℕ) * ell := by
      intro i
      apply exists_cube_tile_interval hm (hx i).1
      rw [hmell]
      exact (hx i).2
    choose tile htileLower htileUpper using htile
    let a := tileEquiv tile
    refine ⟨a, ?_⟩
    have hcoord (i : Fin k) :
        |x i - net a i| ≤ ell / 2 := by
      have hlo := htileLower i
      have hup := htileUpper i
      simp only [net, a, Equiv.symm_apply_apply]
      push_cast at hup
      rw [abs_le]
      constructor <;> nlinarith
    calc
      realL1Dist x (net a) ≤ ∑ _ : Fin k, ell / 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact hcoord i
      _ = (k : ℝ) * (ell / 2) := by simp
      _ ≤ (k : ℝ) / (k + 1) := by
        have hk0 : (0 : ℝ) ≤ k := by positivity
        have hmesh' : ell ≤ 2 / (((k + 1 : ℕ) : ℝ)) := hmesh
        have hscaled :
            (k : ℝ) * ell ≤
              (k : ℝ) * (2 / (((k + 1 : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_left hmesh' hk0
        calc
          (k : ℝ) * (ell / 2) = ((k : ℝ) * ell) / 2 := by ring
          _ ≤ ((k : ℝ) * (2 / (((k + 1 : ℕ) : ℝ)))) / 2 :=
            div_le_div_of_nonneg_right hscaled (by norm_num)
          _ = (k : ℝ) / (k + 1) := by
            have hkne : (k : ℝ) + 1 ≠ 0 := by positivity
            field_simp
            norm_num [Nat.cast_add, Nat.cast_one]
  have hq :
      1 ≤ (k + 1) * M := Nat.mul_pos (by omega) hMpos
  have hMq : M ≤ (k + 1) * M := by
    calc
      M = 1 * M := by simp
      _ ≤ (k + 1) * M := Nat.mul_le_mul_right M (by omega)
  have hradius :
      (k : ℝ) / (k + 1) ≤
        ((((k + 1) * M - M : ℕ) : ℝ) /
          (((k + 1) * M : ℕ) : ℝ)) := by
    have hMR : (0 : ℝ) < M := by exact_mod_cast hMpos
    have hkR : (0 : ℝ) < (k + 1 : ℕ) := by positivity
    have hsub : (k + 1) * M - M = k * M := by
      rw [Nat.add_mul]
      simp
    rw [hsub]
    push_cast
    field_simp
    rfl
  have hcover :
      HasL1NormalizedRankedCover (realCube k L) ((k + 1) * M) :=
    hasL1NormalizedRankedCover_of_finiteNet
      ⟨0, zero_mem_realCube hL⟩ hq hMq net hnetLegal hnetCover hradius
  simpa [HasCubeRankedCover, M, Tile] using hcover

/-- An explicit finite normalized cover of a real cube.
@isnad1 id=hascuber.1h2v.s5.b82fe84fdae6 from=translated src=- shape=f21d1cb0 vocab=e91d7252
-/
theorem hasCubeRankedCover_grid {k : ℕ} {L : ℝ} (hL : 0 ≤ L) :
    HasCubeRankedCover k L
      ((k + 1) * (cubeGridCount k L) ^ k) := by
  exact hasCubeRankedCover_midpointGrid
    (cubeGridCount_pos k L) hL (cubeGrid_mesh_bound hL)

/-- Consequently `ν_k(L)` is finite and obeys the explicit grid bound.
@isnad1 id=le.1h2v.s5.1d3cb8f4f5be from=translated src=- shape=8e7e8e0d vocab=84670d57
-/
theorem cubeCoverNumber_le_grid {k : ℕ} {L : ℝ} (hL : 0 ≤ L) :
    cubeCoverNumber k L ≤ (k + 1) * (cubeGridCount k L) ^ k := by
  apply cubeCoverNumber_min
  exact
    ⟨Nat.mul_pos (by omega) (pow_pos (cubeGridCount_pos k L) k),
      hasCubeRankedCover_grid hL⟩

end BurningPath
