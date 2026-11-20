import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.RankInterleaving
import Tengoku.Seed.Algebra.Order.Floor.Ring
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Replication of normalized cube covers

This module proves the geometric replication estimate
`ν_k(mL) ≤ m^k ν_k(L)`.
-/

namespace BurningPath

/-- Every point of `[0,mL]` lies in one of the `m` consecutive intervals of length `L`.
@isnad1 id=ex.3h3v.s6.125f0434b541 from=translated src=- shape=291be526 vocab=a51b41dd
-/
theorem exists_cube_tile_interval {m : ℕ} (hm : 1 ≤ m)
    {L x : ℝ} (hx0 : 0 ≤ x) (hxm : x ≤ m * L) :
    ∃ a : Fin m, (a.val : ℝ) * L ≤ x ∧ x ≤ (a.val + 1 : ℕ) * L := by
  induction m generalizing x with
  | zero => omega
  | succ m ih =>
      cases m with
      | zero =>
        refine ⟨⟨0, by omega⟩, ?_, ?_⟩
        · simpa using hx0
        · simpa using hxm
      | succ m =>
          by_cases hx : x ≤ ((m + 1 : ℕ) : ℝ) * L
          · obtain ⟨a, haLower, haUpper⟩ := ih (by omega) hx0 hx
            exact ⟨⟨a.val, by omega⟩, haLower, haUpper⟩
          · refine ⟨⟨m + 1, by omega⟩, le_of_not_ge hx, ?_⟩
            simpa [Nat.cast_add, Nat.cast_one] using hxm

/-- Translation preserves the real `ℓ₁` distance.
@isnad1 id=eq.0h4v.s5.451d10e714de from=translated src=- shape=95aec994 vocab=fc12ece5
-/
theorem realL1Dist_add_left {k : ℕ} (a x y : Fin k → ℝ) :
    realL1Dist (fun i ↦ a i + x i) (fun i ↦ a i + y i) =
      realL1Dist x y := by
  simp [realL1Dist]

/-- Clamp a point coordinatewise to the upper face of `Q_L`.-/
def clampToCube (L : ℝ) {k : ℕ} (x : Fin k → ℝ) : Fin k → ℝ :=
  fun i ↦ min (x i) L

/-- Clamping a center into a smaller cube cannot increase its distance to a point of that cube.
@isnad1 id=le.1h4v.s5.cd9d17d30972 from=translated src=- shape=3e8ae2cf vocab=9f65b44d
-/
theorem realL1Dist_clampToCube_le {k : ℕ} {L : ℝ}
    (x c : Fin k → ℝ) (hx : x ∈ realCube k L) :
    realL1Dist x (clampToCube L c) ≤ realL1Dist x c := by
  apply Finset.sum_le_sum
  intro i _
  simp only [clampToCube]
  by_cases hc : c i ≤ L
  · simp [min_eq_left hc]
  · have hxc : x i ≤ c i := (hx i).2.trans (le_of_not_ge hc)
    have hxL := (hx i).2
    rw [show min (c i) L = L by exact min_eq_right (le_of_not_ge hc)]
    rw [abs_of_nonpos (sub_nonpos.mpr hxL), abs_of_nonpos (sub_nonpos.mpr hxc)]
    linarith

/--
A cover of a larger cube restricts to a smaller cube after clamping every
center to the smaller cube.
@isnad1 id=hascuber.3h4v.s5.c01592586df7 from=translated src=- shape=c0aa0b27 vocab=4a91b96f
-/
theorem HasCubeRankedCover.restrict {k q : ℕ} {L U : ℝ}
    (hL : 0 ≤ L) (hLU : L ≤ U)
    (hcover : HasCubeRankedCover k U q) :
    HasCubeRankedCover k L q := by
  obtain ⟨centers, hlegal, hcover⟩ := hcover
  let clamped : Fin q → (Fin k → ℝ) :=
    fun i ↦ clampToCube L (centers i)
  refine ⟨clamped, ?_, ?_⟩
  · intro i j
    simp only [clamped, clampToCube]
    constructor
    · exact le_min (hlegal i j).1 hL
    · exact min_le_right _ _
  · intro x hx
    have hxU : x ∈ realCube k U := by
      intro i
      exact ⟨(hx i).1, (hx i).2.trans hLU⟩
    obtain ⟨i, hi⟩ := hcover x hxU
    refine ⟨i, ?_⟩
    exact (realL1Dist_clampToCube_le x (centers i) hx).trans hi

/--
Replicate a normalized ranked cover of `Q_L` in the `m^k` axis-parallel
tiles of `Q_(mL)` and interleave their ranks.
@isnad1 id=hascuber.4h4v.s6.908627579c49 from=translated src=- shape=2d40aa7e vocab=d9f0e2f9
-/
theorem HasCubeRankedCover.replicate {k m q : ℕ} {L : ℝ}
    (hm : 1 ≤ m) (hq : 1 ≤ q) (hL : 0 ≤ L)
    (hcover : HasCubeRankedCover k L q) :
    HasCubeRankedCover k ((m : ℝ) * L) (m ^ k * q) := by
  classical
  obtain ⟨baseCenters, hbaseLegal, hbaseCover⟩ := hcover
  let Tile := Fin k → Fin m
  let M := Fintype.card Tile
  let tileEquiv : Tile ≃ Fin M := Fintype.equivFin Tile
  let offset (a : Tile) : Fin k → ℝ :=
    fun i ↦ (a i).val * L
  let centers : Fin M → Fin q → (Fin k → ℝ) :=
    fun a j i ↦ offset (tileEquiv.symm a) i + baseCenters j i
  have hM : 1 ≤ M := by
    apply Fintype.card_pos_iff.mpr
    exact ⟨fun _ ↦ ⟨0, by omega⟩⟩
  have hlegal : ∀ a j, centers a j ∈ realCube k ((m : ℝ) * L) := by
    intro a j i
    have ha := (tileEquiv.symm a i).isLt
    have hc := hbaseLegal j i
    simp only [centers, offset]
    constructor
    · exact add_nonneg (mul_nonneg (by positivity) hL) hc.1
    · have haLe : ((tileEquiv.symm a i).val + 1 : ℕ) ≤ m := by omega
      have hoff :
          ((tileEquiv.symm a i).val : ℝ) * L + L ≤ (m : ℝ) * L := by
        have hcast : (((tileEquiv.symm a i).val + 1 : ℕ) : ℝ) ≤ m := by
          exact_mod_cast haLe
        push_cast at hcast
        nlinarith
      nlinarith
  have hpoint :
      ∀ x ∈ realCube k ((m : ℝ) * L),
        ∃ a : Fin M, ∃ j : Fin q,
          realL1Dist x (centers a j) ≤ (j.val : ℝ) / q := by
    intro x hx
    have htile :
        ∀ i, ∃ a : Fin m,
          (a.val : ℝ) * L ≤ x i ∧ x i ≤ (a.val + 1 : ℕ) * L := by
      intro i
      exact exists_cube_tile_interval hm (hx i).1 (hx i).2
    choose tile htileLower htileUpper using htile
    let y : Fin k → ℝ := fun i ↦ x i - (tile i).val * L
    have hy : y ∈ realCube k L := by
      intro i
      constructor
      · exact sub_nonneg.mpr (htileLower i)
      · have hu := htileUpper i
        push_cast at hu
        dsimp only [y]
        nlinarith
    obtain ⟨j, hj⟩ := hbaseCover y hy
    let a := tileEquiv tile
    refine ⟨a, j, ?_⟩
    have hdist :
        realL1Dist x (centers a j) = realL1Dist y (baseCenters j) := by
      unfold realL1Dist
      apply Finset.sum_congr rfl
      intro i _
      simp only [centers, offset, a, Equiv.symm_apply_apply, y]
      congr 1
      ring
    rw [hdist]
    exact hj
  have hinterleaved :
      HasL1NormalizedRankedCover
        (realCube k ((m : ℝ) * L)) (M * q) :=
    hasL1NormalizedRankedCover_interleave hM hq centers hlegal hpoint
  simpa [HasCubeRankedCover, M, Tile, Nat.mul_comm] using hinterleaved

/-- Replicating a cube cover across `m^k` tiles multiplies its size by at most `m^k`.
@isnad1 id=le.3h3v.s6.d3294b321059 from=translated src=- shape=758e8287 vocab=33b74fbb
-/
theorem cubeCoverNumber_nat_mul_le {k m : ℕ} {L : ℝ}
    (hm : 1 ≤ m) (hL : 0 ≤ L)
    (hexists : ∃ q, 1 ≤ q ∧ HasCubeRankedCover k L q) :
    cubeCoverNumber k ((m : ℝ) * L) ≤ m ^ k * cubeCoverNumber k L := by
  obtain ⟨hq, hcover⟩ := cubeCoverNumber_spec hexists
  apply cubeCoverNumber_min
  constructor
  · exact Nat.mul_pos (pow_pos hm k) hq
  · exact hcover.replicate hm hq hL

/-- Coordinatewise clamping extends the replication bound to arbitrary side lengths.
@isnad1 id=le.3h3v.s6.4505b1dd25a1 from=translated src=- shape=a7c2d0e4 vocab=20fc2d18
-/
theorem cubeCoverNumber_le_ceil_mul {k : ℕ} {L₀ L : ℝ}
    (hL₀ : 0 < L₀) (hL₀L : L₀ ≤ L)
    (hexists : ∃ q, 1 ≤ q ∧ HasCubeRankedCover k L₀ q) :
    cubeCoverNumber k L ≤
      ⌈L / L₀⌉₊ ^ k * cubeCoverNumber k L₀ := by
  let m := ⌈L / L₀⌉₊
  have hratio : (1 : ℝ) ≤ L / L₀ := by
    rw [le_div_iff₀ hL₀]
    simpa using hL₀L
  have hm : 1 ≤ m := by
    have hceil : L / L₀ ≤ (m : ℝ) := Nat.le_ceil _
    exact_mod_cast hratio.trans hceil
  have hLm : L ≤ (m : ℝ) * L₀ := by
    have hceil : L / L₀ ≤ (m : ℝ) := Nat.le_ceil _
    exact (div_le_iff₀ hL₀).mp hceil
  obtain ⟨hq, hcover⟩ := cubeCoverNumber_spec hexists
  apply cubeCoverNumber_min
  constructor
  · exact Nat.mul_pos (pow_pos hm k) hq
  · exact
      (hcover.replicate hm hq hL₀.le).restrict
        (hL₀.le.trans hL₀L) hLm

end BurningPath
