import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.CubeDensityLimit
import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.DiscreteContinuumComparison
import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.RankInterleaving
import Tengoku.Seed.Data.Fin.Tuple.Sort
import Tengoku.Seed.Data.Fintype.Perm
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Permuting ordered-simplex covers into cube covers

This module develops the rank-interleaving argument that permutes
ordered-simplex covers into cube covers.
-/

namespace BurningPath

/-- Move a point from the ordered chamber back through a coordinate permutation.-/
def permuteCoordinates {k : ℕ} (σ : Equiv.Perm (Fin k))
    (x : Fin k → ℝ) : Fin k → ℝ :=
  fun i ↦ x (σ.symm i)

/-- Coordinate permutation preserves the relevant `ℓ₁` distance.
@isnad1 id=eq.0h4v.s5.496f4323e933 from=translated src=- shape=b80acbac vocab=30761567
-/
theorem realL1Dist_permuteCoordinates {k : ℕ}
    (σ : Equiv.Perm (Fin k)) (x c : Fin k → ℝ) :
    realL1Dist x (permuteCoordinates σ c) =
      realL1Dist (x ∘ σ) c := by
  unfold realL1Dist
  calc
    ∑ i, |x i - permuteCoordinates σ c i| =
        ∑ i, |x (σ i) - permuteCoordinates σ c (σ i)| := by
      symm
      exact
        (Equiv.sum_comp σ
          (fun i : Fin k ↦ |x i - permuteCoordinates σ c i|))
    _ = ∑ i, |(x ∘ σ) i - c i| := by
      apply Finset.sum_congr rfl
      intro i _
      simp [permuteCoordinates]

/-- The sorted coordinate tuple of a cube point lies in the ordered simplex.
@isnad1 id=mem.1h3v.s6.053d3509856c from=translated src=- shape=3f8cb4e3 vocab=33f3e31f
-/
theorem comp_sort_mem_orderedSimplex {k : ℕ} {L : ℝ}
    {x : Fin k → ℝ} (hx : x ∈ realCube k L) :
    x ∘ Tuple.sort x ∈ orderedSimplex k L := by
  constructor
  · intro i
    exact hx (Tuple.sort x i)
  · exact Tuple.monotone_sort x

/--
Permute a legal simplex cover through all `k!` coordinate chambers and
interleave the local ranks.
@isnad1 id=hascuber.2h3v.s5.7d03c2ca0096 from=translated src=- shape=e7378dac vocab=7b75e6f5
-/
theorem HasSimplexRankedCover.toCubePermutationCover {k q : ℕ} {L : ℝ}
    (hq : 1 ≤ q) (hcover : HasSimplexRankedCover k L q) :
    HasCubeRankedCover k L (Nat.factorial k * q) := by
  classical
  obtain ⟨baseCenters, hbaseLegal, hbaseCover⟩ := hcover
  let Perm := Equiv.Perm (Fin k)
  let M := Fintype.card Perm
  let permEquiv : Perm ≃ Fin M := Fintype.equivFin Perm
  let centers : Fin M → Fin q → (Fin k → ℝ) :=
    fun a j ↦ permuteCoordinates (permEquiv.symm a) (baseCenters j)
  have hM : 1 ≤ M := Fintype.card_pos
  have hlegal : ∀ a j, centers a j ∈ realCube k L := by
    intro a j i
    exact (hbaseLegal j).1 ((permEquiv.symm a).symm i)
  have hpoint :
      ∀ x ∈ realCube k L, ∃ a : Fin M, ∃ j : Fin q,
        realL1Dist x (centers a j) ≤ (j.val : ℝ) / q := by
    intro x hx
    let σ := Tuple.sort x
    let y := x ∘ σ
    have hy : y ∈ orderedSimplex k L := comp_sort_mem_orderedSimplex hx
    obtain ⟨j, hj⟩ := hbaseCover y hy
    let a := permEquiv σ
    refine ⟨a, j, ?_⟩
    have hdist :=
      realL1Dist_permuteCoordinates σ x (baseCenters j)
    simpa [centers, a, y, σ] using hdist.trans_le hj
  have hinterleaved :
      HasL1NormalizedRankedCover (realCube k L) (M * q) :=
    hasL1NormalizedRankedCover_interleave hM hq centers hlegal hpoint
  simpa [HasCubeRankedCover, M, Perm, Fintype.card_perm] using hinterleaved

/-- The cube cover number is at most `k!` times the ordered-simplex cover number.
@isnad1 id=le.2h2v.s5.f6fbd8d685fe from=translated src=- shape=c063be1c vocab=e6f12a12
-/
theorem cubeCoverNumber_le_factorial_mul_simplexCoverNumber
    {k : ℕ} {L : ℝ} (hk : 1 ≤ k) (hL : 0 ≤ L) :
    cubeCoverNumber k L ≤ Nat.factorial k * simplexCoverNumber k L := by
  obtain ⟨hq, hcover⟩ :=
    simplexCoverNumber_spec (exists_simplexRankedCover hk hL)
  apply cubeCoverNumber_min
  exact
    ⟨Nat.mul_pos (Nat.factorial_pos k) hq,
      hcover.toCubePermutationCover hq⟩

/-- Normalized form of the permutation lower bound.
@isnad1 id=le.2h2v.s6.c429fa0e8d4e from=translated src=- shape=cb130d26 vocab=e3521fff
-/
theorem cubeDensity_le_simplexDensity {k : ℕ} {L : ℝ}
    (hk : 1 ≤ k) (hL : 0 < L) :
    cubeCoverDensityAt k L ≤
      (simplexCoverNumber k L : ℝ) /
        (L ^ k / Nat.factorial k) := by
  have hnum :=
    cubeCoverNumber_le_factorial_mul_simplexCoverNumber hk hL.le
  unfold cubeCoverDensityAt
  have hLpow : 0 < L ^ k := pow_pos hL k
  have hkfac : (0 : ℝ) < Nat.factorial k := by positivity
  calc
    (cubeCoverNumber k L : ℝ) / L ^ k ≤
        ((Nat.factorial k * simplexCoverNumber k L : ℕ) : ℝ) / L ^ k := by
      exact div_le_div_of_nonneg_right (by exact_mod_cast hnum) hLpow.le
    _ = (simplexCoverNumber k L : ℝ) /
        (L ^ k / Nat.factorial k) := by
      push_cast
      field_simp

end BurningPath
