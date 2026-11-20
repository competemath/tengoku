import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.SimplexDensityLower
import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.CubeDensityBounds
import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.FiniteNetCover
import Tengoku.Seed.Algebra.Order.Floor.Ring
import Tengoku.Seed.Data.Nat.Choose.Bounds
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Upper half of the ordered-simplex density comparison

The construction uses strictly ordered translates of one fixed cube cover.
The translates cover the simplex away from its top and coincidence walls.
A legal lattice mesh covers the remaining wall layer with only
surface-order many centers.
-/

open scoped BigOperators
open Filter

namespace BurningPath

private def lastIndex {k : ℕ} (hk : 1 ≤ k) : Fin k :=
  ⟨k - 1, by omega⟩

private def baseIndex {k : ℕ} (i : Fin (k - 1)) : Fin k :=
  ⟨i.1, by omega⟩

private def succIndex {k : ℕ} (i : Fin (k - 1)) : Fin k :=
  ⟨i.1 + 1, by omega⟩

private theorem baseIndex_lt_succIndex {k : ℕ} (i : Fin (k - 1)) :
    baseIndex i < succIndex i := by
  exact Fin.mk_lt_mk.mpr (by omega)

private abbrev MissingParam {k : ℕ} (p : Fin k) (N C : ℕ) :=
  ({j : Fin k // j ≠ p} → Fin (N + 1)) × Fin (C + 1)

private abbrev WallParam (k N C : ℕ) (hk : 1 ≤ k) :=
  MissingParam (lastIndex hk) N C ⊕
    Σ i : Fin (k - 1), MissingParam (succIndex i) N C

private def topRaw {k N C : ℕ} {hk : 1 ≤ k}
    (u : MissingParam (lastIndex hk) N C) : Fin k → ℕ :=
  fun j ↦
    if h : j = lastIndex hk then N - u.2.1
    else (u.1 ⟨j, h⟩).1

private def gapRaw {k N C : ℕ} (i : Fin (k - 1))
    (u : MissingParam (succIndex i) N C) : Fin k → ℕ :=
  fun j ↦
    if h : j = succIndex i then
      (u.1 ⟨baseIndex i, (baseIndex_lt_succIndex i).ne⟩).1 + u.2.1
    else (u.1 ⟨j, h⟩).1

private def rawWallParam {k N C : ℕ} {hk : 1 ≤ k}
    (u : WallParam k N C hk) : Fin k → ℕ :=
  match u with
  | Sum.inl v => topRaw v
  | Sum.inr v => gapRaw v.1 v.2

private def wallGamma {k N C : ℕ} {hk : 1 ≤ k}
    (u : WallParam k N C hk) : Gamma N k :=
  if h : Monotone (rawWallParam u) ∧ ∀ i, rawWallParam u i ≤ N then
    ⟨rawWallParam u, h⟩
  else
    ⟨0, monotone_const, by simp⟩

private noncomputable def gammaScale {N k D : ℕ}
    (z : Gamma N k) : Fin k → ℝ :=
  fun i ↦ (z.1 i : ℝ) / D

private noncomputable def floorToGamma {k D : ℕ} {L : ℝ}
    (x : Fin k → ℝ) (hx : x ∈ orderedSimplex k L) :
    Gamma ⌊(D : ℝ) * L⌋₊ k := by
  refine ⟨fun i ↦ ⌊(D : ℝ) * x i⌋₊, ?_, ?_⟩
  · intro i j hij
    exact Nat.floor_mono
      (mul_le_mul_of_nonneg_left (hx.2 hij) (by positivity))
  · intro i
    exact Nat.floor_mono
      (mul_le_mul_of_nonneg_left (hx.1 i).2 (by positivity))

private def simplexWallLayer {k : ℕ} (hk : 1 ≤ k) (ell L : ℝ) :
    Set (Fin k → ℝ) :=
  {x |
    L - x (lastIndex hk) ≤ ell ∨
      ∃ i : Fin (k - 1),
        x (succIndex i) - x (baseIndex i) ≤ ell}

private abbrev StrictCell (k p : ℕ) := Fin k ↪o Fin p

private def cellRegion {k p : ℕ} (ell : ℝ)
    (a : StrictCell k p) : Set (Fin k → ℝ) :=
  {x | ∀ i,
    (a i).1 * ell ≤ x i ∧
      x i ≤ ((a i).1 + 1 : ℕ) * ell}

private noncomputable def translatedCellCenter {k p q : ℕ}
    (ell : ℝ) (baseCenters : Fin q → (Fin k → ℝ))
    (a : StrictCell k p) (j : Fin q) : Fin k → ℝ :=
  fun i ↦ (a i).1 * ell + baseCenters j i

private def cellWallRankEmbedding (M q₀ A J : ℕ) (hM : 1 ≤ M) :
    ((Fin M × Fin q₀) ⊕ Fin J) ↪ Fin (A + 2 * J + M * q₀) where
  toFun u :=
    match u with
    | Sum.inl r =>
        ⟨A + 2 * J +
            (interleavedRankEmbedding M q₀ hM r).1, by
          have hr := (interleavedRankEmbedding M q₀ hM r).isLt
          omega⟩
    | Sum.inr s =>
        ⟨A + J + s.1, by omega⟩
  inj' := by
    intro u v huv
    rcases u with r | s <;> rcases v with r' | s'
    · simp only at huv
      congr 1
      apply (interleavedRankEmbedding M q₀ hM).injective
      apply Fin.ext
      have hval := congrArg Fin.val huv
      change
        A + 2 * J + (interleavedRankEmbedding M q₀ hM r).1 =
          A + 2 * J + (interleavedRankEmbedding M q₀ hM r').1 at hval
      omega
    · simp only at huv
      have hval := congrArg Fin.val huv
      change
        A + 2 * J + (interleavedRankEmbedding M q₀ hM r).1 =
          A + J + s'.1 at hval
      have hr := (interleavedRankEmbedding M q₀ hM r).isLt
      have hs := s'.isLt
      omega
    · simp only at huv
      have hval := congrArg Fin.val huv
      change
        A + J + s.1 =
          A + 2 * J + (interleavedRankEmbedding M q₀ hM r').1 at hval
      have hs := s.isLt
      have hr := (interleavedRankEmbedding M q₀ hM r').isLt
      omega
    · simp only at huv
      congr 1
      apply Fin.ext
      have hval := congrArg Fin.val huv
      change A + J + s.1 = A + J + s'.1 at hval
      omega

@[simp]
private theorem cellWallRankEmbedding_cell_val
    (M q₀ A J : ℕ) (hM : 1 ≤ M) (a : Fin M) (j : Fin q₀) :
    (cellWallRankEmbedding M q₀ A J hM (Sum.inl (a, j))).1 =
      A + 2 * J + (M * j.1 + a.1) :=
  rfl

@[simp]
private theorem cellWallRankEmbedding_wall_val
    (M q₀ A J : ℕ) (hM : 1 ≤ M) (s : Fin J) :
    (cellWallRankEmbedding M q₀ A J hM (Sum.inr s)).1 =
      A + J + s.1 :=
  rfl

private noncomputable def wallMeshScale (k : ℕ) (θ : ℝ) : ℕ :=
  ⌈4 * (k : ℝ) / θ⌉₊

private noncomputable def reserveRanks (θ : ℝ) (I : ℕ) : ℕ :=
  ⌈θ * I⌉₊

end BurningPath
