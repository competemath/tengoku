import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.RankPadding
import Tengoku.Seed.Algebra.Order.BigOperators.Group.Finset
import Tengoku.Seed.Data.Real.Basic
import Tengoku.Seed.Order.Lattice.Nat
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Normalized ranked covers in finite-dimensional `ℓ₁`

These definitions support the cube and ordered-simplex thermodynamic limits.
-/

open scoped BigOperators

namespace BurningPath

/-- The `ℓ₁` distance on real `k`-tuples.-/
def realL1Dist {k : ℕ} (x y : Fin k → ℝ) : ℝ :=
  ∑ i, |x i - y i|

@[simp]
theorem realL1Dist_self {k : ℕ} (x : Fin k → ℝ) :
    realL1Dist x x = 0 := by
  simp [realL1Dist]

theorem realL1Dist_nonneg {k : ℕ} (x y : Fin k → ℝ) :
    0 ≤ realL1Dist x y :=
  Finset.sum_nonneg fun _ _ ↦ abs_nonneg _

theorem realL1Dist_comm {k : ℕ} (x y : Fin k → ℝ) :
    realL1Dist x y = realL1Dist y x := by
  simp only [realL1Dist, abs_sub_comm]

theorem realL1Dist_triangle {k : ℕ} (x y z : Fin k → ℝ) :
    realL1Dist x z ≤ realL1Dist x y + realL1Dist y z := by
  simp only [realL1Dist, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  calc
    |x i - z i| = |(x i - y i) + (y i - z i)| := by ring_nf
    _ ≤ |x i - y i| + |y i - z i| := abs_add_le _ _

theorem realL1Dist_eq_zero_iff {k : ℕ} (x y : Fin k → ℝ) :
    realL1Dist x y = 0 ↔ x = y := by
  constructor
  · intro h
    funext i
    have hi :=
      (Finset.sum_eq_zero_iff_of_nonneg fun _ _ ↦ abs_nonneg _).mp h i (Finset.mem_univ i)
    exact sub_eq_zero.mp (abs_eq_zero.mp hi)
  · rintro rfl
    exact realL1Dist_self x

/-- The unit cross-polytope `C_k`.-/
def crossPolytope (k : ℕ) : Set (Fin k → ℝ) :=
  {x | realL1Dist x 0 ≤ 1}

/-- The cube `Q_L = [0,L]^k`.-/
def realCube (k : ℕ) (L : ℝ) : Set (Fin k → ℝ) :=
  {x | ∀ i, 0 ≤ x i ∧ x i ≤ L}

/-- The ordered simplex `Δ_L`.-/
def orderedSimplex (k : ℕ) (L : ℝ) : Set (Fin k → ℝ) :=
  {x | (∀ i, 0 ≤ x i ∧ x i ≤ L) ∧ Monotone x}

theorem orderedSimplex_subset_cube (k : ℕ) (L : ℝ) :
    orderedSimplex k L ⊆ realCube k L :=
  fun _ hx ↦ hx.1

@[simp]
theorem zero_mem_realCube {k : ℕ} {L : ℝ} (hL : 0 ≤ L) :
    (0 : Fin k → ℝ) ∈ realCube k L := by
  intro i
  simp [hL]

@[simp]
theorem zero_mem_orderedSimplex {k : ℕ} {L : ℝ} (hL : 0 ≤ L) :
    (0 : Fin k → ℝ) ∈ orderedSimplex k L := by
  exact ⟨fun i ↦ by simp [hL], monotone_const⟩

/--
A normalized ranked cover uses exactly the radii `0/q, 1/q, ..., (q-1)/q`, with every center
inside the region being covered.-/
def IsL1NormalizedRankedCover {k q : ℕ} (S : Set (Fin k → ℝ))
    (centers : Fin q → (Fin k → ℝ)) : Prop :=
  (∀ i, centers i ∈ S) ∧
    ∀ x ∈ S, ∃ i : Fin q, realL1Dist x (centers i) ≤ (i.1 : ℝ) / q

/-- A region has a normalized ranked cover of length `q`.-/
def HasL1NormalizedRankedCover {k : ℕ} (S : Set (Fin k → ℝ)) (q : ℕ) : Prop :=
  ∃ centers : Fin q → (Fin k → ℝ), IsL1NormalizedRankedCover S centers

/--
An order-preserving enlargement of the normalized radii lets a cover be reindexed into a longer
rank list; unused ranks receive an arbitrary legal center.-/
theorem IsL1NormalizedRankedCover.reindex {k q₀ q : ℕ} {S : Set (Fin k → ℝ)}
    {centers : Fin q₀ → (Fin k → ℝ)} (hcover : IsL1NormalizedRankedCover S centers)
    (hS : S.Nonempty) (e : Fin q₀ ↪ Fin q)
    (hradius : ∀ i, (i.1 : ℝ) / q₀ ≤ ((e i).1 : ℝ) / q) :
    ∃ fullCenters : Fin q → (Fin k → ℝ),
      IsL1NormalizedRankedCover S fullCenters ∧ ∀ i, fullCenters (e i) = centers i := by
  classical
  obtain ⟨defaultCenter, hdefaultCenter⟩ := hS
  let fullCenters : Fin q → (Fin k → ℝ) :=
    Function.extend e centers (fun _ ↦ defaultCenter)
  have hfull : ∀ i, fullCenters (e i) = centers i := by
    intro i
    exact e.injective.extend_apply centers (fun _ ↦ defaultCenter) i
  refine ⟨fullCenters, ?_, hfull⟩
  constructor
  · intro i
    by_cases hi : i ∈ Set.range e
    · obtain ⟨j, rfl⟩ := hi
      rw [hfull]
      exact hcover.1 j
    · change Function.extend e centers (fun _ ↦ defaultCenter) i ∈ S
      rw [Function.extend_apply' centers (fun _ ↦ defaultCenter) i]
      · exact hdefaultCenter
      · simpa only [Set.mem_range] using hi
  · intro x hx
    obtain ⟨i, hi⟩ := hcover.2 x hx
    refine ⟨e i, ?_⟩
    rw [hfull]
    exact hi.trans (hradius i)

/-- The ceiling rank-padding map pads every nonempty legal `ℓ₁` cover to a longer rank list.-/
theorem IsL1NormalizedRankedCover.pad {k q₀ q : ℕ} {S : Set (Fin k → ℝ)}
    {centers : Fin q₀ → (Fin k → ℝ)} (hcover : IsL1NormalizedRankedCover S centers)
    (hS : S.Nonempty) (hq₀ : 1 ≤ q₀) (hqq₀ : q₀ ≤ q) :
    ∃ fullCenters : Fin q → (Fin k → ℝ),
      IsL1NormalizedRankedCover S fullCenters ∧
        ∀ i, fullCenters (rankPaddingEmbedding q₀ q hq₀ hqq₀ i) = centers i := by
  exact hcover.reindex hS (rankPaddingEmbedding q₀ q hq₀ hqq₀)
    (rankPaddingEmbedding_normalized_le hq₀ hqq₀)

/-- Cube-cover existence at a given normalized rank length.-/
def HasCubeRankedCover (k : ℕ) (L : ℝ) (q : ℕ) : Prop :=
  HasL1NormalizedRankedCover (realCube k L) q

/-- Ordered-simplex-cover existence at a given normalized rank length.-/
def HasSimplexRankedCover (k : ℕ) (L : ℝ) (q : ℕ) : Prop :=
  HasL1NormalizedRankedCover (orderedSimplex k L) q

/-- The least positive normalized rank length covering `Q_L`.-/
noncomputable def cubeCoverNumber (k : ℕ) (L : ℝ) : ℕ :=
  sInf {q | 1 ≤ q ∧ HasCubeRankedCover k L q}

/-- The least positive normalized rank length covering `Δ_L` with legal centers.-/
noncomputable def simplexCoverNumber (k : ℕ) (L : ℝ) : ℕ :=
  sInf {q | 1 ≤ q ∧ HasSimplexRankedCover k L q}

/-- The variational bulk density `inf_{L>0} ν_k(L) / L^k`.-/
noncomputable def cubeBulkDensity (k : ℕ) : ℝ :=
  sInf {x | ∃ L : ℝ, 0 < L ∧ x = (cubeCoverNumber k L : ℝ) / L ^ k}

theorem cubeCoverNumber_spec {k : ℕ} {L : ℝ}
    (h : ∃ q, 1 ≤ q ∧ HasCubeRankedCover k L q) :
    1 ≤ cubeCoverNumber k L ∧ HasCubeRankedCover k L (cubeCoverNumber k L) :=
  Nat.sInf_mem h

theorem cubeCoverNumber_min {k q : ℕ} {L : ℝ}
    (hq : 1 ≤ q ∧ HasCubeRankedCover k L q) :
    cubeCoverNumber k L ≤ q :=
  Nat.sInf_le hq

theorem simplexCoverNumber_spec {k : ℕ} {L : ℝ}
    (h : ∃ q, 1 ≤ q ∧ HasSimplexRankedCover k L q) :
    1 ≤ simplexCoverNumber k L ∧
      HasSimplexRankedCover k L (simplexCoverNumber k L) :=
  Nat.sInf_mem h

theorem simplexCoverNumber_min {k q : ℕ} {L : ℝ}
    (hq : 1 ≤ q ∧ HasSimplexRankedCover k L q) :
    simplexCoverNumber k L ≤ q :=
  Nat.sInf_le hq

/-- Rank padding makes cube-cover feasibility upward closed.-/
theorem HasCubeRankedCover.mono {k q₀ q : ℕ} {L : ℝ} (hL : 0 ≤ L)
    (hq₀ : 1 ≤ q₀) (hqq₀ : q₀ ≤ q) (hcover : HasCubeRankedCover k L q₀) :
    HasCubeRankedCover k L q := by
  obtain ⟨centers, hcenters⟩ := hcover
  obtain ⟨fullCenters, hfull, _⟩ :=
    hcenters.pad ⟨0, zero_mem_realCube hL⟩ hq₀ hqq₀
  exact ⟨fullCenters, hfull⟩

/-- Rank padding makes ordered-simplex-cover feasibility upward closed.-/
theorem HasSimplexRankedCover.mono {k q₀ q : ℕ} {L : ℝ} (hL : 0 ≤ L)
    (hq₀ : 1 ≤ q₀) (hqq₀ : q₀ ≤ q) (hcover : HasSimplexRankedCover k L q₀) :
    HasSimplexRankedCover k L q := by
  obtain ⟨centers, hcenters⟩ := hcover
  obtain ⟨fullCenters, hfull, _⟩ :=
    hcenters.pad ⟨0, zero_mem_orderedSimplex hL⟩ hq₀ hqq₀
  exact ⟨fullCenters, hfull⟩

end BurningPath
