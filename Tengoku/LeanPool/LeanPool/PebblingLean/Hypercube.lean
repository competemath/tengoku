/-
Copyright (c) 2026 Lior Pachter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lior Pachter
-/
module

public import Tengoku.LeanPool.LeanPool.PebblingLean.Basic
public import Tengoku

/-!
# Hypercubes

The `n`-dimensional hypercube is represented as Boolean coordinate functions
`Fin n → Bool`. Two vertices are adjacent when they differ in exactly one
coordinate.
-/

@[expose] public section

namespace PebblingLean

/-- Vertices of the `n`-cube. -/
abbrev HypercubeVertex (n : ℕ) := Fin n → Bool

namespace Hypercube

/--
@isnad1 id=eq.0h1v.s5.53a379db1bea from=translated src=- shape=5b09d1d5 vocab=9a8d3fff
-/
theorem card_vertex (n : ℕ) : Fintype.card (HypercubeVertex n) = 2 ^ n := by
  simp [HypercubeVertex]

/-- Hamming distance on Boolean coordinate functions. -/
def dist {n : ℕ} (x y : HypercubeVertex n) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => x i ≠ y i)).card

/-- Coordinates on which two hypercube vertices differ. -/
def diffSet {n : ℕ} (x y : HypercubeVertex n) : Finset (Fin n) :=
  Finset.univ.filter (fun i : Fin n => x i ≠ y i)

/--
@isnad1 id=eq.0h3v.s4.c360bf8b1cdf from=translated src=- shape=b36fdc16 vocab=47bc3968
-/
theorem dist_eq_card_diffSet {n : ℕ} (x y : HypercubeVertex n) :
    dist x y = (diffSet x y).card := by
  rfl

/-- Hamming distance in `Q_n` is at most `n`.
@isnad1 id=le.0h3v.s4.ae62dc11a5b8 from=translated src=- shape=a427f74f vocab=28a32ade
-/
theorem dist_le {n : ℕ} (x y : HypercubeVertex n) : dist x y ≤ n := by
  unfold dist
  calc
    (Finset.univ.filter fun i : Fin n => x i ≠ y i).card ≤
        (Finset.univ : Finset (Fin n)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = n := by
      simp

/-- The vertex obtained from `base` by flipping exactly the coordinates in
`s`. -/
def fromDiffSet {n : ℕ} (base : HypercubeVertex n) (s : Finset (Fin n)) :
    HypercubeVertex n :=
  fun i => if i ∈ s then Bool.not (base i) else base i

/--
@isnad1 id=eq.0h3v.s4.020eb3d8109f from=translated src=- shape=4661ae63 vocab=b3c1c2c0
-/
@[simp]
theorem diffSet_fromDiffSet {n : ℕ} (base : HypercubeVertex n) (s : Finset (Fin n)) :
    diffSet base (fromDiffSet base s) = s := by
  ext i
  by_cases hi : i ∈ s <;> simp [diffSet, fromDiffSet, hi]

/--
@isnad1 id=eq.0h3v.s4.17789cc2ffa3 from=translated src=- shape=a1f2d8cb vocab=3cdb85de
-/
@[simp]
theorem fromDiffSet_diffSet {n : ℕ} (base v : HypercubeVertex n) :
    fromDiffSet base (diffSet base v) = v := by
  funext i
  by_cases hsame : base i = v i
  · have hnot : i ∉ diffSet base v := by
      simp [diffSet, hsame]
    simp [fromDiffSet, hnot, hsame]
  · have hin : i ∈ diffSet base v := by
      simp [diffSet, hsame]
    have hflip : Bool.not (base i) = v i := by
      exact (Bool.eq_not_iff.mpr (Ne.symm hsame)).symm
    simp [fromDiffSet, hin, hflip]

/-- Vertices of `Q_n` are equivalent to subsets of coordinates, by recording
where they differ from a fixed base vertex. -/
def diffSetEquiv {n : ℕ} (base : HypercubeVertex n) :
    HypercubeVertex n ≃ Finset (Fin n) where
  toFun := diffSet base
  invFun := fromDiffSet base
  left_inv := fromDiffSet_diffSet base
  right_inv := diffSet_fromDiffSet base

/-- The Hamming sphere of radius `k` around any fixed hypercube vertex has
cardinality `n choose k`.
@isnad1 id=eq.0h3v.s5.4bb74de20e0c from=translated src=- shape=462c1cb2 vocab=2ed8ba5a
-/
theorem card_sphere {n : ℕ} (base : HypercubeVertex n) (k : ℕ) :
    Fintype.card {v : HypercubeVertex n // dist base v = k} = Nat.choose n k := by
  classical
  let e :
      {v : HypercubeVertex n // dist base v = k} ≃
        {s : Finset (Fin n) // s.card = k} :=
    (diffSetEquiv base).subtypeEquiv (fun v => by
      change dist base v = k ↔ (diffSet base v).card = k
      simp [dist_eq_card_diffSet])
  calc
    Fintype.card {v : HypercubeVertex n // dist base v = k}
        = Fintype.card {s : Finset (Fin n) // s.card = k} := by
          exact Fintype.card_congr e
    _ = Nat.choose n k := by
          simp

/--
@isnad1 id=eq.0h2v.s4.0dd6e0793f37 from=translated src=- shape=fc61c6a6 vocab=dbc59d27
-/
@[simp]
theorem dist_self {n : ℕ} (x : HypercubeVertex n) : dist x x = 0 := by
  simp [dist]

/--
@isnad1 id=iff.0h3v.s4.82d55bbc4317 from=translated src=- shape=b2a84df1 vocab=dbc59d27
-/
theorem dist_eq_zero_iff {n : ℕ} {x y : HypercubeVertex n} :
    dist x y = 0 ↔ x = y := by
  constructor
  · intro hdist
    funext i
    by_contra hne
    have hempty :
        (Finset.univ.filter fun i : Fin n => x i ≠ y i) = ∅ := by
      exact Finset.card_eq_zero.mp hdist
    simp_all
  · simp_all

/--
@isnad1 id=eq.0h3v.s4.b4864d9904db from=translated src=- shape=9ee3e7a7 vocab=dbc59d27
-/
theorem dist_comm {n : ℕ} (x y : HypercubeVertex n) : dist x y = dist y x := by
  simp [dist, ne_comm]

/-- Hamming distance satisfies the triangle inequality.
@isnad1 id=le.0h4v.s5.3cea5aaac492 from=translated src=- shape=cdbbb858 vocab=04f982a0
-/
theorem dist_triangle {n : ℕ} (x y z : HypercubeVertex n) :
    dist x z ≤ dist x y + dist y z := by
  classical
  unfold dist
  apply (Finset.card_mono ?_).trans
  · exact Finset.card_union_le _ _
  intro i hi
  rw [Finset.mem_filter] at hi
  rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
  by_cases hxy : x i = y i
  · simp_all
  · simp_all

/-- The `n`-dimensional hypercube graph. -/
def graph (n : ℕ) : Graph (HypercubeVertex n) where
  Adj x y := dist x y = 1
  symm := by
    intro x y h
    rw [dist_comm x y] at h
    exact h
  loopless := by
    simp_all

/-- Adjacent hypercube vertices have distances to any third vertex that differ
by at most one in this direction.
@isnad1 id=le.1h4v.s5.88a9c4984824 from=translated src=- shape=4f362d71 vocab=37bc81fd
-/
theorem dist_adj_le_succ {n : ℕ} {x y t : HypercubeVertex n}
    (hxy : (graph n).Adj x y) : dist x t ≤ dist y t + 1 := by
  have h := dist_triangle x y t
  rw [hxy] at h
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

end Hypercube

end PebblingLean
