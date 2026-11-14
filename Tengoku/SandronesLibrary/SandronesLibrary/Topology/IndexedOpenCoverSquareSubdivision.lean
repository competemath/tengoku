/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.HomotopySquareGrid

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Dyadic square subdivisions subordinate to an indexed open cover.

> **Entry**: topology.homotopy.indexed-open-cover-square-subdivision -/

open Set
open scoped unitInterval

noncomputable section

namespace SandronesLibrary.Topology

variable {X : Type*} [TopologicalSpace X]

/-- Internal carrier for a uniform square grid labelled by an arbitrary indexed open cover.-/
private structure IndexedOpenCoverSquareSubdivision {ι : Type*}
    (H : C(unitInterval × unitInterval, X)) (W : ι → Set X) where
  steps : ℕ
  steps_pos : 0 < steps
  steps_dyadic : ∃ n : ℕ, steps = 2 ^ n
  label : Fin steps → Fin steps → ι
  cell_mem : ∀ i j u v,
    H (unitSquareCellPoint steps steps_pos i j u v) ∈ W (label i j)

private theorem dist_convexComb_left_le_indexed (a b u : unitInterval) :
    dist (Set.Icc.convexComb a b u) a ≤ dist b a := by
  rw [Subtype.dist_eq, Subtype.dist_eq, Real.dist_eq, Real.dist_eq]
  change
    |((1 - (u : ℝ)) * (a : ℝ) + (u : ℝ) * (b : ℝ)) - (a : ℝ)| ≤
      |(b : ℝ) - (a : ℝ)|
  rw [show ((1 - (u : ℝ)) * (a : ℝ) + (u : ℝ) * (b : ℝ)) - (a : ℝ) =
      (u : ℝ) * ((b : ℝ) - (a : ℝ)) by ring, abs_mul,
    abs_of_nonneg u.2.1]
  exact mul_le_of_le_one_left (abs_nonneg _) u.2.2

private theorem exists_dyadic_steps_inv_lt {δ : ℝ} (hδ : 0 < δ) :
    ∃ n : ℕ, (((2 ^ n : ℕ) : ℝ)⁻¹ < δ) := by
  obtain ⟨n, hn, hnmesh⟩ := Real.exists_nat_pos_inv_lt hδ
  have nat_le_two_pow : ∀ m : ℕ, m ≤ 2 ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        have hpow : 1 ≤ 2 ^ m := Nat.one_le_two_pow
        calc
          m + 1 ≤ 2 ^ m + 1 := Nat.add_le_add_right ih 1
          _ ≤ 2 ^ m + 2 ^ m := Nat.add_le_add_left hpow (2 ^ m)
          _ = 2 ^ (m + 1) := by simp [pow_succ, Nat.mul_two]
  have hnle : n ≤ 2 ^ n := nat_le_two_pow n
  refine ⟨n, lt_of_le_of_lt ?_ hnmesh⟩
  exact inv_anti₀ (by exact_mod_cast hn) (by exact_mod_cast hnle)

/-- Every indexed open cover of the square image has a uniformly meshed,
cellwise subordinate finite subdivision whose dyadic exponent is at least a prescribed depth.-/
private theorem exists_indexedOpenCoverSquareSubdivision_atLeastDepth {ι : Type*}
    (H : C(unitInterval × unitInterval, X)) (W : ι → Set X)
    (hW : ∀ k, IsOpen (W k)) (hH : ∀ z, ∃ k, H z ∈ W k)
    (minimumDepth : ℕ) :
    ∃ D : IndexedOpenCoverSquareSubdivision H W,
      ∃ n : ℕ, minimumDepth ≤ n ∧ D.steps = 2 ^ n := by
  let C : ι → Set (unitInterval × unitInterval) := fun k ↦ H ⁻¹' W k
  have hCopen : ∀ k, IsOpen (C k) := fun k ↦ (hW k).preimage H.continuous
  have hCcover : (Set.univ : Set (unitInterval × unitInterval)) ⊆ ⋃ k, C k := by
    intro z _
    obtain ⟨k, hk⟩ := hH z
    exact Set.mem_iUnion.mpr ⟨k, hk⟩
  obtain ⟨δ, hδ, hball⟩ :=
    lebesgue_number_lemma_of_metric
      (s := (Set.univ : Set (unitInterval × unitInterval)))
      isCompact_univ hCopen hCcover
  obtain ⟨n₀, hn₀mesh⟩ := exists_dyadic_steps_inv_lt hδ
  let n := max minimumDepth n₀
  have hn₀n : n₀ ≤ n := le_max_right _ _
  have hpow : 2 ^ n₀ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn₀n
  have hmesh : (((2 ^ n : ℕ) : ℝ)⁻¹ < δ) := by
    exact lt_of_le_of_lt
      (inv_anti₀ (by positivity) (by exact_mod_cast hpow)) hn₀mesh
  let N : ℕ := 2 ^ n
  have hN : 0 < N := by simp [N]
  have hchoice : ∀ i j : Fin N, ∃ k,
      Metric.ball
        (unitIntervalMeshPoint N hN i.castSucc,
          unitIntervalMeshPoint N hN j.castSucc) δ ⊆ C k := by
    intro i j
    exact hball _ (Set.mem_univ _)
  let label : Fin N → Fin N → ι := fun i j ↦ Classical.choose (hchoice i j)
  refine ⟨{
    steps := N
    steps_pos := hN
    steps_dyadic := ⟨n, rfl⟩
    label := label
    cell_mem := ?_ }, n, le_max_left _ _, rfl⟩
  intro i j u v
  have hx : dist
      (Set.Icc.convexComb (unitIntervalMeshPoint N hN i.castSucc)
        (unitIntervalMeshPoint N hN i.succ) u)
      (unitIntervalMeshPoint N hN i.castSucc) < δ := by
    calc
      _ ≤ dist (unitIntervalMeshPoint N hN i.succ)
          (unitIntervalMeshPoint N hN i.castSucc) :=
        dist_convexComb_left_le_indexed _ _ _
      _ = (N : ℝ)⁻¹ := by
        rw [dist_comm, dist_unitIntervalMeshPoint_castSucc_succ]
      _ < δ := hmesh
  have hy : dist
      (Set.Icc.convexComb (unitIntervalMeshPoint N hN j.castSucc)
        (unitIntervalMeshPoint N hN j.succ) v)
      (unitIntervalMeshPoint N hN j.castSucc) < δ := by
    calc
      _ ≤ dist (unitIntervalMeshPoint N hN j.succ)
          (unitIntervalMeshPoint N hN j.castSucc) :=
        dist_convexComb_left_le_indexed _ _ _
      _ = (N : ℝ)⁻¹ := by
        rw [dist_comm, dist_unitIntervalMeshPoint_castSucc_succ]
      _ < δ := hmesh
  have hdist : dist
      (unitSquareCellPoint N hN i j u v)
      (unitIntervalMeshPoint N hN i.castSucc,
        unitIntervalMeshPoint N hN j.castSucc) < δ := by
    simpa [unitSquareCellPoint, Prod.dist_eq, max_lt_iff] using And.intro hx hy
  exact Classical.choose_spec (hchoice i j) (Metric.mem_ball.mpr hdist)

/-- Consumer-facing dyadic data form: the cell indices are definitionally
`Fin (2^n)`, avoiding downstream transports through a stored `steps` field.-/
theorem exists_indexedOpenCoverSquareSubdivisionData_atLeastDepth {ι : Type*}
    (H : C(unitInterval × unitInterval, X)) (W : ι → Set X)
    (hW : ∀ k, IsOpen (W k)) (hH : ∀ z, ∃ k, H z ∈ W k)
    (minimumDepth : ℕ) :
    ∃ n : ℕ, minimumDepth ≤ n ∧
      ∃ label : Fin (2 ^ n) → Fin (2 ^ n) → ι,
        ∀ i j u v,
          H (unitSquareCellPoint (2 ^ n) (by positivity) i j u v) ∈ W (label i j) := by
  obtain ⟨D, n, hn, hsteps⟩ :=
    exists_indexedOpenCoverSquareSubdivision_atLeastDepth H W hW hH minimumDepth
  let castIndex : Fin (2 ^ n) → Fin D.steps := Fin.cast hsteps.symm
  let label : Fin (2 ^ n) → Fin (2 ^ n) → ι :=
    fun i j ↦ D.label (castIndex i) (castIndex j)
  refine ⟨n, hn, label, fun i j u v ↦ ?_⟩
  have hcell := D.cell_mem (castIndex i) (castIndex j) u v
  simpa [label, castIndex, unitSquareCellPoint, unitIntervalMeshPoint, hsteps] using hcell

end SandronesLibrary.Topology
