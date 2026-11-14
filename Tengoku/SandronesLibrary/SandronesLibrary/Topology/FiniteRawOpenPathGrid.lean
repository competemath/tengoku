/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.PiecewiseC1Path
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.HomotopySquareGrid

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! A topology-owned finite raw path grid in a real normed vector space.

> **Entry**: topology.homotopy.finite-raw-open-path-grid -/

open Set
open scoped unitInterval

noncomputable section

namespace SandronesLibrary.Topology

/-- Native finite raw grid matching the indices of a square subdivision. The
carrier is an arbitrary real normed vector space; complex analysis enters only
when local primitives are attached later.-/
structure FiniteRawOpenPathGrid (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] where
  steps : ℕ
  vertex : Fin (steps + 1) → Fin (steps + 1) → E
  cellSet : Fin steps → Fin steps → Set E
  cellSet_open : ∀ i j, IsOpen (cellSet i j)
  horizontalRaw : (i : Fin steps) → (j : Fin (steps + 1)) →
    Path (vertex i.castSucc j) (vertex i.succ j)
  verticalRaw : (i : Fin (steps + 1)) → (j : Fin steps) →
    Path (vertex i j.castSucc) (vertex i j.succ)
  bottom_mem : ∀ i j, Set.range (horizontalRaw i j.castSucc) ⊆ cellSet i j
  right_mem : ∀ i j, Set.range (verticalRaw i.succ j) ⊆ cellSet i j
  top_mem : ∀ i j, Set.range (horizontalRaw i j.succ) ⊆ cellSet i j
  left_mem : ∀ i j, Set.range (verticalRaw i.castSucc j) ⊆ cellSet i j
  horizontal_zero_piecewiseC1 : ∀ i, Path.PiecewiseC1 (horizontalRaw i 0)
  horizontal_last_piecewiseC1 : ∀ i,
    Path.PiecewiseC1 (horizontalRaw i (Fin.last steps))
  vertical_zero_piecewiseC1 : ∀ j, Path.PiecewiseC1 (verticalRaw 0 j)
  vertical_last_piecewiseC1 : ∀ j,
    Path.PiecewiseC1 (verticalRaw (Fin.last steps) j)

/-- Adapter from the exact data fields of an indexed square subdivision to the
native finite raw path grid. It is stated on the fields so the research files
remain independently compilable.-/
def finiteRawOpenPathGrid_of_squareSubdivisionData
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : C(unitInterval × unitInterval, E)) (steps : ℕ) (hsteps : 0 < steps)
    {ι : Type*} (W : ι → Set E) (label : Fin steps → Fin steps → ι)
    (hW : ∀ k, IsOpen (W k))
    (cell_mem : ∀ i j u v,
      H (unitSquareCellPoint steps hsteps i j u v) ∈ W (label i j))
    (horizontal_zero_piecewiseC1 : ∀ i,
      Path.PiecewiseC1 (squareGridHorizontalEdge H steps hsteps i 0))
    (horizontal_last_piecewiseC1 : ∀ i,
      Path.PiecewiseC1
        (squareGridHorizontalEdge H steps hsteps i (Fin.last steps)))
    (vertical_zero_piecewiseC1 : ∀ j,
      Path.PiecewiseC1 (squareGridVerticalEdge H steps hsteps 0 j))
    (vertical_last_piecewiseC1 : ∀ j,
      Path.PiecewiseC1
        (squareGridVerticalEdge H steps hsteps (Fin.last steps) j)) :
    FiniteRawOpenPathGrid E := {
  steps := steps
  vertex := squareGridVertex H steps hsteps
  cellSet := fun i j ↦ W (label i j)
  cellSet_open := fun i j ↦ hW (label i j)
  horizontalRaw := squareGridHorizontalEdge H steps hsteps
  verticalRaw := squareGridVerticalEdge H steps hsteps
  bottom_mem := by
    intro i j z hz
    obtain ⟨u, rfl⟩ := hz
    change H
      (Set.Icc.convexComb (unitIntervalMeshPoint steps hsteps i.castSucc)
        (unitIntervalMeshPoint steps hsteps i.succ) u,
        unitIntervalMeshPoint steps hsteps j.castSucc) ∈ W (label i j)
    simpa [unitSquareCellPoint] using cell_mem i j u 0
  right_mem := by
    intro i j z hz
    obtain ⟨v, rfl⟩ := hz
    change H
      (unitIntervalMeshPoint steps hsteps i.succ,
        Set.Icc.convexComb (unitIntervalMeshPoint steps hsteps j.castSucc)
          (unitIntervalMeshPoint steps hsteps j.succ) v) ∈ W (label i j)
    simpa [unitSquareCellPoint] using cell_mem i j 1 v
  top_mem := by
    intro i j z hz
    obtain ⟨u, rfl⟩ := hz
    change H
      (Set.Icc.convexComb (unitIntervalMeshPoint steps hsteps i.castSucc)
        (unitIntervalMeshPoint steps hsteps i.succ) u,
        unitIntervalMeshPoint steps hsteps j.succ) ∈ W (label i j)
    simpa [unitSquareCellPoint] using cell_mem i j u 1
  left_mem := by
    intro i j z hz
    obtain ⟨v, rfl⟩ := hz
    change H
      (unitIntervalMeshPoint steps hsteps i.castSucc,
        Set.Icc.convexComb (unitIntervalMeshPoint steps hsteps j.castSucc)
          (unitIntervalMeshPoint steps hsteps j.succ) v) ∈ W (label i j)
    simpa [unitSquareCellPoint] using cell_mem i j 0 v
  horizontal_zero_piecewiseC1 := horizontal_zero_piecewiseC1
  horizontal_last_piecewiseC1 := horizontal_last_piecewiseC1
  vertical_zero_piecewiseC1 := vertical_zero_piecewiseC1
  vertical_last_piecewiseC1 := vertical_last_piecewiseC1 }

end SandronesLibrary.Topology
