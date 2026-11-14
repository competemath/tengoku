/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.VanKampenCoverSubdivision
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.HomotopySquareGrid

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 二开集覆盖下的方格细分

本文件建立 van Kampen 单射论证所需的二维细分层：若连续方形逐点落在两个开集之一，则存在有限
一致方格网格，使每个闭方格的像完整落在一个带 Bool 标签的覆盖成员中。水平或竖直相邻方格的
标签切换时，它们的整条公共边都映入两个开集的交。

当前条目：

* `topology.fundamental-group.van-kampen-square-subdivision`。

本文件不构造方格边界词，不证明内部边抵消、规范同态单射或完整 Seifert--van Kampen 定理。
-/

open Set
open scoped unitInterval

noncomputable section

namespace SandronesLibrary.Topology

variable {X : Type*} [TopologicalSpace X]

private theorem dist_convexComb_left_le (a b u : unitInterval) :
    dist (Set.Icc.convexComb a b u) a ≤ dist b a := by
  rw [Subtype.dist_eq, Subtype.dist_eq, Real.dist_eq, Real.dist_eq]
  change
    |((1 - (u : ℝ)) * (a : ℝ) + (u : ℝ) * (b : ℝ)) - (a : ℝ)| ≤
      |(b : ℝ) - (a : ℝ)|
  rw [show ((1 - (u : ℝ)) * (a : ℝ) + (u : ℝ) * (b : ℝ)) - (a : ℝ) =
      (u : ℝ) * ((b : ℝ) - (a : ℝ)) by ring, abs_mul,
    abs_of_nonneg u.2.1]
  exact mul_le_of_le_one_left (abs_nonneg _) u.2.2

/-- 二开集覆盖下的有限一致方格细分，每个闭方格整体落在一个覆盖成员中。

> **Entry**: topology.fundamental-group.van-kampen-square-subdivision-/
structure BinaryOpenCoverSquareSubdivision (H : C(unitInterval × unitInterval, X))
    (U V : Set X) where
  steps : ℕ
  steps_pos : 0 < steps
  label : Fin steps → Fin steps → Bool
  cell_mem : ∀ i j u v,
    H (unitSquareCellPoint steps steps_pos i j u v) ∈
      binaryOpenCoverPiece U V (label i j)

/-- 连续方形逐点落在二开集之一时，存在每个闭方格都落在单个覆盖成员中的一致有限细分。
@isnad1 id=nonempty.3h4v.s8.72b67e442357 from=translated src=- shape=957777a8 vocab=94d9a8a6
-/
theorem exists_binaryOpenCoverSquareSubdivision
    (H : C(unitInterval × unitInterval, X)) {U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V)
    (hH : ∀ z, H z ∈ U ∨ H z ∈ V) :
    Nonempty (BinaryOpenCoverSquareSubdivision H U V) := by
  let C : Bool → Set (unitInterval × unitInterval)
    | false => H ⁻¹' U
    | true => H ⁻¹' V
  have hCopen : ∀ b, IsOpen (C b) := by
    intro b
    cases b
    · exact hU.preimage H.continuous
    · exact hV.preimage H.continuous
  have hCcover : (Set.univ : Set (unitInterval × unitInterval)) ⊆ ⋃ b, C b := by
    intro z _
    rcases hH z with hz | hz
    · exact Set.mem_iUnion.mpr ⟨false, hz⟩
    · exact Set.mem_iUnion.mpr ⟨true, hz⟩
  obtain ⟨δ, hδ, hball⟩ :=
    lebesgue_number_lemma_of_metric
      (s := (Set.univ : Set (unitInterval × unitInterval)))
      isCompact_univ hCopen hCcover
  obtain ⟨N, hN, hmesh⟩ := Real.exists_nat_pos_inv_lt hδ
  have hchoice : ∀ i j : Fin N, ∃ b : Bool,
      Metric.ball
        (unitIntervalMeshPoint N hN i.castSucc,
          unitIntervalMeshPoint N hN j.castSucc) δ ⊆ C b := by
    intro i j
    exact hball _ (Set.mem_univ _)
  let label : Fin N → Fin N → Bool := fun i j => Classical.choose (hchoice i j)
  refine ⟨{
    steps := N
    steps_pos := hN
    label := label
    cell_mem := ?_ }⟩
  intro i j u v
  have hx : dist
      (Set.Icc.convexComb (unitIntervalMeshPoint N hN i.castSucc)
        (unitIntervalMeshPoint N hN i.succ) u)
      (unitIntervalMeshPoint N hN i.castSucc) < δ := by
    calc
      _ ≤ dist (unitIntervalMeshPoint N hN i.succ)
          (unitIntervalMeshPoint N hN i.castSucc) := dist_convexComb_left_le _ _ _
      _ = (N : ℝ)⁻¹ := by
        rw [dist_comm, dist_unitIntervalMeshPoint_castSucc_succ]
      _ < δ := hmesh
  have hy : dist
      (Set.Icc.convexComb (unitIntervalMeshPoint N hN j.castSucc)
        (unitIntervalMeshPoint N hN j.succ) v)
      (unitIntervalMeshPoint N hN j.castSucc) < δ := by
    calc
      _ ≤ dist (unitIntervalMeshPoint N hN j.succ)
          (unitIntervalMeshPoint N hN j.castSucc) := dist_convexComb_left_le _ _ _
      _ = (N : ℝ)⁻¹ := by
        rw [dist_comm, dist_unitIntervalMeshPoint_castSucc_succ]
      _ < δ := hmesh
  have hdist : dist
      (unitSquareCellPoint N hN i j u v)
      (unitIntervalMeshPoint N hN i.castSucc,
        unitIntervalMeshPoint N hN j.castSucc) < δ := by
    simpa [unitSquareCellPoint, Prod.dist_eq, max_lt_iff] using And.intro hx hy
  have hmem := Classical.choose_spec (hchoice i j) (Metric.mem_ball.mpr hdist)
  cases hlabel : label i j <;>
    simpa [label, C, binaryOpenCoverPiece, hlabel] using hmem

/-- 水平相邻方格标签不同时，它们的整条公共竖边都映入交集。
@isnad1 id=mem.2h9v.s8.e744442c11f3 from=translated src=- shape=73b2bf1e vocab=1f36677e
-/
theorem BinaryOpenCoverSquareSubdivision.horizontalSwitchEdge_mem_intersection
    {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (hswitch : D.label i j ≠ D.label k j) (v : unitInterval) :
    H (unitIntervalMeshPoint D.steps D.steps_pos i.succ,
      Set.Icc.convexComb (unitIntervalMeshPoint D.steps D.steps_pos j.castSucc)
        (unitIntervalMeshPoint D.steps D.steps_pos j.succ) v) ∈ U ∩ V := by
  have hi := D.cell_mem i j 1 v
  have hk := D.cell_mem k j 0 v
  simp only [unitSquareCellPoint, Set.Icc.convexComb_one, Set.Icc.convexComb_zero] at hi hk
  rw [← hshared] at hk
  cases hli : D.label i j <;> cases hlk : D.label k j <;>
    simp_all [binaryOpenCoverPiece]

/-- 竖直相邻方格标签不同时，它们的整条公共横边都映入交集。
@isnad1 id=mem.2h9v.s8.a0b7a3fe2834 from=translated src=- shape=0e603426 vocab=1f36677e
-/
theorem BinaryOpenCoverSquareSubdivision.verticalSwitchEdge_mem_intersection
    {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (hswitch : D.label i j ≠ D.label i l) (u : unitInterval) :
    H (Set.Icc.convexComb (unitIntervalMeshPoint D.steps D.steps_pos i.castSucc)
        (unitIntervalMeshPoint D.steps D.steps_pos i.succ) u,
      unitIntervalMeshPoint D.steps D.steps_pos j.succ) ∈ U ∩ V := by
  have hj := D.cell_mem i j u 1
  have hl := D.cell_mem i l u 0
  simp only [unitSquareCellPoint, Set.Icc.convexComb_one, Set.Icc.convexComb_zero] at hj hl
  rw [← hshared] at hl
  cases hlj : D.label i j <;> cases hll : D.label i l <;>
    simp_all [binaryOpenCoverPiece]

end SandronesLibrary.Topology
