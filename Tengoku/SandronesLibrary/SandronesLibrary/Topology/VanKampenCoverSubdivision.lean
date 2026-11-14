/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.PathHomotopyStandard
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.UnitIntervalMesh
import Tengoku.Seed.Topology.Subpath
import Tengoku.Seed.Topology.MetricSpace.Pseudo.Lemmas

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 二开集覆盖下的道路细分

本文件建立 van Kampen 论证所需的道路细分层：若一条道路的像逐点落在两个开集的并中，则存在
有限一致网格，使每个 Mathlib `Path.subpath` 的像完整落在其中一个开集。相邻段标签发生切换时，
公共网格顶点落在两个开集的交中；所有子道路用 Mathlib `Path.concat` 拼回原道路的全区间子道路，
并保持端点相对同伦。

当前条目：

* `topology.fundamental-group.van-kampen-cover-subdivision`。

本文件不构造基本群之间的典范映射，也不宣称 van Kampen 映射的满射、单射或同构。
-/

open Set
open scoped unitInterval

noncomputable section

namespace SandronesLibrary.Topology

variable {X : Type*} [TopologicalSpace X]

/-- 二元覆盖中由布尔标签选择的成员：`false` 选择 `U`，`true` 选择 `V`。

> **Entry**: topology.fundamental-group.van-kampen-cover-subdivision-/
def binaryOpenCoverPiece (U V : Set X) : Bool → Set X
  | false => U
  | true => V

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

namespace Path

/-- 道路的有限一致细分：每段由布尔值标记，并证明对应的 Mathlib 子道路完整留在所选覆盖成员中。-/
structure BinaryOpenCoverSubdivision {x y : X} (p : Path x y) (U V : Set X) where
  steps : ℕ
  steps_pos : 0 < steps
  label : Fin steps → Bool
  subpath_mem : ∀ i : Fin steps, ∀ u : unitInterval,
    p.subpath (unitIntervalMeshPoint steps steps_pos i.castSucc)
        (unitIntervalMeshPoint steps steps_pos i.succ) u ∈
      binaryOpenCoverPiece U V (label i)

/-- 两个相邻子道路的标签发生切换时，它们共享的网格顶点同时属于两个覆盖成员。
@isnad1 id=mem.2h9v.s7.0def42813cec from=translated src=- shape=eb450e12 vocab=d10fbdb3
-/
theorem BinaryOpenCoverSubdivision.switchVertex_mem_intersection
    {x y : X} {p : Path x y} {U V : Set X}
    (D : BinaryOpenCoverSubdivision p U V) (i j : Fin D.steps)
    (hshared : i.succ = j.castSucc) (hswitch : D.label i ≠ D.label j) :
    p (unitIntervalMeshPoint D.steps D.steps_pos i.succ) ∈ U ∩ V := by
  have hi := D.subpath_mem i 1
  have hj := D.subpath_mem j 0
  simp only [Path.subpath] at hi
  simp only [Path.subpath] at hj
  rw [← hshared] at hj
  cases hli : D.label i <;> cases hlj : D.label j <;>
    simp_all [binaryOpenCoverPiece]

/-- 每条带标签子道路的值域，正是原道路在相应闭网格区间上的像。
@isnad1 id=eq.0h8v.s8.e55ecc6c3b9b from=translated src=- shape=5cd99913 vocab=27f59bbf
-/
theorem BinaryOpenCoverSubdivision.subpath_range
    {x y : X} {p : Path x y} {U V : Set X}
    (D : BinaryOpenCoverSubdivision p U V) (i : Fin D.steps) :
    Set.range (p.subpath (unitIntervalMeshPoint D.steps D.steps_pos i.castSucc)
        (unitIntervalMeshPoint D.steps D.steps_pos i.succ)) =
      p '' Set.Icc (unitIntervalMeshPoint D.steps D.steps_pos i.castSucc)
        (unitIntervalMeshPoint D.steps D.steps_pos i.succ) := by
  exact Path.range_subpath_of_le _ _ _
    (unitIntervalMeshPoint_castSucc_le_succ D.steps D.steps_pos i)

/-- 按网格次序拼接全部 Mathlib 子道路，得到与原道路全区间子道路端点相对同伦的道路。
@isnad1 id=homotopi.0h7v.s8.2477c4bca900 from=translated src=- shape=1948af2b vocab=d69b0ab6
-/
theorem BinaryOpenCoverSubdivision.concatSubpaths_homotopic
    {x y : X} {p : Path x y} {U V : Set X}
    (D : BinaryOpenCoverSubdivision p U V) :
    Path.Homotopic
      (Path.concat
        (p ∘ unitIntervalMeshPoint D.steps D.steps_pos)
        (fun i => p.subpath
          (unitIntervalMeshPoint D.steps D.steps_pos i.castSucc)
          (unitIntervalMeshPoint D.steps D.steps_pos i.succ)))
      (p.subpath
        (unitIntervalMeshPoint D.steps D.steps_pos 0)
        (unitIntervalMeshPoint D.steps D.steps_pos (Fin.last D.steps))) := by
  exact Path.Homotopic.concat_subpath p (unitIntervalMeshPoint D.steps D.steps_pos)

/-- 若道路逐点落在两个开集之一，则它具有一个有限一致细分，使每条 Mathlib 子道路完整落在某个
选定的覆盖成员中。
@isnad1 id=nonempty.3h6v.s6.b685d234ab5f from=translated src=- shape=fff062d6 vocab=aa7a705c
-/
theorem exists_binaryOpenCoverSubdivision
    {x y : X} (p : Path x y) {U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V) (hp : ∀ t, p t ∈ U ∨ p t ∈ V) :
    Nonempty (BinaryOpenCoverSubdivision p U V) := by
  let C : Bool → Set unitInterval
    | false => p ⁻¹' U
    | true => p ⁻¹' V
  have hCopen : ∀ b, IsOpen (C b) := by
    intro b
    cases b
    · exact hU.preimage p.continuous
    · exact hV.preimage p.continuous
  have hCcover : (Set.univ : Set unitInterval) ⊆ ⋃ b, C b := by
    intro t _
    rcases hp t with ht | ht
    · exact Set.mem_iUnion.mpr ⟨false, ht⟩
    · exact Set.mem_iUnion.mpr ⟨true, ht⟩
  obtain ⟨δ, hδ, hball⟩ :=
    lebesgue_number_lemma_of_metric (s := (Set.univ : Set unitInterval))
      isCompact_univ hCopen hCcover
  obtain ⟨N, hN, hmesh⟩ := Real.exists_nat_pos_inv_lt hδ
  have hchoice : ∀ i : Fin N, ∃ b : Bool,
      Metric.ball (unitIntervalMeshPoint N hN i.castSucc) δ ⊆ C b := by
    intro i
    exact hball _ (Set.mem_univ _)
  let label : Fin N → Bool := fun i => Classical.choose (hchoice i)
  refine ⟨{
    steps := N
    steps_pos := hN
    label := label
    subpath_mem := ?_ }⟩
  intro i u
  have hdist :
      dist (Set.Icc.convexComb (unitIntervalMeshPoint N hN i.castSucc)
        (unitIntervalMeshPoint N hN i.succ) u)
        (unitIntervalMeshPoint N hN i.castSucc) < δ := by
    calc
      _ ≤ dist (unitIntervalMeshPoint N hN i.succ)
          (unitIntervalMeshPoint N hN i.castSucc) := dist_convexComb_left_le _ _ _
      _ = (N : ℝ)⁻¹ := by rw [dist_comm, dist_unitIntervalMeshPoint_castSucc_succ]
      _ < δ := hmesh
  have hmem := Classical.choose_spec (hchoice i) (Metric.mem_ball.mpr hdist)
  cases hli : label i <;>
    simpa [label, C, binaryOpenCoverPiece, Path.subpath, hli] using hmem

end Path

end SandronesLibrary.Topology
