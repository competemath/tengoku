/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.PathHomotopyImageControl
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.UnitIntervalMesh
import Tengoku.Seed.Topology.UniformSpace.HeineCantor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 开集内道路的相对折线逼近

本文件证明实赋范线性空间中落在开集内的连续道路，可以在同一开集内、相对端点同伦到一个由有限
条直线段拼接成的道路。证明先用紧性和一致连续性取得统一网格及逐段公共凸球，再在每段内作仿射
直线化，最后用带像集证书的有限同伦拼接组装整体结果。

当前条目：

* `topology.homotopy.path-polygonal-approximation`。

本文件不宣称同伦或折线路径光滑，也不证明线积分不变。
-/

open Set
open scoped unitInterval Convex

noncomputable section

namespace SandronesLibrary.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {X : Type*} [TopologicalSpace X]

private theorem dist_unitInterval_convexComb_left_le
    (a b u : unitInterval) :
    dist (Set.Icc.convexComb a b u) a ≤ dist b a := by
  rw [Subtype.dist_eq, Subtype.dist_eq, Real.dist_eq, Real.dist_eq]
  change
    |((1 - (u : ℝ)) * (a : ℝ) + (u : ℝ) * (b : ℝ)) - (a : ℝ)| ≤
      |(b : ℝ) - (a : ℝ)|
  rw [show ((1 - (u : ℝ)) * (a : ℝ) + (u : ℝ) * (b : ℝ)) - (a : ℝ) =
      (u : ℝ) * ((b : ℝ) - (a : ℝ)) by ring, abs_mul,
    abs_of_nonneg u.2.1]
  exact mul_le_of_le_one_left (abs_nonneg _) u.2.2

/-- 一致有限网格及各原子道路段与直线替换共享的凸球证书；每个球都包含于 `U`。

> **Entry**: topology.homotopy.path-polygonal-approximation-/
structure Path.MeshBallSubdivision {x y : E} (p : Path x y) (U : Set E) where
  steps : ℕ
  steps_pos : 0 < steps
  radius : ℝ
  radius_pos : 0 < radius
  path_mem : ∀ t : unitInterval, p t ∈ U
  ball_subset : ∀ i : Fin steps,
    Metric.ball (p (unitIntervalMeshPoint steps steps_pos i.castSucc)) radius ⊆ U
  subpath_mem : ∀ i : Fin steps, ∀ u : unitInterval,
    p.subpath (unitIntervalMeshPoint steps steps_pos i.castSucc)
        (unitIntervalMeshPoint steps steps_pos i.succ) u ∈
      Metric.ball (p (unitIntervalMeshPoint steps steps_pos i.castSucc)) radius
  segment_mem : ∀ i : Fin steps, ∀ u : unitInterval,
    Path.segment
        (p (unitIntervalMeshPoint steps steps_pos i.castSucc))
        (p (unitIntervalMeshPoint steps steps_pos i.succ)) u ∈
      Metric.ball (p (unitIntervalMeshPoint steps steps_pos i.castSucc)) radius

/-- 紧性与一致连续性在任何包含道路像的开集内给出带公共球半径的有限网格细分。-/
theorem Path.exists_meshBallSubdivision {x y : E} (p : Path x y)
    {U : Set E} (hU : IsOpen U) (hpU : ∀ t, p t ∈ U) :
    Nonempty (SandronesLibrary.Topology.Path.MeshBallSubdivision p U) := by
  have hK : IsCompact (Set.range p) := isCompact_range p.continuous
  obtain ⟨δ, hδpos, hδU⟩ :=
    hK.exists_cthickening_subset_open hU (Set.range_subset_iff.mpr hpU)
  have hpUC : UniformContinuous p :=
    CompactSpace.uniformContinuous_of_continuous p.continuous
  obtain ⟨η, hηpos, hcontrol⟩ :=
    Metric.uniformContinuous_iff.mp hpUC δ hδpos
  obtain ⟨N, hN, hmesh⟩ := Real.exists_nat_pos_inv_lt hηpos
  refine ⟨{
    steps := N
    steps_pos := hN
    radius := δ
    radius_pos := hδpos
    path_mem := hpU
    ball_subset := ?_
    subpath_mem := ?_
    segment_mem := ?_ }⟩
  · intro i z hz
    apply hδU
    exact Metric.mem_cthickening_of_dist_le z
      (p (unitIntervalMeshPoint N hN i.castSucc)) δ (Set.range p)
      ⟨unitIntervalMeshPoint N hN i.castSucc, rfl⟩ (le_of_lt hz)
  · intro i u
    let a := unitIntervalMeshPoint N hN i.castSucc
    let b := unitIntervalMeshPoint N hN i.succ
    have htime : dist (Set.Icc.convexComb a b u) a < η := by
      calc
        _ ≤ dist b a := dist_unitInterval_convexComb_left_le a b u
        _ = (N : ℝ)⁻¹ := by
          rw [dist_comm, dist_unitIntervalMeshPoint_castSucc_succ]
        _ < η := hmesh
    exact hcontrol htime
  · intro i u
    let a := unitIntervalMeshPoint N hN i.castSucc
    let b := unitIntervalMeshPoint N hN i.succ
    have habTime : dist a b < η := by
      rw [dist_unitIntervalMeshPoint_castSucc_succ]
      exact hmesh
    have hab : p b ∈ Metric.ball (p a) δ := by
      simpa [Metric.mem_ball, dist_comm] using hcontrol habTime
    exact (convex_ball (p a) δ).lineMap_mem
      (Metric.mem_ball_self hδpos) hab u.2

/-- 若道路像位于开集中，则存在正的一致网格，使每对相邻样本点之间的直线段仍位于该开集。-/
theorem Path.exists_mesh_segments_subset_open {x y : E} (p : Path x y)
    {U : Set E} (hU : IsOpen U) (hpU : ∀ t, p t ∈ U) :
    ∃ N : ℕ, ∃ hN : 0 < N, ∀ i : Fin N,
      Set.range (Path.segment
        (p (unitIntervalMeshPoint N hN i.castSucc))
        (p (unitIntervalMeshPoint N hN i.succ))) ⊆ U := by
  obtain ⟨D⟩ := SandronesLibrary.Topology.Path.exists_meshBallSubdivision p hU hpU
  refine ⟨D.steps, D.steps_pos, ?_⟩
  intro i z hz
  rcases hz with ⟨u, rfl⟩
  exact D.ball_subset i (D.segment_mem i u)

/-- 用 Mathlib 直线段依次连接 `p` 的一致网格样本点，得到有限折线道路。-/
def Path.meshPolygonal {x y : E} (p : Path x y) (N : ℕ) (hN : 0 < N) :
    Path x y :=
  (Path.concat
    (p ∘ unitIntervalMeshPoint N hN)
    (fun i ↦ Path.segment
      (p (unitIntervalMeshPoint N hN i.castSucc))
      (p (unitIntervalMeshPoint N hN i.succ)))).cast
    (by simp) (by simp)

/-- 网格折线道路的公开一步展开：先用有限 `Path.concat` 拼接连结相邻一致网格样本点的
`Path.segment`，最后只作端点类型转换。-/
theorem Path.meshPolygonal_eq_concat {x y : E} (p : Path x y)
    (N : ℕ) (hN : 0 < N) :
    SandronesLibrary.Topology.Path.meshPolygonal p N hN =
      (Path.concat
        (p ∘ unitIntervalMeshPoint N hN)
        (fun i ↦ Path.segment
          (p (unitIntervalMeshPoint N hN i.castSucc))
          (p (unitIntervalMeshPoint N hN i.succ)))).cast
        (by simp) (by simp) :=
  rfl

/-- 把原道路的各网格子道路作相应有限拼接，再将端点转回原端点类型。-/
def Path.meshSubpathConcat {x y : X} (p : Path x y) (N : ℕ) (hN : 0 < N) :
    Path x y :=
  (Path.concat
    (p ∘ unitIntervalMeshPoint N hN)
    (fun i ↦ p.subpath
      (unitIntervalMeshPoint N hN i.castSucc)
      (unitIntervalMeshPoint N hN i.succ))).cast
    (by simp) (by simp)

/-- 同时将每条网格子道路直线化，再拼接各个局部端点相对仿射同伦。-/
def Path.meshStraighteningHomotopy {x y : E} (p : Path x y)
    (N : ℕ) (hN : 0 < N) :
    (SandronesLibrary.Topology.Path.meshSubpathConcat p N hN).Homotopy
      (SandronesLibrary.Topology.Path.meshPolygonal p N hN) := by
  let vertices : Fin (N + 1) → E := p ∘ unitIntervalMeshPoint N hN
  let original : (i : Fin N) → Path (vertices i.castSucc) (vertices i.succ) :=
    fun i ↦ p.subpath
      (unitIntervalMeshPoint N hN i.castSucc)
      (unitIntervalMeshPoint N hN i.succ)
  let straight : (i : Fin N) → Path (vertices i.castSucc) (vertices i.succ) :=
    fun i ↦ Path.segment
      (p (unitIntervalMeshPoint N hN i.castSucc))
      (p (unitIntervalMeshPoint N hN i.succ))
  have H := Path.Homotopy.concat vertices original straight
    (fun i ↦ SandronesLibrary.Topology.Path.affineHomotopy
      (original i) (straight i))
  simpa [SandronesLibrary.Topology.Path.meshSubpathConcat,
    SandronesLibrary.Topology.Path.meshPolygonal, vertices, original, straight] using
    H.pathCast (x' := x) (y' := y) (by simp [vertices]) (by simp [vertices])

/-- 网格球证书把直线化同伦加强为带证书的构造：每个中间点都仍位于 `U`。-/
def Path.meshStraighteningHomotopyWithMapsTo
    {x y : E} (p : Path x y) {U : Set E}
    (D : SandronesLibrary.Topology.Path.MeshBallSubdivision p U) :
    {K : (SandronesLibrary.Topology.Path.meshSubpathConcat
          p D.steps D.steps_pos).Homotopy
        (SandronesLibrary.Topology.Path.meshPolygonal
          p D.steps D.steps_pos) //
      ∀ t s : unitInterval, K (t, s) ∈ U} := by
  let vertices : Fin (D.steps + 1) → E :=
    p ∘ unitIntervalMeshPoint D.steps D.steps_pos
  let original : (i : Fin D.steps) →
      Path (vertices i.castSucc) (vertices i.succ) :=
    fun i ↦ p.subpath
      (unitIntervalMeshPoint D.steps D.steps_pos i.castSucc)
      (unitIntervalMeshPoint D.steps D.steps_pos i.succ)
  let straight : (i : Fin D.steps) →
      Path (vertices i.castSucc) (vertices i.succ) :=
    fun i ↦ Path.segment
      (p (unitIntervalMeshPoint D.steps D.steps_pos i.castSucc))
      (p (unitIntervalMeshPoint D.steps D.steps_pos i.succ))
  let localH : (i : Fin D.steps) → (original i).Homotopy (straight i) :=
    fun i ↦ SandronesLibrary.Topology.Path.affineHomotopy
      (original i) (straight i)
  have hlocal : ∀ i t s, localH i (t, s) ∈ U := by
    intro i t s
    apply D.ball_subset i
    exact SandronesLibrary.Topology.Path.affineHomotopy_mapsTo_ball
      (original i) (straight i)
      (p (unitIntervalMeshPoint D.steps D.steps_pos i.castSucc)) D.radius
      (D.subpath_mem i) (D.segment_mem i) t s
  let raw := Path.Homotopy.concatWithMapsTo vertices original straight localH
    (fun i ↦ D.path_mem (unitIntervalMeshPoint D.steps D.steps_pos i))
    hlocal
  let K := raw.1.pathCast (x' := x) (y' := y)
    (by simp [vertices]) (by simp [vertices])
  refine ⟨?_, ?_⟩
  · simpa [SandronesLibrary.Topology.Path.meshSubpathConcat,
      SandronesLibrary.Topology.Path.meshPolygonal, vertices, original, straight] using K
  · intro t s
    exact raw.2 t s

/-- 原道路的一致网格子道路拼接与原道路端点相对同伦。-/
def Path.meshSubpathConcatHomotopy {x y : X} (p : Path x y)
    (N : ℕ) (hN : 0 < N) :
    (SandronesLibrary.Topology.Path.meshSubpathConcat p N hN).Homotopy p := by
  have H := Path.Homotopy.concatSubpath p (unitIntervalMeshPoint N hN)
  let HC := H.pathCast (x' := x) (y' := y) (by simp) (by simp)
  apply Path.Homotopy.cast HC
  · rfl
  · apply Path.ext
    funext t
    simp [Path.subpath]

/-- 子道路拼接的重参数化同伦，并显式携带“每个取值都留在任何包含原道路像的集合中”的证书。-/
def Path.meshSubpathConcatHomotopyWithMapsTo
    {x y : X} (p : Path x y) {U : Set X}
    (N : ℕ) (hN : 0 < N) (hpU : ∀ t, p t ∈ U) :
    {K : (SandronesLibrary.Topology.Path.meshSubpathConcat p N hN).Homotopy p //
      ∀ t s : unitInterval, K (t, s) ∈ U} := by
  let raw := Path.Homotopy.concatSubpathWithMapsTo p
    (unitIntervalMeshPoint N hN) hpU
  let endpointCast := raw.1.pathCast (x' := x) (y' := y) (by simp) (by simp)
  have htarget :
      (p.subpath
        (unitIntervalMeshPoint N hN 0)
        (unitIntervalMeshPoint N hN (Fin.last N))).cast
          (by simp) (by simp) = p := by
    apply Path.ext
    funext t
    simp [Path.subpath]
  let K := endpointCast.cast rfl htarget
  let Kfinal :
      (SandronesLibrary.Topology.Path.meshSubpathConcat p N hN).Homotopy p := by
    simpa [SandronesLibrary.Topology.Path.meshSubpathConcat] using K
  refine ⟨Kfinal, ?_⟩
  intro t s
  have hfinal : Kfinal (t, s) = K (t, s) := by
    unfold Kfinal
    rfl
  rw [hfinal]
  have hK : K (t, s) = raw.1 (t, s) := by
    unfold K endpointCast
    rw [Path.Homotopy.cast_apply]
    rfl
  rw [hK]
  exact raw.2 t s

/-- 每个一致网格折线化都与原道路端点相对同伦。-/
def Path.meshPolygonalHomotopy {x y : E} (p : Path x y)
    (N : ℕ) (hN : 0 < N) :
    p.Homotopy (SandronesLibrary.Topology.Path.meshPolygonal p N hN) :=
  (SandronesLibrary.Topology.Path.meshSubpathConcatHomotopy p N hN).symm.trans
    (SandronesLibrary.Topology.Path.meshStraighteningHomotopy p N hN)

/-- 网格球细分给出从原道路到其折线化的端点相对同伦，且同伦的完整像仍位于 `U`。-/
def Path.meshPolygonalHomotopyWithMapsTo
    {x y : E} (p : Path x y) {U : Set E}
    (D : SandronesLibrary.Topology.Path.MeshBallSubdivision p U) :
    {K : p.Homotopy (SandronesLibrary.Topology.Path.meshPolygonal
          p D.steps D.steps_pos) //
      ∀ t s : unitInterval, K (t, s) ∈ U} := by
  let reparam := SandronesLibrary.Topology.Path.meshSubpathConcatHomotopyWithMapsTo
    p D.steps D.steps_pos D.path_mem
  let straight := SandronesLibrary.Topology.Path.meshStraighteningHomotopyWithMapsTo p D
  let K := reparam.1.symm.trans straight.1
  refine ⟨K, ?_⟩
  exact Path.Homotopy.trans_mapsTo reparam.1.symm straight.1
    (fun t s ↦ by
      rw [Path.Homotopy.symm_apply]
      exact reparam.2 _ _)
    straight.2

/-- 选定 `exists_mesh_segments_subset_open` 给出的网格直线段后，所得完整折线道路也留在原开集中。-/
theorem Path.meshPolygonal_range_subset_open {x y : E} (p : Path x y)
    {U : Set E} (N : ℕ) (hN : 0 < N) (hpU : ∀ t, p t ∈ U)
    (hsegments : ∀ i : Fin N,
      Set.range (Path.segment
        (p (unitIntervalMeshPoint N hN i.castSucc))
        (p (unitIntervalMeshPoint N hN i.succ))) ⊆ U) :
    Set.range (SandronesLibrary.Topology.Path.meshPolygonal p N hN) ⊆ U := by
  rw [Set.range_subset_iff]
  intro t
  simp only [SandronesLibrary.Topology.Path.meshPolygonal, Path.cast_coe]
  exact Set.range_subset_iff.mp
    (SandronesLibrary.Topology.Path.concat_range_subset
      (p ∘ unitIntervalMeshPoint N hN)
      (fun i ↦ Path.segment
        (p (unitIntervalMeshPoint N hN i.castSucc))
        (p (unitIntervalMeshPoint N hN i.succ)))
      (fun i ↦ hpU (unitIntervalMeshPoint N hN i)) hsegments) t

/-- 实赋范线性空间的开集中，每条道路都有一条位于同一开集的有限折线替代；原道路到该替代的
端点相对同伦的完整像也位于该开集。-/
theorem Path.exists_meshPolygonal_range_subset_open_and_homotopyWithin
    {x y : E} (p : Path x y) {U : Set E}
    (hU : IsOpen U) (hpU : ∀ t, p t ∈ U) :
    ∃ N : ℕ, ∃ hN : 0 < N,
      Set.range (SandronesLibrary.Topology.Path.meshPolygonal p N hN) ⊆ U ∧
        ∃ K : p.Homotopy
            (SandronesLibrary.Topology.Path.meshPolygonal p N hN),
          ∀ t s : unitInterval, K (t, s) ∈ U := by
  obtain ⟨D⟩ := SandronesLibrary.Topology.Path.exists_meshBallSubdivision p hU hpU
  let certified :=
    SandronesLibrary.Topology.Path.meshPolygonalHomotopyWithMapsTo p D
  refine ⟨D.steps, D.steps_pos, ?_, certified.1, certified.2⟩
  exact
    SandronesLibrary.Topology.Path.meshPolygonal_range_subset_open
      p D.steps D.steps_pos D.path_mem
      (fun i z hz ↦ by
        rcases hz with ⟨u, rfl⟩
        exact D.ball_subset i (D.segment_mem i u))

/-- 强的开集内折线化定理的环境空间同伦推论：遗忘同伦像的开集内证书。-/
theorem Path.exists_meshPolygonal_range_subset_open_and_homotopy
    {x y : E} (p : Path x y) {U : Set E}
    (hU : IsOpen U) (hpU : ∀ t, p t ∈ U) :
    ∃ N : ℕ, ∃ hN : 0 < N,
      Set.range (SandronesLibrary.Topology.Path.meshPolygonal p N hN) ⊆ U ∧
        Nonempty (p.Homotopy
          (SandronesLibrary.Topology.Path.meshPolygonal p N hN)) := by
  obtain ⟨N, hN, hpoly, K, _⟩ :=
    SandronesLibrary.Topology.Path.exists_meshPolygonal_range_subset_open_and_homotopyWithin
      p hU hpU
  exact ⟨N, hN, hpoly, ⟨K⟩⟩

end SandronesLibrary.Topology
