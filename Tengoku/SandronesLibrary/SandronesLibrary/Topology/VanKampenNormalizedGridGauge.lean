/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.VanKampenFramedGridBoundary

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# van Kampen 网格的二维规范化 gauge

本文件在道路同伦方形的边界上构造基点 potentials，并选择逐格水平边重基化为一的 row frames。
这些 frames 沿竖直 transitions 传播成二维 gauge，最终证明完整网格左右 holonomy 相等。

当前条目：

* `topology.fundamental-group.van-kampen-normalized-grid-gauge`。

row-prefix 归纳全部为 private；08 起只消费完整行高层等式。本文件不把左右相等误写成任一侧为一，
也不证明 kernel、单射或 van Kampen 同构。
-/

open Set
open scoped unitInterval

noncomputable section

namespace SandronesLibrary.Topology

variable {X : Type*} [TopologicalSpace X]

/-- 在道路同伦方形的最下行，每个单格的两个下顶点在其标签 piece 中都严格等于公共基点。

> **Entry**: topology.fundamental-group.van-kampen-normalized-grid-gauge
@isnad1 id=eq.2h11v.s7.1ff803c5e6f1 from=translated src=- shape=30d85e34 vocab=abcbcac6
-/
theorem BinaryOpenCoverSquareSubdivision.gridCellVertexInPiece_bottom_eq_basepoint
    {x₀ x₁ : X} {p q : Path x₀ x₁} (F : Path.Homotopy p q)
    {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision (pathHomotopySquare F) U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (i : Fin D.steps) (a : Fin 2) :
    D.gridCellVertexInPiece i ⟨0, D.steps_pos⟩ a 0 =
      binaryOpenCoverBasepoint hxU hxV (D.label i ⟨0, D.steps_pos⟩) := by
  apply Subtype.ext
  simp [BinaryOpenCoverSquareSubdivision.gridCellVertexInPiece,
    BinaryOpenCoverSquareSubdivision.gridCellMapInPiece,
    unitSquareGridVertex, squareGridVertex, unitSquareCellPoint,
    pathHomotopySquare]
  cases D.label i ⟨0, D.steps_pos⟩ <;> rfl

/-- 当道路同伦的两端都是基点环路时，最上行单格的两个上顶点在其标签 piece 中也严格等于公共
基点。
@isnad1 id=other.2h10v.s7.a2bc657cacdc from=translated src=- shape=f32edd97 vocab=06b56818
-/
theorem BinaryOpenCoverSquareSubdivision.gridCellVertexInPiece_top_eq_basepoint
    {x₀ : X} {p q : Path x₀ x₀} (F : Path.Homotopy p q)
    {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision (pathHomotopySquare F) U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (i : Fin D.steps) (a : Fin 2) :
    let last : Fin D.steps :=
      ⟨D.steps - 1, Nat.sub_lt D.steps_pos Nat.zero_lt_one⟩
    D.gridCellVertexInPiece i last a 1 =
      binaryOpenCoverBasepoint hxU hxV (D.label i last) := by
  let last : Fin D.steps :=
    ⟨D.steps - 1, Nat.sub_lt D.steps_pos Nat.zero_lt_one⟩
  have hsucc : last.succ = Fin.last D.steps := by
    apply Fin.ext
    simp [last]
    have := D.steps_pos
    omega
  have hlocal : unitIntervalMeshPoint 1 unitSquareOnePos (1 : Fin 2) = 1 := by
    simpa using unitIntervalMeshPoint_last 1 unitSquareOnePos
  have hmesh : unitIntervalMeshPoint D.steps D.steps_pos last.succ = 1 := by
    rw [hsucc]
    exact unitIntervalMeshPoint_last D.steps D.steps_pos
  have hbase : ((binaryOpenCoverBasepoint hxU hxV (D.label i last) :
      binaryOpenCoverPiece U V (D.label i last)) : X) = x₀ := by
    cases h : D.label i last <;> rfl
  apply Subtype.ext
  unfold BinaryOpenCoverSquareSubdivision.gridCellVertexInPiece
    BinaryOpenCoverSquareSubdivision.gridCellMapInPiece
  dsimp only [unitSquareGridVertex, unitSquareCellPoint, squareGridVertex]
  rw [hbase]
  change pathHomotopySquare F
      (Set.Icc.convexComb
          (unitIntervalMeshPoint D.steps D.steps_pos i.castSucc)
          (unitIntervalMeshPoint D.steps D.steps_pos i.succ)
          (unitIntervalMeshPoint 1 unitSquareOnePos a),
        Set.Icc.convexComb
          (unitIntervalMeshPoint D.steps D.steps_pos last.castSucc)
          (unitIntervalMeshPoint D.steps D.steps_pos last.succ)
          (unitIntervalMeshPoint 1 unitSquareOnePos 1)) = x₀
  rw [hlocal, Set.Icc.convexComb_one, hmesh]
  exact pathHomotopySquare_top F _

/-- 最上行单格的局部上边送回环境空间后逐点恒为公共基点。
@isnad1 id=other.0h10v.s11.d73598f7b3b9 from=translated src=- shape=5be81177 vocab=ee5a5381
-/
theorem BinaryOpenCoverSquareSubdivision.coe_gridCellTopEdge_eq
    {x₀ : X} {p q : Path x₀ x₀} (F : Path.Homotopy p q)
    {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision (pathHomotopySquare F) U V)
    (i : Fin D.steps) (t : unitInterval) :
    let row : Fin D.steps :=
      ⟨D.steps - 1, Nat.sub_lt D.steps_pos Nat.zero_lt_one⟩
    ((((squareGridHorizontalEdge
        (ContinuousMap.id (unitInterval × unitInterval))
        1 unitSquareOnePos 0 1).map
          (D.gridCellMapInPiece i row).continuous) t :
          binaryOpenCoverPiece U V (D.label i row)) : X) = x₀ := by
  dsimp only
  let row : Fin D.steps :=
    ⟨D.steps - 1, Nat.sub_lt D.steps_pos Nat.zero_lt_one⟩
  have hsucc : row.succ = Fin.last D.steps := by
    apply Fin.ext
    simp [row]
    have := D.steps_pos
    omega
  have hmesh : unitIntervalMeshPoint D.steps D.steps_pos row.succ = 1 := by
    rw [hsucc]
    exact unitIntervalMeshPoint_last D.steps D.steps_pos
  have hone : unitIntervalMeshPoint 1 unitSquareOnePos (1 : Fin 2) = 1 := by
    simpa using unitIntervalMeshPoint_last 1 unitSquareOnePos
  change ↑(D.gridCellMapInPiece i row
      (squareGridHorizontalEdge
        (ContinuousMap.id (unitInterval × unitInterval))
        1 unitSquareOnePos 0 1 t)) = x₀
  unfold BinaryOpenCoverSquareSubdivision.gridCellMapInPiece
  simp [squareGridHorizontalEdge, unitSquareCellPoint, hmesh, hone]

/-- 若同伦终道路是基点常值道路，则最右列每个单格的两个右顶点在其标签 piece 中都是公共基点。
@isnad1 id=other.2h9v.s7.f09b6a358b92 from=translated src=- shape=39a365df vocab=803673d9
-/
theorem BinaryOpenCoverSquareSubdivision.gridCellVertexInPiece_right_eq_basepoint
    {x₀ : X} {p : Path x₀ x₀}
    (F : Path.Homotopy p (Path.refl x₀)) {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision (pathHomotopySquare F) U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (j : Fin D.steps) (b : Fin 2) :
    let last : Fin D.steps :=
      ⟨D.steps - 1, Nat.sub_lt D.steps_pos Nat.zero_lt_one⟩
    D.gridCellVertexInPiece last j 1 b =
      binaryOpenCoverBasepoint hxU hxV (D.label last j) := by
  let last : Fin D.steps :=
    ⟨D.steps - 1, Nat.sub_lt D.steps_pos Nat.zero_lt_one⟩
  have hsucc : last.succ = Fin.last D.steps := by
    apply Fin.ext
    simp [last]
    have := D.steps_pos
    omega
  have hlocal : unitIntervalMeshPoint 1 unitSquareOnePos (1 : Fin 2) = 1 := by
    simpa using unitIntervalMeshPoint_last 1 unitSquareOnePos
  have hmesh : unitIntervalMeshPoint D.steps D.steps_pos last.succ = 1 := by
    rw [hsucc]
    exact unitIntervalMeshPoint_last D.steps D.steps_pos
  have hbase : ((binaryOpenCoverBasepoint hxU hxV (D.label last j) :
      binaryOpenCoverPiece U V (D.label last j)) : X) = x₀ := by
    cases h : D.label last j <;> rfl
  apply Subtype.ext
  unfold BinaryOpenCoverSquareSubdivision.gridCellVertexInPiece
    BinaryOpenCoverSquareSubdivision.gridCellMapInPiece
  dsimp only [unitSquareGridVertex, unitSquareCellPoint, squareGridVertex]
  rw [hbase]
  change pathHomotopySquare F
      (Set.Icc.convexComb
          (unitIntervalMeshPoint D.steps D.steps_pos last.castSucc)
          (unitIntervalMeshPoint D.steps D.steps_pos last.succ)
          (unitIntervalMeshPoint 1 unitSquareOnePos 1),
        Set.Icc.convexComb
          (unitIntervalMeshPoint D.steps D.steps_pos j.castSucc)
          (unitIntervalMeshPoint D.steps D.steps_pos j.succ)
          (unitIntervalMeshPoint 1 unitSquareOnePos b)) = x₀
  rw [hlocal, Set.Icc.convexComb_one, hmesh]
  exact pathHomotopySquare_one_left F _

/-- 最右列单格的局部右边送回环境空间后逐点恒为公共基点。
@isnad1 id=other.0h9v.s11.f47244e48805 from=translated src=- shape=ad979cfc vocab=1f650a04
-/
theorem BinaryOpenCoverSquareSubdivision.coe_gridCellRightEdge_eq
    {x₀ : X} {p : Path x₀ x₀}
    (F : Path.Homotopy p (Path.refl x₀)) {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision (pathHomotopySquare F) U V)
    (j : Fin D.steps) (t : unitInterval) :
    let col : Fin D.steps :=
      ⟨D.steps - 1, Nat.sub_lt D.steps_pos Nat.zero_lt_one⟩
    ((((squareGridVerticalEdge
        (ContinuousMap.id (unitInterval × unitInterval))
        1 unitSquareOnePos 1 0).map
          (D.gridCellMapInPiece col j).continuous) t :
          binaryOpenCoverPiece U V (D.label col j)) : X) = x₀ := by
  dsimp only
  let col : Fin D.steps :=
    ⟨D.steps - 1, Nat.sub_lt D.steps_pos Nat.zero_lt_one⟩
  have hsucc : col.succ = Fin.last D.steps := by
    apply Fin.ext
    simp [col]
    have := D.steps_pos
    omega
  have hmesh : unitIntervalMeshPoint D.steps D.steps_pos col.succ = 1 := by
    rw [hsucc]
    exact unitIntervalMeshPoint_last D.steps D.steps_pos
  have hone : unitIntervalMeshPoint 1 unitSquareOnePos (1 : Fin 2) = 1 := by
    simpa using unitIntervalMeshPoint_last 1 unitSquareOnePos
  change ↑(D.gridCellMapInPiece col j
      (squareGridVerticalEdge
        (ContinuousMap.id (unitInterval × unitInterval))
        1 unitSquareOnePos 1 0 t)) = x₀
  unfold BinaryOpenCoverSquareSubdivision.gridCellMapInPiece
  simp [squareGridVerticalEdge, unitSquareCellPoint, hmesh, hone]

namespace BinaryOpenCoverSquareSubdivision

/-- 将“某个单格顶点就是公共 piece 基点”统一转成 grid-cell potential 接口需要的交集基点像等式。
@isnad1 id=eq.3h10v.s8.bbd0bd90491d from=translated src=- shape=3b64df87 vocab=2762d02d
-/
theorem intersectionBasepoint_eq_gridCellVertexInPiece_of_eq_basepoint
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (i j : Fin D.steps) (a b : Fin 2)
    (hvertex : D.gridCellVertexInPiece i j a b =
      binaryOpenCoverBasepoint hxU hxV (D.label i j)) :
    binaryOpenCoverIntersectionToPiece U V (D.label i j)
        (binaryOpenCoverIntersectionBasepoint hxU hxV) =
      D.gridCellVertexInPiece i j a b := by
  rw [hvertex]
  exact (binaryOpenCoverBasepoint_eq_intersectionToPiece
    hxU hxV (D.label i j)).symm

end BinaryOpenCoverSquareSubdivision

/-- 公共基点边界顶点的标准 grid-cell potential。显式保留顶点等于 piece 基点的证明，使底、顶、右
三条边可以共享同一个定义。-/
noncomputable def BinaryOpenCoverSquareSubdivision.gridCellBasepointPotential
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j : Fin D.steps) (a b : Fin 2)
    (hvertex : D.gridCellVertexInPiece i j a b =
      binaryOpenCoverBasepoint hxU hxV (D.label i j)) :
    binaryVanKampenPushout U V hxU hxV :=
  D.gridCellVertexPotentialFromIntersection hxU hxV hUV hU hV
    (binaryOpenCoverIntersectionBasepoint hxU hxV) i j a b
    (D.intersectionBasepoint_eq_gridCellVertexInPiece_of_eq_basepoint
      hxU hxV i j a b hvertex)

/-- 最下行单格局部下边送回底层空间后逐点恒为道路起点。-/
private theorem BinaryOpenCoverSquareSubdivision.coe_gridCellBottomEdge_eq
    {x₀ x₁ : X} {p q : Path x₀ x₁} (F : Path.Homotopy p q)
    {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision (pathHomotopySquare F) U V)
    (i : Fin D.steps) (t : unitInterval) :
    ((((squareGridHorizontalEdge
        (ContinuousMap.id (unitInterval × unitInterval))
        1 unitSquareOnePos 0 0).map
          (D.gridCellMapInPiece i ⟨0, D.steps_pos⟩).continuous) t :
          binaryOpenCoverPiece U V (D.label i ⟨0, D.steps_pos⟩)) : X) = x₀ := by
  change ↑(D.gridCellMapInPiece i ⟨0, D.steps_pos⟩
      ((squareGridHorizontalEdge
        (ContinuousMap.id (unitInterval × unitInterval))
        1 unitSquareOnePos 0 0) t)) = x₀
  unfold BinaryOpenCoverSquareSubdivision.gridCellMapInPiece
  simp [squareGridHorizontalEdge, unitSquareCellPoint]

/-- 最下行单格的下边 cast 到公共 piece 基点后的基环路。-/
private def BinaryOpenCoverSquareSubdivision.gridCellBottomEdgeAtBasepoint
    {x₀ x₁ : X} {p q : Path x₀ x₁} (F : Path.Homotopy p q)
    {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision (pathHomotopySquare F) U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (i : Fin D.steps) :
    Path
      (binaryOpenCoverBasepoint hxU hxV (D.label i ⟨0, D.steps_pos⟩))
      (binaryOpenCoverBasepoint hxU hxV (D.label i ⟨0, D.steps_pos⟩)) :=
  let j : Fin D.steps := ⟨0, D.steps_pos⟩
  let edge := ((squareGridHorizontalEdge
      (ContinuousMap.id (unitInterval × unitInterval))
      1 unitSquareOnePos 0 0).map (D.gridCellMapInPiece i j).continuous)
  edge.cast
    (D.gridCellVertexInPiece_bottom_eq_basepoint F hxU hxV i 0).symm
    (D.gridCellVertexInPiece_bottom_eq_basepoint F hxU hxV i 1).symm

/-- 上述 cast 后的最下行 piece 边严格等于公共基点处的常值道路。-/
private theorem BinaryOpenCoverSquareSubdivision.gridCellBottomEdgeAtBasepoint_eq_refl
    {x₀ x₁ : X} {p q : Path x₀ x₁} (F : Path.Homotopy p q)
    {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision (pathHomotopySquare F) U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (i : Fin D.steps) :
    D.gridCellBottomEdgeAtBasepoint F hxU hxV i =
      Path.refl (binaryOpenCoverBasepoint hxU hxV
        (D.label i ⟨0, D.steps_pos⟩)) := by
  apply Path.ext
  funext t
  apply Subtype.ext
  change ((((squareGridHorizontalEdge
      (ContinuousMap.id (unitInterval × unitInterval))
      1 unitSquareOnePos 0 0).map
        (D.gridCellMapInPiece i ⟨0, D.steps_pos⟩).continuous) t :
        binaryOpenCoverPiece U V (D.label i ⟨0, D.steps_pos⟩)) : X) =
    ↑(binaryOpenCoverBasepoint hxU hxV (D.label i ⟨0, D.steps_pos⟩))
  rw [D.coe_gridCellBottomEdge_eq F i t]
  cases D.label i ⟨0, D.steps_pos⟩ <;> rfl

/-- 最下行单格下顶点的 boundary frame：在相应 piece 中，以公共基点常值 connector 为参考，
记录实际单格 connector 的 potential，并送入 Pushout。-/
noncomputable def BinaryOpenCoverSquareSubdivision.gridCellBottomBoundaryPotential
    {x₀ x₁ : X} {p q : Path x₀ x₁} (F : Path.Homotopy p q)
    {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision (pathHomotopySquare F) U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i : Fin D.steps) (a : Fin 2) :
    binaryVanKampenPushout U V hxU hxV :=
  let j : Fin D.steps := ⟨0, D.steps_pos⟩
  let base := binaryOpenCoverBasepoint hxU hxV (D.label i j)
  let connector := D.gridCellVertexConnectorInPiece hxU hxV hU hV i j a 0
  let hvertex : base = D.gridCellVertexInPiece i j a 0 :=
    (D.gridCellVertexInPiece_bottom_eq_basepoint F hxU hxV i a).symm
  Monoid.PushoutI.of (D.label i j)
    (connectorChange (Path.refl base) (connector.cast rfl hvertex))

/-- 每个真实最下行 piece 边，在其两个 boundary potentials 下送入 Pushout 后严格为单位元。
@isnad1 id=eq.4h10v.s12.7e859cad9384 from=translated src=- shape=be2cdd4e vocab=4527ec1a
-/
theorem BinaryOpenCoverSquareSubdivision.gridCellBottomEdge_rebase_eq_one
    {x₀ x₁ : X} {p q : Path x₀ x₁} (F : Path.Homotopy p q)
    {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision (pathHomotopySquare F) U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i : Fin D.steps) :
    rebaseEdge
        (D.gridCellBottomBoundaryPotential F hxU hxV hU hV i 0)
        (D.gridCellBottomBoundaryPotential F hxU hxV hU hV i 1)
        (Monoid.PushoutI.of (D.label i ⟨0, D.steps_pos⟩)
          (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV
            i ⟨0, D.steps_pos⟩ 0)) = 1 := by
  let j : Fin D.steps := ⟨0, D.steps_pos⟩
  let base := binaryOpenCoverBasepoint hxU hxV (D.label i j)
  let startConnector := D.gridCellVertexConnectorInPiece hxU hxV hU hV i j 0 0
  let endConnector := D.gridCellVertexConnectorInPiece hxU hxV hU hV i j 1 0
  let segment := ((squareGridHorizontalEdge
      (ContinuousMap.id (unitInterval × unitInterval))
      1 unitSquareOnePos 0 0).map (D.gridCellMapInPiece i j).continuous)
  let hz : base = D.gridCellVertexInPiece i j 0 0 :=
    (D.gridCellVertexInPiece_bottom_eq_basepoint F hxU hxV i 0).symm
  let hw : base = D.gridCellVertexInPiece i j 1 0 :=
    (D.gridCellVertexInPiece_bottom_eq_basepoint F hxU hxV i 1).symm
  have hsegment : segment.cast hz hw = Path.refl base := by
    simpa [BinaryOpenCoverSquareSubdivision.gridCellBottomEdgeAtBasepoint,
      segment, hz, hw, j, base] using
      D.gridCellBottomEdgeAtBasepoint_eq_refl F hxU hxV i
  change rebaseEdge
      (Monoid.PushoutI.of
        (φ := binaryOpenCoverIntersectionMaps U V hxU hxV) (D.label i j)
        (connectorChange (Path.refl base) (startConnector.cast rfl hz)))
      (Monoid.PushoutI.of
        (φ := binaryOpenCoverIntersectionMaps U V hxU hxV) (D.label i j)
        (connectorChange (Path.refl base) (endConnector.cast rfl hw)))
      (Monoid.PushoutI.of
        (φ := binaryOpenCoverIntersectionMaps U V hxU hxV) (D.label i j)
        (FundamentalGroup.fromPath
          ⟦Path.correctedLoop startConnector segment endConnector⟧)) = 1
  exact map_rebase_correctedLoop_eq_one_of_cast_eq_refl
    (Monoid.PushoutI.of
      (φ := binaryOpenCoverIntersectionMaps U V hxU hxV) (D.label i j))
      (Path.refl base)
      startConnector segment endConnector hz hw hsegment

/-- 一行的 gauge-normalized frames：第一格左侧取单位元；每格左侧由真实
horizontal transition 从前一格右侧传播，右侧则定义为对应横边元素乘左侧。
因此水平相容性与每条上下横边的归一化同时由构造保证。-/
private noncomputable def BinaryOpenCoverSquareSubdivision.gaugeNormalizedRowFramesAt
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (j : Fin D.steps) :
    (p : ℕ) → (hp : p < D.steps) →
      CellVertexFrames (binaryVanKampenPushout U V hxU hxV)
  | 0, hp =>
      let i : Fin D.steps := ⟨0, hp⟩
      let bottom : binaryVanKampenPushout U V hxU hxV :=
        Monoid.PushoutI.of (D.label i j)
          (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i j 0)
      let top : binaryVanKampenPushout U V hxU hxV :=
        Monoid.PushoutI.of (D.label i j)
          (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i j 1)
      { bottomLeft := 1
        bottomRight := bottom
        topLeft := 1
        topRight := top }
  | p + 1, hp =>
      let hp' : p < D.steps := Nat.lt_trans (Nat.lt_succ_self p) hp
      let i : Fin D.steps := ⟨p, hp'⟩
      let k : Fin D.steps := ⟨p + 1, hp⟩
      let hshared : i.succ = k.castSucc := by apply Fin.ext; rfl
      let previous := D.gaugeNormalizedRowFramesAt hxU hxV hUV hU hV j p hp'
      let T := D.horizontalInternalEdgeTransitions hxU hxV hUV hU hV
        i k j hshared
      let bottomLeft := T.startChange * previous.bottomRight
      let topLeft := T.endChange * previous.topRight
      let bottom : binaryVanKampenPushout U V hxU hxV :=
        Monoid.PushoutI.of (D.label k j)
          (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV k j 0)
      let top : binaryVanKampenPushout U V hxU hxV :=
        Monoid.PushoutI.of (D.label k j)
          (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV k j 1)
      { bottomLeft := bottomLeft
        bottomRight := bottom * bottomLeft
        topLeft := topLeft
        topRight := top * topLeft }

/-- 上述自然编号定义组成完整的单行 frame family。-/
noncomputable def BinaryOpenCoverSquareSubdivision.gaugeNormalizedRowFrames
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (j : Fin D.steps) :
    Fin D.steps → CellVertexFrames (binaryVanKampenPushout U V hxU hxV) :=
  fun i => D.gaugeNormalizedRowFramesAt hxU hxV hUV hU hV j i.val i.isLt

/-- gauge-normalized frames 对每条真实水平 internal transition 相容。
@isnad1 id=horizont.6h9v.s8.d9e12796d47a from=translated src=- shape=43b02cab vocab=4204c339
-/
theorem BinaryOpenCoverSquareSubdivision.gaugeNormalizedRowFrames_compatible
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (j : Fin D.steps) (i k : Fin D.steps) (hshared : i.succ = k.castSucc) :
    HorizontalCellFramesCompatible
      (D.horizontalInternalEdgeTransitions hxU hxV hUV hU hV i k j hshared)
      (D.gaugeNormalizedRowFrames hxU hxV hUV hU hV j i)
      (D.gaugeNormalizedRowFrames hxU hxV hUV hU hV j k) := by
  rcases i with ⟨iv, hiv⟩
  rcases k with ⟨kv, hkv⟩
  have hval : iv + 1 = kv := congrArg Fin.val hshared
  change iv + 1 = kv at hval
  subst kv
  constructor <;> rfl

/-- gauge-normalized frames 下，每格的下横边与上横边都严格归一化为单位元。
@isnad1 id=other.5h8v.s12.5cef771fc263 from=translated src=- shape=504075ac vocab=2d3256ff
-/
theorem BinaryOpenCoverSquareSubdivision.gaugeNormalizedRowFrames_horizontal_edges
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (j i : Fin D.steps) :
    let F := D.gaugeNormalizedRowFrames hxU hxV hUV hU hV j i
    rebaseEdge F.bottomLeft F.bottomRight
        (Monoid.PushoutI.of (D.label i j)
          (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i j 0)) = 1 ∧
      rebaseEdge F.topLeft F.topRight
        (Monoid.PushoutI.of (D.label i j)
          (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i j 1)) = 1 := by
  rcases i with ⟨_ | p, hp⟩
  · let i : Fin D.steps := ⟨0, hp⟩
    constructor
    · change rebaseEdge 1
          (Monoid.PushoutI.of
            (φ := binaryOpenCoverIntersectionMaps U V hxU hxV) (D.label i j)
            (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i j 0))
          (Monoid.PushoutI.of
            (φ := binaryOpenCoverIntersectionMaps U V hxU hxV) (D.label i j)
            (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i j 0)) = 1
      simpa using rebaseEdge_mul_start_eq_one
        (1 : binaryVanKampenPushout U V hxU hxV)
        (Monoid.PushoutI.of
          (φ := binaryOpenCoverIntersectionMaps U V hxU hxV) (D.label i j)
          (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i j 0))
    · change rebaseEdge 1
          (Monoid.PushoutI.of
            (φ := binaryOpenCoverIntersectionMaps U V hxU hxV) (D.label i j)
            (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i j 1))
          (Monoid.PushoutI.of
            (φ := binaryOpenCoverIntersectionMaps U V hxU hxV) (D.label i j)
            (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i j 1)) = 1
      simpa using rebaseEdge_mul_start_eq_one
        (1 : binaryVanKampenPushout U V hxU hxV)
        (Monoid.PushoutI.of
          (φ := binaryOpenCoverIntersectionMaps U V hxU hxV) (D.label i j)
          (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i j 1))
  · have hp' : p < D.steps := Nat.lt_trans (Nat.lt_succ_self p) hp
    let previous := D.gaugeNormalizedRowFramesAt hxU hxV hUV hU hV j p hp'
    let left : Fin D.steps := ⟨p, hp'⟩
    let current : Fin D.steps := ⟨p + 1, hp⟩
    let hshared : left.succ = current.castSucc := by apply Fin.ext; rfl
    let T := D.horizontalInternalEdgeTransitions hxU hxV hUV hU hV
      left current j hshared
    let bottomLeft := T.startChange * previous.bottomRight
    let topLeft := T.endChange * previous.topRight
    let bottom : binaryVanKampenPushout U V hxU hxV :=
      Monoid.PushoutI.of (D.label current j)
        (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV current j 0)
    let top : binaryVanKampenPushout U V hxU hxV :=
      Monoid.PushoutI.of (D.label current j)
        (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV current j 1)
    change rebaseEdge bottomLeft (bottom * bottomLeft) bottom = 1 ∧
      rebaseEdge topLeft (top * topLeft) top = 1
    exact ⟨rebaseEdge_mul_start_eq_one bottomLeft bottom,
      rebaseEdge_mul_start_eq_one topLeft top⟩

/-- 沿相邻两行之间的逐列竖直 transitions 提升底部 frames，同时从一个独立的水平相容 family
读取新行的顶部 frames。-/
private noncomputable def BinaryOpenCoverSquareSubdivision.liftHorizontalRowFramesWithTop
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (j l : Fin D.steps) (hVertical : j.succ = l.castSucc)
    (lowerFrames topFrames : Fin D.steps → CellVertexFrames
      (binaryVanKampenPushout U V hxU hxV)) :
    Fin D.steps → CellVertexFrames (binaryVanKampenPushout U V hxU hxV) :=
  fun i =>
    let Vt := D.verticalInternalEdgeTransitions hxU hxV hUV hU hV
      i j l hVertical
    (lowerFrames i).liftAcrossVertical Vt
      (topFrames i).topRight (topFrames i).topLeft

/-- 下行 frames 与所选新行顶部 frames 分别水平相容时，逐列竖直提升所得完整新行仍水平相容。-/
private theorem BinaryOpenCoverSquareSubdivision.liftHorizontalRowFramesWithTop_compatible
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (j l : Fin D.steps) (hVertical : j.succ = l.castSucc)
    (lowerFrames topFrames : Fin D.steps → CellVertexFrames
      (binaryVanKampenPushout U V hxU hxV))
    (hLower : ∀ (i k : Fin D.steps) (hHorizontal : i.succ = k.castSucc),
      HorizontalCellFramesCompatible
        (D.horizontalInternalEdgeTransitions hxU hxV hUV hU hV i k j hHorizontal)
        (lowerFrames i) (lowerFrames k))
    (hTop : ∀ (i k : Fin D.steps) (hHorizontal : i.succ = k.castSucc),
      HorizontalCellFramesCompatible
        (D.horizontalInternalEdgeTransitions hxU hxV hUV hU hV i k l hHorizontal)
        (topFrames i) (topFrames k))
    (i k : Fin D.steps) (hHorizontal : i.succ = k.castSucc) :
    HorizontalCellFramesCompatible
      (D.horizontalInternalEdgeTransitions hxU hxV hUV hU hV i k l hHorizontal)
      (D.liftHorizontalRowFramesWithTop hxU hxV hUV hU hV
        j l hVertical lowerFrames topFrames i)
      (D.liftHorizontalRowFramesWithTop hxU hxV hUV hU hV
        j l hVertical lowerFrames topFrames k) := by
  apply horizontalCellFramesCompatible_liftAcrossVertical
    (D.horizontalInternalEdgeTransitions hxU hxV hUV hU hV i k j hHorizontal)
    (D.horizontalInternalEdgeTransitions hxU hxV hUV hU hV i k l hHorizontal)
    (D.verticalInternalEdgeTransitions hxU hxV hUV hU hV i j l hVertical)
    (D.verticalInternalEdgeTransitions hxU hxV hUV hU hV k j l hVertical)
    (lowerFrames i) (lowerFrames k)
    ((topFrames i).topRight) ((topFrames i).topLeft)
    ((topFrames k).topRight) ((topFrames k).topLeft)
  · exact hLower i k hHorizontal
  · exact D.centralInternalTransitions_square hxU hxV hUV hU hV
      i k j l hHorizontal hVertical
  · exact (hTop i k hHorizontal).top

/-- 底行使用 gauge-normalized frames；每个后继行的底部从前一行顶部竖直提升，顶部采用该行
gauge-normalized family 的顶部两端。-/
private noncomputable def BinaryOpenCoverSquareSubdivision.gaugeGridRowFramesAt
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V) :
    (p : ℕ) → (hp : p < D.steps) →
      Fin D.steps → CellVertexFrames (binaryVanKampenPushout U V hxU hxV)
  | 0, hp => D.gaugeNormalizedRowFrames hxU hxV hUV hU hV ⟨0, hp⟩
  | p + 1, hp =>
      let hp' : p < D.steps := Nat.lt_trans (Nat.lt_succ_self p) hp
      let j : Fin D.steps := ⟨p, hp'⟩
      let l : Fin D.steps := ⟨p + 1, hp⟩
      let hVertical : j.succ = l.castSucc := by apply Fin.ext; rfl
      D.liftHorizontalRowFramesWithTop hxU hxV hUV hU hV
        j l hVertical
        (D.gaugeGridRowFramesAt hxU hxV hUV hU hV p hp')
        (D.gaugeNormalizedRowFrames hxU hxV hUV hU hV l)

/-- 二维 gauge 递归生成的每一行都与该行所有真实水平 internal transitions 相容。-/
private theorem BinaryOpenCoverSquareSubdivision.gaugeGridRowFramesAt_compatible
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V) :
    ∀ (p : ℕ) (hp : p < D.steps)
      (i k : Fin D.steps) (hHorizontal : i.succ = k.castSucc),
      HorizontalCellFramesCompatible
        (D.horizontalInternalEdgeTransitions hxU hxV hUV hU hV
          i k ⟨p, hp⟩ hHorizontal)
        (D.gaugeGridRowFramesAt hxU hxV hUV hU hV p hp i)
        (D.gaugeGridRowFramesAt hxU hxV hUV hU hV p hp k)
  | 0, hp, i, k, hHorizontal =>
      D.gaugeNormalizedRowFrames_compatible hxU hxV hUV hU hV
        ⟨0, hp⟩ i k hHorizontal
  | p + 1, hp, i, k, hHorizontal => by
      have hp' : p < D.steps := Nat.lt_trans (Nat.lt_succ_self p) hp
      let j : Fin D.steps := ⟨p, hp'⟩
      let l : Fin D.steps := ⟨p + 1, hp⟩
      have hVertical : j.succ = l.castSucc := by apply Fin.ext; rfl
      apply D.liftHorizontalRowFramesWithTop_compatible hxU hxV hUV hU hV
        j l hVertical
        (D.gaugeGridRowFramesAt hxU hxV hUV hU hV p hp')
        (D.gaugeNormalizedRowFrames hxU hxV hUV hU hV l)
      · intro i' k' hHorizontal'
        exact D.gaugeGridRowFramesAt_compatible hxU hxV hUV hU hV
          p hp' i' k' hHorizontal'
      · exact D.gaugeNormalizedRowFrames_compatible hxU hxV hUV hU hV l

/-- 二维 gauge 递归的每行顶部 frames 严格等于该行独立 gauge-normalized family 的顶部。-/
private theorem BinaryOpenCoverSquareSubdivision.gaugeGridRowFramesAt_top_eq
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V) :
    ∀ (p : ℕ) (hp : p < D.steps) (i : Fin D.steps),
      let actual := D.gaugeGridRowFramesAt hxU hxV hUV hU hV p hp i
      let normalized := D.gaugeNormalizedRowFrames hxU hxV hUV hU hV ⟨p, hp⟩ i
      actual.topLeft = normalized.topLeft ∧ actual.topRight = normalized.topRight
  | 0, hp, i => by
      exact ⟨rfl, rfl⟩
  | p + 1, hp, i => by
      exact ⟨rfl, rfl⟩

/-- 二维 gauge frames 下，每一行的每条上横边都严格归一化为单位元。-/
private theorem BinaryOpenCoverSquareSubdivision.gaugeGridRowFramesAt_top_edge_eq_one
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (p : ℕ) (hp : p < D.steps) (i : Fin D.steps) :
    let F := D.gaugeGridRowFramesAt hxU hxV hUV hU hV p hp i
    rebaseEdge F.topLeft F.topRight
      (Monoid.PushoutI.of (D.label i ⟨p, hp⟩)
        (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i ⟨p, hp⟩ 1)) = 1 := by
  have htop := D.gaugeGridRowFramesAt_top_eq hxU hxV hUV hU hV p hp i
  have hnorm := (D.gaugeNormalizedRowFrames_horizontal_edges
    hxU hxV hUV hU hV ⟨p, hp⟩ i).2
  dsimp only at htop ⊢
  rw [htop.1, htop.2]
  exact hnorm

/-- 相邻两行同一列中，下格规范化上边严格等于上格规范化下边。-/
private theorem BinaryOpenCoverSquareSubdivision.gaugeGridRowFramesAt_vertical_edge
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (p : ℕ) (hp : p + 1 < D.steps) (i : Fin D.steps) :
    let hp' : p < D.steps := Nat.lt_trans (Nat.lt_succ_self p) hp
    let j : Fin D.steps := ⟨p, hp'⟩
    let l : Fin D.steps := ⟨p + 1, hp⟩
    let lower := D.gaugeGridRowFramesAt hxU hxV hUV hU hV p hp' i
    let upper := D.gaugeGridRowFramesAt hxU hxV hUV hU hV (p + 1) hp i
    rebaseEdge lower.topLeft lower.topRight
        (Monoid.PushoutI.of (D.label i j)
          (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i j 1)) =
      rebaseEdge upper.bottomLeft upper.bottomRight
        (Monoid.PushoutI.of (D.label i l)
          (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i l 0)) := by
  let hp' : p < D.steps := Nat.lt_trans (Nat.lt_succ_self p) hp
  let j : Fin D.steps := ⟨p, hp'⟩
  let l : Fin D.steps := ⟨p + 1, hp⟩
  have hVertical : j.succ = l.castSucc := by apply Fin.ext; rfl
  let lowerFrames := D.gaugeGridRowFramesAt hxU hxV hUV hU hV p hp'
  have h := D.verticalInternalEdge_relation_in_frame hxU hxV hUV hU hV
    i j l hVertical (lowerFrames i).topLeft (lowerFrames i).topRight
  simpa [BinaryOpenCoverSquareSubdivision.gaugeGridRowFramesAt,
    BinaryOpenCoverSquareSubdivision.liftHorizontalRowFramesWithTop,
    CellVertexFrames.liftAcrossVertical, lowerFrames, j, l, hp'] using h

/-- 二维 gauge frames 下，每一行的每条下横边也严格归一化为单位元。-/
private theorem BinaryOpenCoverSquareSubdivision.gaugeGridRowFramesAt_bottom_edge_eq_one
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V) :
    ∀ (p : ℕ) (hp : p < D.steps) (i : Fin D.steps),
    let F := D.gaugeGridRowFramesAt hxU hxV hUV hU hV p hp i
    rebaseEdge F.bottomLeft F.bottomRight
      (Monoid.PushoutI.of (D.label i ⟨p, hp⟩)
        (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i ⟨p, hp⟩ 0)) = 1
  | 0, hp, i => by
      exact (D.gaugeNormalizedRowFrames_horizontal_edges
        hxU hxV hUV hU hV ⟨0, hp⟩ i).1
  | p + 1, hp, i => by
      have hp' : p < D.steps := Nat.lt_trans (Nat.lt_succ_self p) hp
      have hshared := D.gaugeGridRowFramesAt_vertical_edge
        hxU hxV hUV hU hV p hp i
      have htop := D.gaugeGridRowFramesAt_top_edge_eq_one
        hxU hxV hUV hU hV p hp' i
      dsimp only at hshared htop ⊢
      rw [← hshared]
      exact htop

/-- 二维 gauge frames 上第 `p` 行任意列前缀的完整上、下边词均为单位元。-/
private theorem BinaryOpenCoverSquareSubdivision.gaugeGridFramedRowPrefix_horizontal_words_eq_one
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (p : ℕ) (hp : p < D.steps) :
    ∀ (q : ℕ) (hq : q < D.steps),
    let frames := D.gaugeGridRowFramesAt hxU hxV hUV hU hV p hp
    let S := D.framedHorizontalRowPrefixState hxU hxV hUV hU hV
      ⟨p, hp⟩ frames (D.gaugeGridRowFramesAt_compatible
        hxU hxV hUV hU hV p hp) q hq
    S.topWord = 1 ∧ S.boundary.after * S.bottomPrefix = 1
  | 0, hq => by
      let i : Fin D.steps := ⟨0, hq⟩
      let frames := D.gaugeGridRowFramesAt hxU hxV hUV hU hV p hp
      let S := D.framedHorizontalRowPrefixState hxU hxV hUV hU hV
        ⟨p, hp⟩ frames (D.gaugeGridRowFramesAt_compatible
          hxU hxV hUV hU hV p hp) 0 hq
      have htop := D.gaugeGridRowFramesAt_top_edge_eq_one
        hxU hxV hUV hU hV p hp i
      have hbottom := D.gaugeGridRowFramesAt_bottom_edge_eq_one
        hxU hxV hUV hU hV p hp i
      dsimp only at htop hbottom ⊢
      change rebaseEdge (frames i).topLeft (frames i).topRight
            (Monoid.PushoutI.of (D.label i ⟨p, hp⟩)
              (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i ⟨p, hp⟩ 1)) = 1 ∧
        rebaseEdge (frames i).bottomLeft (frames i).bottomRight
            (Monoid.PushoutI.of (D.label i ⟨p, hp⟩)
              (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i ⟨p, hp⟩ 0)) * 1 = 1
      exact ⟨htop, by simpa using hbottom⟩
  | q + 1, hq => by
      have hq' : q < D.steps := Nat.lt_trans (Nat.lt_succ_self q) hq
      let frames := D.gaugeGridRowFramesAt hxU hxV hUV hU hV p hp
      let compat := D.gaugeGridRowFramesAt_compatible
        hxU hxV hUV hU hV p hp
      let previous := D.framedHorizontalRowPrefixState hxU hxV hUV hU hV
        ⟨p, hp⟩ frames compat q hq'
      let current := D.framedHorizontalRowPrefixState hxU hxV hUV hU hV
        ⟨p, hp⟩ frames compat (q + 1) hq
      let k : Fin D.steps := ⟨q + 1, hq⟩
      have ih := D.gaugeGridFramedRowPrefix_horizontal_words_eq_one
        hxU hxV hUV hU hV p hp q hq'
      have htopEdge := D.gaugeGridRowFramesAt_top_edge_eq_one
        hxU hxV hUV hU hV p hp k
      have hbottomEdge := D.gaugeGridRowFramesAt_bottom_edge_eq_one
        hxU hxV hUV hU hV p hp k
      dsimp only at htopEdge hbottomEdge
      change current.topWord = 1 ∧
        current.boundary.after * current.bottomPrefix = 1
      change previous.topWord = 1 ∧
        previous.boundary.after * previous.bottomPrefix = 1 at ih
      have htop : current.topWord =
          rebaseEdge (frames k).topLeft (frames k).topRight
            (Monoid.PushoutI.of (D.label k ⟨p, hp⟩)
              (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV k ⟨p, hp⟩ 1)) *
            previous.topWord := by rfl
      have hbottom : current.boundary.after * current.bottomPrefix =
          rebaseEdge (frames k).bottomLeft (frames k).bottomRight
            (Monoid.PushoutI.of (D.label k ⟨p, hp⟩)
              (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV k ⟨p, hp⟩ 0)) *
            (previous.boundary.after * previous.bottomPrefix) := by
        rw [current.after_eq]
        rfl
      rw [htop, hbottom, htopEdge, hbottomEdge, ih.1, ih.2]
      simp

/-- 二维 gauge frames 上第 `p` 行的完整上下边界词均为单位元。-/
private theorem BinaryOpenCoverSquareSubdivision.gaugeGridFramedFullRow_horizontal_words_eq_one
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (p : ℕ) (hp : p < D.steps) :
    let frames := D.gaugeGridRowFramesAt hxU hxV hUV hU hV p hp
    let S := D.framedHorizontalFullRowState hxU hxV hUV hU hV
      ⟨p, hp⟩ frames (D.gaugeGridRowFramesAt_compatible
        hxU hxV hUV hU hV p hp)
    S.topWord = 1 ∧ S.boundary.after * S.bottomPrefix = 1 := by
  exact D.gaugeGridFramedRowPrefix_horizontal_words_eq_one
    hxU hxV hUV hU hV p hp (D.steps - 1)
      (Nat.sub_lt D.steps_pos Nat.zero_lt_one)

/-- 二维 gauge frames 上第 `p` 行的左右外边词严格相等。-/
private theorem BinaryOpenCoverSquareSubdivision.gaugeGridFramedFullRow_leftEdge_eq_rightEdge
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (p : ℕ) (hp : p < D.steps) :
    let frames := D.gaugeGridRowFramesAt hxU hxV hUV hU hV p hp
    let S := D.framedHorizontalFullRowState hxU hxV hUV hU hV
      ⟨p, hp⟩ frames (D.gaugeGridRowFramesAt_compatible
        hxU hxV hUV hU hV p hp)
    S.leftEdge = S.boundary.focus := by
  let frames := D.gaugeGridRowFramesAt hxU hxV hUV hU hV p hp
  let compat := D.gaugeGridRowFramesAt_compatible
    hxU hxV hUV hU hV p hp
  let S := D.framedHorizontalFullRowState hxU hxV hUV hU hV
    ⟨p, hp⟩ frames compat
  have hrel := D.framedHorizontalFullRowState_standard_relation
    hxU hxV hUV hU hV ⟨p, hp⟩ frames compat
  have hwords := D.gaugeGridFramedFullRow_horizontal_words_eq_one
    hxU hxV hUV hU hV p hp
  change S.leftEdge⁻¹ * S.topWord⁻¹ * S.boundary.focus *
      (S.boundary.after * S.bottomPrefix) = 1 at hrel
  change S.topWord = 1 ∧ S.boundary.after * S.bottomPrefix = 1 at hwords
  rw [hwords.1, hwords.2] at hrel
  simp only [inv_one, mul_one] at hrel
  have hmul := congrArg (fun z => S.leftEdge * z) hrel
  simpa [mul_assoc] using hmul.symm

/-- 二维 gauge frames 上第 `p` 行的完整 framed-row 状态。-/
private noncomputable def BinaryOpenCoverSquareSubdivision.gaugeGridFramedFullRowStateAt
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (p : ℕ) (hp : p < D.steps) :=
  D.framedHorizontalFullRowState hxU hxV hUV hU hV ⟨p, hp⟩
    (D.gaugeGridRowFramesAt hxU hxV hUV hU hV p hp)
    (D.gaugeGridRowFramesAt_compatible hxU hxV hUV hU hV p hp)

/-- 从底行到第 `p` 行，按二维 gauge 状态累积左外侧竖边词。-/
noncomputable def BinaryOpenCoverSquareSubdivision.gaugeGridLeftBoundaryWordAt
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V) :
    (p : ℕ) → (hp : p < D.steps) → binaryVanKampenPushout U V hxU hxV
  | 0, hp =>
      (D.gaugeGridFramedFullRowStateAt hxU hxV hUV hU hV 0 hp).leftEdge
  | p + 1, hp =>
      let hp' : p < D.steps := Nat.lt_trans (Nat.lt_succ_self p) hp
      (D.gaugeGridFramedFullRowStateAt hxU hxV hUV hU hV (p + 1) hp).leftEdge *
        D.gaugeGridLeftBoundaryWordAt hxU hxV hUV hU hV p hp'

/-- 从底行到第 `p` 行，按二维 gauge 状态累积右外侧竖边词。-/
noncomputable def BinaryOpenCoverSquareSubdivision.gaugeGridRightBoundaryWordAt
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V) :
    (p : ℕ) → (hp : p < D.steps) → binaryVanKampenPushout U V hxU hxV
  | 0, hp =>
      (D.gaugeGridFramedFullRowStateAt hxU hxV hUV hU hV 0 hp).boundary.focus
  | p + 1, hp =>
      let hp' : p < D.steps := Nat.lt_trans (Nat.lt_succ_self p) hp
      (D.gaugeGridFramedFullRowStateAt hxU hxV hUV hU hV (p + 1) hp).boundary.focus *
        D.gaugeGridRightBoundaryWordAt hxU hxV hUV hU hV p hp'

/-- 每行左右外边相等沿行号累积后，任意高度前缀的左右整侧词严格相等。
@isnad1 id=eq.6h7v.s7.e80c484ea147 from=translated src=- shape=574dc720 vocab=f592df0d
-/
theorem BinaryOpenCoverSquareSubdivision.gaugeGridBoundaryWordsAt_left_eq_right
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V) :
    ∀ (p : ℕ) (hp : p < D.steps),
      D.gaugeGridLeftBoundaryWordAt hxU hxV hUV hU hV p hp =
        D.gaugeGridRightBoundaryWordAt hxU hxV hUV hU hV p hp
  | 0, hp =>
      D.gaugeGridFramedFullRow_leftEdge_eq_rightEdge
        hxU hxV hUV hU hV 0 hp
  | p + 1, hp => by
      have hp' : p < D.steps := Nat.lt_trans (Nat.lt_succ_self p) hp
      have hrow := D.gaugeGridFramedFullRow_leftEdge_eq_rightEdge
        hxU hxV hUV hU hV (p + 1) hp
      change (D.gaugeGridFramedFullRowStateAt hxU hxV hUV hU hV
        (p + 1) hp).leftEdge =
        (D.gaugeGridFramedFullRowStateAt hxU hxV hUV hU hV
          (p + 1) hp).boundary.focus at hrow
      rw [BinaryOpenCoverSquareSubdivision.gaugeGridLeftBoundaryWordAt,
        BinaryOpenCoverSquareSubdivision.gaugeGridRightBoundaryWordAt,
        hrow,
        D.gaugeGridBoundaryWordsAt_left_eq_right hxU hxV hUV hU hV p hp']

/-- 整张有限方格在二维 gauge 下只剩左右外侧 holonomy，且两者严格相等。
@isnad1 id=eq.5h6v.s7.a3b760ffe30f from=translated src=- shape=bd6203fe vocab=0100b368
-/
theorem BinaryOpenCoverSquareSubdivision.gaugeGridFullBoundary_left_eq_right
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V) :
    D.gaugeGridLeftBoundaryWordAt hxU hxV hUV hU hV
        (D.steps - 1) (Nat.sub_lt D.steps_pos Nat.zero_lt_one) =
      D.gaugeGridRightBoundaryWordAt hxU hxV hUV hU hV
        (D.steps - 1) (Nat.sub_lt D.steps_pos Nat.zero_lt_one) :=
  D.gaugeGridBoundaryWordsAt_left_eq_right hxU hxV hUV hU hV
    (D.steps - 1) (Nat.sub_lt D.steps_pos Nat.zero_lt_one)

/-- 任意水平相容 frame family 中，只要每个单格的上下横边都归一化为 `1`，任意行前缀的
完整上、下边界词也都为 `1`。-/
private theorem BinaryOpenCoverSquareSubdivision.framedRowPrefix_horizontal_words_eq_one
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (j : Fin D.steps)
    (frames : Fin D.steps → CellVertexFrames
      (binaryVanKampenPushout U V hxU hxV))
    (hcompat : ∀ (i k : Fin D.steps) (hshared : i.succ = k.castSucc),
      HorizontalCellFramesCompatible
        (D.horizontalInternalEdgeTransitions hxU hxV hUV hU hV i k j hshared)
        (frames i) (frames k))
    (hedges : ∀ i : Fin D.steps,
      rebaseEdge (frames i).bottomLeft (frames i).bottomRight
          (Monoid.PushoutI.of (D.label i j)
            (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i j 0)) = 1 ∧
        rebaseEdge (frames i).topLeft (frames i).topRight
          (Monoid.PushoutI.of (D.label i j)
            (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i j 1)) = 1) :
    ∀ (q : ℕ) (hq : q < D.steps),
      let S := D.framedHorizontalRowPrefixState hxU hxV hUV hU hV
        j frames hcompat q hq
      S.topWord = 1 ∧ S.boundary.after * S.bottomPrefix = 1
  | 0, hq => by
      let i : Fin D.steps := ⟨0, hq⟩
      let S := D.framedHorizontalRowPrefixState hxU hxV hUV hU hV
        j frames hcompat 0 hq
      change rebaseEdge (frames i).topLeft (frames i).topRight
            (Monoid.PushoutI.of (D.label i j)
              (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i j 1)) = 1 ∧
        rebaseEdge (frames i).bottomLeft (frames i).bottomRight
            (Monoid.PushoutI.of (D.label i j)
              (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i j 0)) * 1 = 1
      exact ⟨(hedges i).2, by simpa using (hedges i).1⟩
  | q + 1, hq => by
      have hq' : q < D.steps := Nat.lt_trans (Nat.lt_succ_self q) hq
      let previous := D.framedHorizontalRowPrefixState hxU hxV hUV hU hV
        j frames hcompat q hq'
      let current := D.framedHorizontalRowPrefixState hxU hxV hUV hU hV
        j frames hcompat (q + 1) hq
      let k : Fin D.steps := ⟨q + 1, hq⟩
      have ih := D.framedRowPrefix_horizontal_words_eq_one hxU hxV hUV hU hV
        j frames hcompat hedges q hq'
      have hedge := hedges k
      change current.topWord = 1 ∧
        current.boundary.after * current.bottomPrefix = 1
      change previous.topWord = 1 ∧
        previous.boundary.after * previous.bottomPrefix = 1 at ih
      have htop : current.topWord =
          rebaseEdge (frames k).topLeft (frames k).topRight
            (Monoid.PushoutI.of (D.label k j)
              (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV k j 1)) *
            previous.topWord := by rfl
      have hbottom : current.boundary.after * current.bottomPrefix =
          rebaseEdge (frames k).bottomLeft (frames k).bottomRight
            (Monoid.PushoutI.of (D.label k j)
              (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV k j 0)) *
            (previous.boundary.after * previous.bottomPrefix) := by
        rw [current.after_eq]
        rfl
      rw [htop, hbottom, hedge.2, hedge.1, ih.1, ih.2]
      simp

/-- 上述逐格归一化假设下，完整单行的左右外边 framed 元素严格相等。
@isnad1 id=other.7h8v.s12.4423c63e3fef from=translated src=- shape=ecd12e8a vocab=667cef59
-/
theorem BinaryOpenCoverSquareSubdivision.framedFullRow_leftEdge_eq_rightEdge
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (j : Fin D.steps)
    (frames : Fin D.steps → CellVertexFrames
      (binaryVanKampenPushout U V hxU hxV))
    (hcompat : ∀ (i k : Fin D.steps) (hshared : i.succ = k.castSucc),
      HorizontalCellFramesCompatible
        (D.horizontalInternalEdgeTransitions hxU hxV hUV hU hV i k j hshared)
        (frames i) (frames k))
    (hedges : ∀ i : Fin D.steps,
      rebaseEdge (frames i).bottomLeft (frames i).bottomRight
          (Monoid.PushoutI.of (D.label i j)
            (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i j 0)) = 1 ∧
        rebaseEdge (frames i).topLeft (frames i).topRight
          (Monoid.PushoutI.of (D.label i j)
            (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i j 1)) = 1) :
    let S := D.framedHorizontalFullRowState hxU hxV hUV hU hV j frames hcompat
    S.leftEdge = S.boundary.focus := by
  let S := D.framedHorizontalFullRowState hxU hxV hUV hU hV j frames hcompat
  have hrel := D.framedHorizontalFullRowState_standard_relation
    hxU hxV hUV hU hV j frames hcompat
  have hwords := D.framedRowPrefix_horizontal_words_eq_one
    hxU hxV hUV hU hV j frames hcompat hedges
    (D.steps - 1) (Nat.sub_lt D.steps_pos Nat.zero_lt_one)
  change S.leftEdge⁻¹ * S.topWord⁻¹ * S.boundary.focus *
      (S.boundary.after * S.bottomPrefix) = 1 at hrel
  change S.topWord = 1 ∧ S.boundary.after * S.bottomPrefix = 1 at hwords
  rw [hwords.1, hwords.2] at hrel
  simp only [inv_one, mul_one] at hrel
  have hmul := congrArg (fun z => S.leftEdge * z) hrel
  simpa [mul_assoc] using hmul.symm

end SandronesLibrary.Topology
