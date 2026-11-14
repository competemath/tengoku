/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.VanKampenSwitchSharedEdge

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# van Kampen 内部边的统一 gauge 与有限望远镜公式

本文件把同标签和异标签公共边关系统一为纯群论 `rebaseEdge` 语言，并证明有限边链的中间 frame
严格望远镜消去。`EdgeTransitions` 只保存内部边起终点的两个变换；水平和竖直统一关系在定义层
隐藏标签分类，使后续网格证明不再重复区分 common/switch 情形。

当前条目：

* `topology.fundamental-group.van-kampen-edge-gauge`。

本文件不执行整张网格的 perimeter/row telescope，不证明 kernel 消失、单射或 van Kampen 同构。
-/

open Set
open scoped unitInterval

noncomputable section

namespace SandronesLibrary.Topology

variable {X : Type*} [TopologicalSpace X]

/-- 两个定向面词沿一条方向相反的公共边粘合后，公共边可在非交换群中严格消去。

若左面词为 `beforeL * shared * afterL`，右面词为
`beforeR * shared⁻¹ * afterR`，则粘合后的外边界顺序是
`beforeR * afterL * beforeL * afterR`。这个次序不能交换。

> **Entry**: topology.fundamental-group.van-kampen-edge-gauge-/
theorem twoCellBoundary_glue
    {G : Type*} [Group G]
    (beforeL shared afterL beforeR afterR : G)
    (hL : beforeL * shared * afterL = 1)
    (hR : beforeR * shared⁻¹ * afterR = 1) :
    beforeR * afterL * beforeL * afterR = 1 := by
  have hshared : shared = beforeL⁻¹ * afterL⁻¹ := by
    calc
      shared = beforeL⁻¹ * (beforeL * shared * afterL) * afterL⁻¹ := by
        simp [mul_assoc]
      _ = beforeL⁻¹ * afterL⁻¹ := by rw [hL]; simp
  calc
    beforeR * afterL * beforeL * afterR =
        beforeR * shared⁻¹ * afterR := by rw [hshared]; simp [mul_assoc]
    _ = 1 := hR

/-- 用起终点处的连接变换重新表示一条定向边。基本群的道路乘法为反序，故终点变换在左。-/
def rebaseEdge {G : Type*} [Group G] (startChange endChange edge : G) : G :=
  endChange⁻¹ * edge * startChange

@[simp] theorem rebaseEdge_one_changes
    {G : Type*} [Group G] (edge : G) :
    rebaseEdge 1 1 edge = edge := by
  simp [rebaseEdge]

/-- 两条首尾相接的边换连接后按道路反序相乘，中间顶点的变换因子严格消去。-/
private theorem rebaseEdge_mul
    {G : Type*} [Group G]
    (startChange middleChange endChange first second : G) :
    rebaseEdge middleChange endChange second *
        rebaseEdge startChange middleChange first =
      rebaseEdge startChange endChange (second * first) := by
  simp [rebaseEdge, mul_assoc]

/-- 给定边元素和左端 frame，把右端 frame 取为 `edge * startChange`，
则该边在两端 frames 下严格规范化为单位元。-/
@[simp] theorem rebaseEdge_mul_start_eq_one
    {G : Type*} [Group G] (startChange edge : G) :
    rebaseEdge startChange (edge * startChange) edge = 1 := by
  simp [rebaseEdge, mul_assoc]

/-- 反向边的换连接表示，是原换连接边的逆元。-/
private theorem rebaseEdge_inv
    {G : Type*} [Group G] (startChange endChange edge : G) :
    rebaseEdge endChange startChange edge⁻¹ =
      (rebaseEdge startChange endChange edge)⁻¹ := by
  simp [rebaseEdge, mul_assoc]

/-- 闭合边词的所有顶点变换望远镜消去后，只剩基点处的共轭。-/
private theorem rebaseEdge_cycle_four
    {G : Type*} [Group G]
    (t₀ t₁ t₂ t₃ e₀ e₁ e₂ e₃ : G) :
    rebaseEdge t₃ t₀ e₃ * rebaseEdge t₂ t₃ e₂ *
          rebaseEdge t₁ t₂ e₁ * rebaseEdge t₀ t₁ e₀ =
      t₀⁻¹ * (e₃ * e₂ * e₁ * e₀) * t₀ := by
  simp [rebaseEdge, mul_assoc]

/-- 两套 connector 比较给出的边关系，等价于由两端 transition 控制的 `rebaseEdge`。-/
theorem edgeElements_eq_rebaseEdge_of_change_relations
    {G : Type*} [Group G] (endL startL commonL cellL : G)
    (endR startR commonR cellR : G)
    (hL : endL⁻¹ * commonL * startL = cellL)
    (hR : endR⁻¹ * commonR * startR = cellR)
    (hcommon : commonL = commonR) :
    cellL = rebaseEdge (startR⁻¹ * startL) (endR⁻¹ * endL) cellR := by
  rw [edgeElements_eq_of_change_relations endL startL commonL cellL
    endR startR commonR cellR hL hR hcommon]
  simp [rebaseEdge, mul_assoc]

/-- 水平异标签公共边关系的端点 gauge 形式；这是有限网格望远镜消去使用的接口。-/
private theorem BinaryOpenCoverSquareSubdivision.horizontalSwitchEdge_pushout_rebase
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (hswitch : D.label i j ≠ D.label k j) :
    let CL := D.horizontalSwitchLeftConnectorComparison hxU hxV hUV hU hV
      i k j hshared hswitch
    let CR := D.horizontalSwitchRightConnectorComparison hxU hxV hUV hU hV
      i k j hshared hswitch
    (Monoid.PushoutI.of (D.label i j)
        (D.gridCellBasedVerticalEdgeInPiece hxU hxV hU hV i j 1) :
      binaryVanKampenPushout U V hxU hxV) =
      rebaseEdge
        ((Monoid.PushoutI.of (D.label k j) CR.startChange)⁻¹ *
          Monoid.PushoutI.of (D.label i j) CL.startChange)
        ((Monoid.PushoutI.of (D.label k j) CR.endChange)⁻¹ *
          Monoid.PushoutI.of (D.label i j) CL.endChange)
        (Monoid.PushoutI.of (D.label k j)
          (D.gridCellBasedVerticalEdgeInPiece hxU hxV hU hV k j 0)) := by
  dsimp only
  rw [D.horizontalSwitchEdge_pushout_relation hxU hxV hUV hU hV
    i k j hshared hswitch]
  simp [rebaseEdge, mul_assoc]

/-- 竖直异标签公共边关系的端点 gauge 形式。-/
private theorem BinaryOpenCoverSquareSubdivision.verticalSwitchEdge_pushout_rebase
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (hswitch : D.label i j ≠ D.label i l) :
    let CB := D.verticalSwitchBottomConnectorComparison hxU hxV hUV hU hV
      i j l hshared hswitch
    let CT := D.verticalSwitchTopConnectorComparison hxU hxV hUV hU hV
      i j l hshared hswitch
    (Monoid.PushoutI.of (D.label i j)
        (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i j 1) :
      binaryVanKampenPushout U V hxU hxV) =
      rebaseEdge
        ((Monoid.PushoutI.of (D.label i l) CT.startChange)⁻¹ *
          Monoid.PushoutI.of (D.label i j) CB.startChange)
        ((Monoid.PushoutI.of (D.label i l) CT.endChange)⁻¹ *
          Monoid.PushoutI.of (D.label i j) CB.endChange)
        (Monoid.PushoutI.of (D.label i l)
          (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i l 0)) := by
  dsimp only
  rw [D.verticalSwitchEdge_pushout_relation hxU hxV hUV hU hV
    i j l hshared hswitch]
  simp [rebaseEdge, mul_assoc]

private theorem BinaryOpenCoverSquareSubdivision.gridCellBasedHorizontalEdgeInPieceOfLabel_self
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j : Fin D.steps) (row : Fin 2) :
    D.gridCellBasedHorizontalEdgeInPieceOfLabel hxU hxV hU hV
        i j row (D.label i j) rfl =
      D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i j row := by
  rfl

private theorem BinaryOpenCoverSquareSubdivision.gridCellBasedVerticalEdgeInPieceOfLabel_self
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j : Fin D.steps) (column : Fin 2) :
    D.gridCellBasedVerticalEdgeInPieceOfLabel hxU hxV hU hV
        i j column (D.label i j) rfl =
      D.gridCellBasedVerticalEdgeInPiece hxU hxV hU hV i j column := by
  rfl

/-- 显式共同标签横边送入 Pushout 后就是该格实际标签的旧横边。-/
private theorem BinaryOpenCoverSquareSubdivision.pushout_horizontalEdgeOfLabel_eq
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j : Fin D.steps) (row : Fin 2) (b : Bool)
    (hb : D.label i j = b) :
    (Monoid.PushoutI.of b
        (D.gridCellBasedHorizontalEdgeInPieceOfLabel hxU hxV hU hV
          i j row b hb) : binaryVanKampenPushout U V hxU hxV) =
      Monoid.PushoutI.of
        (φ := binaryOpenCoverIntersectionMaps U V hxU hxV) (D.label i j)
        (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i j row) := by
  cases hb
  rw [D.gridCellBasedHorizontalEdgeInPieceOfLabel_self]

/-- 显式共同标签竖边送入 Pushout 后就是该格实际标签的旧竖边。-/
private theorem BinaryOpenCoverSquareSubdivision.pushout_verticalEdgeOfLabel_eq
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j : Fin D.steps) (column : Fin 2) (b : Bool)
    (hb : D.label i j = b) :
    (Monoid.PushoutI.of b
        (D.gridCellBasedVerticalEdgeInPieceOfLabel hxU hxV hU hV
          i j column b hb) : binaryVanKampenPushout U V hxU hxV) =
      Monoid.PushoutI.of (D.label i j)
        (D.gridCellBasedVerticalEdgeInPiece hxU hxV hU hV i j column) := by
  cases hb
  rw [D.gridCellBasedVerticalEdgeInPieceOfLabel_self]

/-- 反解一条端点 gauge 关系。-/
theorem eq_rebaseEdge_of_rebaseEdge_eq
    {G : Type*} [Group G] (startChange endChange left right : G)
    (h : rebaseEdge startChange endChange left = right) :
    left = rebaseEdge startChange⁻¹ endChange⁻¹ right := by
  rw [← h]
  simp [rebaseEdge, mul_assoc]

/-- 水平同标签公共边在 Pushout 中的端点 gauge 形式。-/
private theorem BinaryOpenCoverSquareSubdivision.horizontalCommonEdge_pushout_rebase
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (hlabel : D.label i j = D.label k j) :
    let C := D.horizontalCommonEdgeConnectorComparison hxU hxV hU hV
      i k j hshared hlabel
    (Monoid.PushoutI.of (D.label i j)
        (D.gridCellBasedVerticalEdgeInPiece hxU hxV hU hV i j 1) :
      binaryVanKampenPushout U V hxU hxV) =
      rebaseEdge
        (Monoid.PushoutI.of (D.label i j) C.startChange)⁻¹
        (Monoid.PushoutI.of (D.label i j) C.endChange)⁻¹
        (Monoid.PushoutI.of (D.label k j)
          (D.gridCellBasedVerticalEdgeInPiece hxU hxV hU hV k j 0)) := by
  dsimp only
  let C := D.horizontalCommonEdgeConnectorComparison hxU hxV hU hV
    i k j hshared hlabel
  let f := (Monoid.PushoutI.of
      (φ := binaryOpenCoverIntersectionMaps U V hxU hxV) (D.label i j) :
      FundamentalGroup (binaryOpenCoverPiece U V (D.label i j))
        (binaryOpenCoverBasepoint hxU hxV (D.label i j)) →*
      binaryVanKampenPushout U V hxU hxV)
  have h := congrArg f
    (D.horizontalCommonEdge_pieceElements_relation hxU hxV hU hV
      i k j hshared hlabel)
  simp only [map_mul, map_inv] at h
  rw [D.pushout_verticalEdgeOfLabel_eq hxU hxV hU hV
    k j 0 (D.label i j) hlabel.symm] at h
  apply eq_rebaseEdge_of_rebaseEdge_eq (f C.startChange) (f C.endChange)
  simpa [rebaseEdge] using h

/-- 竖直同标签公共边在 Pushout 中的端点 gauge 形式。-/
private theorem BinaryOpenCoverSquareSubdivision.verticalCommonEdge_pushout_rebase
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (hlabel : D.label i j = D.label i l) :
    let C := D.verticalCommonEdgeConnectorComparison hxU hxV hU hV
      i j l hshared hlabel
    (Monoid.PushoutI.of (D.label i j)
        (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i j 1) :
      binaryVanKampenPushout U V hxU hxV) =
      rebaseEdge
        (Monoid.PushoutI.of (D.label i j) C.startChange)⁻¹
        (Monoid.PushoutI.of (D.label i j) C.endChange)⁻¹
        (Monoid.PushoutI.of (D.label i l)
          (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i l 0)) := by
  dsimp only
  let C := D.verticalCommonEdgeConnectorComparison hxU hxV hU hV
    i j l hshared hlabel
  let f := (Monoid.PushoutI.of
      (φ := binaryOpenCoverIntersectionMaps U V hxU hxV) (D.label i j) :
      FundamentalGroup (binaryOpenCoverPiece U V (D.label i j))
        (binaryOpenCoverBasepoint hxU hxV (D.label i j)) →*
      binaryVanKampenPushout U V hxU hxV)
  have h := congrArg f
    (D.verticalCommonEdge_pieceElements_relation hxU hxV hU hV
      i j l hshared hlabel)
  simp only [map_mul, map_inv] at h
  rw [D.pushout_horizontalEdgeOfLabel_eq hxU hxV hU hV
    i l 0 (D.label i j) hlabel.symm] at h
  apply eq_rebaseEdge_of_rebaseEdge_eq (f C.startChange) (f C.endChange)
  simpa [rebaseEdge] using h

/-- 只保存一条内部边两端的 gauge 变换；关系证明与数据分离以避免依赖证明展开。-/
structure EdgeTransitions (G : Type*) where
  startChange : G
  endChange : G

noncomputable def BinaryOpenCoverSquareSubdivision.horizontalCommonEdgeTransitions
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (hlabel : D.label i j = D.label k j) :
    EdgeTransitions (binaryVanKampenPushout U V hxU hxV) :=
  let C := D.horizontalCommonEdgeConnectorComparison hxU hxV hU hV
    i k j hshared hlabel
  { startChange := (Monoid.PushoutI.of (D.label i j) C.startChange)⁻¹
    endChange := (Monoid.PushoutI.of (D.label i j) C.endChange)⁻¹ }

private theorem BinaryOpenCoverSquareSubdivision.horizontalCommonEdge_relation_transitions
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (hlabel : D.label i j = D.label k j) :
    let T := D.horizontalCommonEdgeTransitions hxU hxV hU hV
      i k j hshared hlabel
    (Monoid.PushoutI.of (D.label i j)
        (D.gridCellBasedVerticalEdgeInPiece hxU hxV hU hV i j 1) :
      binaryVanKampenPushout U V hxU hxV) =
      rebaseEdge T.startChange T.endChange
        (Monoid.PushoutI.of (D.label k j)
          (D.gridCellBasedVerticalEdgeInPiece hxU hxV hU hV k j 0)) := by
  exact D.horizontalCommonEdge_pushout_rebase hxU hxV hU hV
    i k j hshared hlabel

noncomputable def BinaryOpenCoverSquareSubdivision.horizontalSwitchEdgeTransitions
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (hswitch : D.label i j ≠ D.label k j) :
    EdgeTransitions (binaryVanKampenPushout U V hxU hxV) :=
  let CL := D.horizontalSwitchLeftConnectorComparison hxU hxV hUV hU hV
    i k j hshared hswitch
  let CR := D.horizontalSwitchRightConnectorComparison hxU hxV hUV hU hV
    i k j hshared hswitch
  { startChange := (Monoid.PushoutI.of (D.label k j) CR.startChange)⁻¹ *
      Monoid.PushoutI.of (D.label i j) CL.startChange
    endChange := (Monoid.PushoutI.of (D.label k j) CR.endChange)⁻¹ *
      Monoid.PushoutI.of (D.label i j) CL.endChange }

private theorem BinaryOpenCoverSquareSubdivision.horizontalSwitchEdge_relation_transitions
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (hswitch : D.label i j ≠ D.label k j) :
    let T := D.horizontalSwitchEdgeTransitions hxU hxV hUV hU hV
      i k j hshared hswitch
    (Monoid.PushoutI.of (D.label i j)
        (D.gridCellBasedVerticalEdgeInPiece hxU hxV hU hV i j 1) :
      binaryVanKampenPushout U V hxU hxV) =
      rebaseEdge T.startChange T.endChange
        (Monoid.PushoutI.of (D.label k j)
          (D.gridCellBasedVerticalEdgeInPiece hxU hxV hU hV k j 0)) := by
  exact D.horizontalSwitchEdge_pushout_rebase hxU hxV hUV hU hV
    i k j hshared hswitch

noncomputable def BinaryOpenCoverSquareSubdivision.horizontalInternalEdgeTransitions
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc) :
    EdgeTransitions (binaryVanKampenPushout U V hxU hxV) :=
  if hlabel : D.label i j = D.label k j then
    D.horizontalCommonEdgeTransitions hxU hxV hU hV i k j hshared hlabel
  else
    D.horizontalSwitchEdgeTransitions hxU hxV hUV hU hV i k j hshared hlabel

theorem BinaryOpenCoverSquareSubdivision.horizontalInternalEdge_relation
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc) :
    let T := D.horizontalInternalEdgeTransitions hxU hxV hUV hU hV
      i k j hshared
    (Monoid.PushoutI.of (D.label i j)
        (D.gridCellBasedVerticalEdgeInPiece hxU hxV hU hV i j 1) :
      binaryVanKampenPushout U V hxU hxV) =
      rebaseEdge T.startChange T.endChange
        (Monoid.PushoutI.of (D.label k j)
          (D.gridCellBasedVerticalEdgeInPiece hxU hxV hU hV k j 0)) := by
  by_cases hlabel : D.label i j = D.label k j
  · rw [BinaryOpenCoverSquareSubdivision.horizontalInternalEdgeTransitions,
      dite_eq_left hlabel]
    exact D.horizontalCommonEdge_relation_transitions hxU hxV hU hV
      i k j hshared hlabel
  · rw [BinaryOpenCoverSquareSubdivision.horizontalInternalEdgeTransitions,
      dite_eq_right hlabel]
    exact D.horizontalSwitchEdge_relation_transitions hxU hxV hUV hU hV
      i k j hshared hlabel

noncomputable def BinaryOpenCoverSquareSubdivision.verticalCommonEdgeTransitions
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (hlabel : D.label i j = D.label i l) :
    EdgeTransitions (binaryVanKampenPushout U V hxU hxV) :=
  let C := D.verticalCommonEdgeConnectorComparison hxU hxV hU hV
    i j l hshared hlabel
  { startChange := (Monoid.PushoutI.of (D.label i j) C.startChange)⁻¹
    endChange := (Monoid.PushoutI.of (D.label i j) C.endChange)⁻¹ }

private theorem BinaryOpenCoverSquareSubdivision.verticalCommonEdge_relation_transitions
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (hlabel : D.label i j = D.label i l) :
    let T := D.verticalCommonEdgeTransitions hxU hxV hU hV
      i j l hshared hlabel
    (Monoid.PushoutI.of (D.label i j)
        (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i j 1) :
      binaryVanKampenPushout U V hxU hxV) =
      rebaseEdge T.startChange T.endChange
        (Monoid.PushoutI.of (D.label i l)
          (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i l 0)) := by
  exact D.verticalCommonEdge_pushout_rebase hxU hxV hU hV
    i j l hshared hlabel

noncomputable def BinaryOpenCoverSquareSubdivision.verticalSwitchEdgeTransitions
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (hswitch : D.label i j ≠ D.label i l) :
    EdgeTransitions (binaryVanKampenPushout U V hxU hxV) :=
  let CB := D.verticalSwitchBottomConnectorComparison hxU hxV hUV hU hV
    i j l hshared hswitch
  let CT := D.verticalSwitchTopConnectorComparison hxU hxV hUV hU hV
    i j l hshared hswitch
  { startChange := (Monoid.PushoutI.of (D.label i l) CT.startChange)⁻¹ *
      Monoid.PushoutI.of (D.label i j) CB.startChange
    endChange := (Monoid.PushoutI.of (D.label i l) CT.endChange)⁻¹ *
      Monoid.PushoutI.of (D.label i j) CB.endChange }

private theorem BinaryOpenCoverSquareSubdivision.verticalSwitchEdge_relation_transitions
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (hswitch : D.label i j ≠ D.label i l) :
    let T := D.verticalSwitchEdgeTransitions hxU hxV hUV hU hV
      i j l hshared hswitch
    (Monoid.PushoutI.of (D.label i j)
        (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i j 1) :
      binaryVanKampenPushout U V hxU hxV) =
      rebaseEdge T.startChange T.endChange
        (Monoid.PushoutI.of (D.label i l)
          (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i l 0)) := by
  exact D.verticalSwitchEdge_pushout_rebase hxU hxV hUV hU hV
    i j l hshared hswitch

noncomputable def BinaryOpenCoverSquareSubdivision.verticalInternalEdgeTransitions
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc) :
    EdgeTransitions (binaryVanKampenPushout U V hxU hxV) :=
  if hlabel : D.label i j = D.label i l then
    D.verticalCommonEdgeTransitions hxU hxV hU hV i j l hshared hlabel
  else
    D.verticalSwitchEdgeTransitions hxU hxV hUV hU hV i j l hshared hlabel

theorem BinaryOpenCoverSquareSubdivision.verticalInternalEdge_relation
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc) :
    let T := D.verticalInternalEdgeTransitions hxU hxV hUV hU hV
      i j l hshared
    (Monoid.PushoutI.of (D.label i j)
        (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i j 1) :
      binaryVanKampenPushout U V hxU hxV) =
      rebaseEdge T.startChange T.endChange
        (Monoid.PushoutI.of (D.label i l)
          (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i l 0)) := by
  by_cases hlabel : D.label i j = D.label i l
  · rw [BinaryOpenCoverSquareSubdivision.verticalInternalEdgeTransitions,
      dite_eq_left hlabel]
    exact D.verticalCommonEdge_relation_transitions hxU hxV hU hV
      i j l hshared hlabel
  · rw [BinaryOpenCoverSquareSubdivision.verticalInternalEdgeTransitions,
      dite_eq_right hlabel]
    exact D.verticalSwitchEdge_relation_transitions hxU hxV hUV hU hV
      i j l hshared hlabel

/-- 按道路乘法的反序约定，取有限边链的边词。每项第一坐标保存该边终点的 transition。-/
def reverseEdgeChainProduct {G : Type*} [Group G] : List (G × G) → G
  | [] => 1
  | (_, edge) :: rest => reverseEdgeChainProduct rest * edge

/-- 反序边链乘积就是取第二坐标后反转列表的通常乘积。-/
theorem reverseEdgeChainProduct_eq_reverse_map_snd_prod
    {G : Type*} [Group G] (chain : List (G × G)) :
    reverseEdgeChainProduct chain = (chain.map Prod.snd).reverse.prod := by
  induction chain with
  | nil => rfl
  | cons head rest ih =>
      rcases head with ⟨endChange, edge⟩
      simp only [reverseEdgeChainProduct, List.map_cons, List.reverse_cons,
        List.prod_append, List.prod_singleton]
      rw [ih]

/-- Reverse edge products turn concatenation into multiplication in the opposite
block order.-/
theorem reverseEdgeChainProduct_append
    {G : Type*} [Group G] (first second : List (G × G)) :
    reverseEdgeChainProduct (first ++ second) =
      reverseEdgeChainProduct second * reverseEdgeChainProduct first := by
  rw [reverseEdgeChainProduct_eq_reverse_map_snd_prod,
    reverseEdgeChainProduct_eq_reverse_map_snd_prod,
    reverseEdgeChainProduct_eq_reverse_map_snd_prod]
  simp [List.prod_append]

/-- 有限边链的最终顶点 transition。-/
def edgeChainEnd {G : Type*} (startChange : G) : List (G × G) → G
  | [] => startChange
  | (endChange, _) :: rest => edgeChainEnd endChange rest

/-- 非空 `Fin` 边链的最终 transition 就是最后一项保存的终点 transition。-/
private theorem edgeChainEnd_ofFn_succ
    {G : Type*} (n : ℕ) (startChange : G)
    (endChange edge : Fin (n + 1) → G) :
    edgeChainEnd startChange (List.ofFn fun k => (endChange k, edge k)) =
      endChange (Fin.last n) := by
  induction n generalizing startChange with
  | zero => simp [edgeChainEnd, List.ofFn_succ]
  | succ n ih =>
      rw [List.ofFn_succ, edgeChainEnd]
      rw [ih]
      rfl

/-- 任意正自然数的规范最后一个 `Fin` 下标。-/
def finLastOfPos (n : ℕ) (hn : 0 < n) : Fin n :=
  ⟨n - 1, Nat.sub_lt hn Nat.zero_lt_one⟩

@[simp] theorem finLastOfPos_succ (n : ℕ) (hn : 0 < n + 1) :
    finLastOfPos (n + 1) hn = Fin.last n := by
  apply Fin.ext
  simp [finLastOfPos]

/-- 任意正长度 `Fin` 边链的最终 transition，是其规范最后一项保存的终点 transition。-/
theorem edgeChainEnd_ofFn_of_pos
    {G : Type*} (n : ℕ) (hn : 0 < n) (startChange : G)
    (endChange edge : Fin n → G) :
    edgeChainEnd startChange (List.ofFn fun k => (endChange k, edge k)) =
      endChange (finLastOfPos n hn) := by
  cases n with
  | zero => exact (Nat.not_lt_zero 0 hn).elim
  | succ n =>
      simpa using edgeChainEnd_ofFn_succ n startChange endChange edge

/-- 将有限边链的每条边分别按其起终点 transition 换连接，再按道路反序相乘。-/
def rebasedEdgeChainProduct {G : Type*} [Group G] (startChange : G) :
    List (G × G) → G
  | [] => 1
  | (endChange, edge) :: rest =>
      rebasedEdgeChainProduct endChange rest *
        rebaseEdge startChange endChange edge

/-- 任意有限边链的所有中间顶点 transition 严格望远镜消去。-/
theorem rebasedEdgeChainProduct_eq_rebaseEdge
    {G : Type*} [Group G] (startChange : G) (chain : List (G × G)) :
    rebasedEdgeChainProduct startChange chain =
      rebaseEdge startChange (edgeChainEnd startChange chain)
        (reverseEdgeChainProduct chain) := by
  induction chain generalizing startChange with
  | nil => simp [rebasedEdgeChainProduct, edgeChainEnd,
      reverseEdgeChainProduct, rebaseEdge]
  | cons head rest ih =>
      rcases head with ⟨endChange, edge⟩
      rw [rebasedEdgeChainProduct, ih]
      rw [reverseEdgeChainProduct, edgeChainEnd]
      exact rebaseEdge_mul startChange endChange
        (edgeChainEnd endChange rest) edge (reverseEdgeChainProduct rest)

/-- 闭合有限边链换连接后，只剩所选基点 transition 的共轭。-/
theorem rebasedEdgeChainProduct_eq_conj_of_end_eq
    {G : Type*} [Group G] (startChange : G) (chain : List (G × G))
    (hend : edgeChainEnd startChange chain = startChange) :
    rebasedEdgeChainProduct startChange chain =
      startChange⁻¹ * reverseEdgeChainProduct chain * startChange := by
  rw [rebasedEdgeChainProduct_eq_rebaseEdge, hend]
  rfl

/-- 对由 `Fin` 编号的非空边链，若每条边的命名终点 frame 等于下一条边的命名起点
frame，则逐项换连接后的反序边词正是 `rebasedEdgeChainProduct`。-/
private theorem rebasedEdgeChainProduct_ofFn_eq_reverseEdgeChainProduct
    {G : Type*} [Group G] (n : ℕ)
    (startFrame endFrame edge : Fin (n + 1) → G)
    (hadj : ∀ k : Fin n, endFrame k.castSucc = startFrame k.succ) :
    rebasedEdgeChainProduct (startFrame 0)
        (List.ofFn fun k => (endFrame k, edge k)) =
      reverseEdgeChainProduct
        (List.ofFn fun k =>
          (endFrame k, rebaseEdge (startFrame k) (endFrame k) (edge k))) := by
  induction n with
  | zero =>
      simp [rebasedEdgeChainProduct, reverseEdgeChainProduct]
  | succ n ih =>
      conv_lhs =>
        rw [List.ofFn_succ]
      conv_rhs =>
        rw [List.ofFn_succ]
      rw [rebasedEdgeChainProduct, reverseEdgeChainProduct]
      have hfirst : endFrame 0 = startFrame (Fin.succ 0) := hadj 0
      rw [hfirst]
      rw [ih
        (startFrame := fun k => startFrame k.succ)
        (endFrame := fun k => endFrame k.succ)
        (edge := fun k => edge k.succ)
        (hadj := fun k => hadj k.succ)]

/-- `rebasedEdgeChainProduct_ofFn_eq_reverseEdgeChainProduct` 的任意正长度版本；相邻性以两条
`Fin n` 边的共享顶点等式表述，避免调用者先把依赖长度重写成后继数。-/
theorem rebasedEdgeChainProduct_ofFn_eq_reverseEdgeChainProduct_of_pos
    {G : Type*} [Group G] (n : ℕ) (hn : 0 < n)
    (startFrame endFrame edge : Fin n → G)
    (hadj : ∀ (s t : Fin n), s.succ = t.castSucc →
      endFrame s = startFrame t) :
    rebasedEdgeChainProduct (startFrame ⟨0, hn⟩)
        (List.ofFn fun k => (endFrame k, edge k)) =
      reverseEdgeChainProduct
        (List.ofFn fun k =>
          (endFrame k, rebaseEdge (startFrame k) (endFrame k) (edge k))) := by
  cases n with
  | zero => exact (Nat.not_lt_zero 0 hn).elim
  | succ n =>
      exact rebasedEdgeChainProduct_ofFn_eq_reverseEdgeChainProduct n
        startFrame endFrame edge
        (fun k => hadj k.castSucc k.succ (Fin.succ_castSucc k))

/-- `Fin.dfoldl` 每次把新项乘在左侧，因此结果是数组按索引反序后的列表乘积。-/
theorem reverseDfoldl_eq_reverse_ofFn_prod
    {G : Type*} [Group G] : ∀ {n : ℕ} (a : Fin n → G),
    Fin.dfoldl n (fun _ => G) (fun i acc => a i * acc) 1 =
      (List.ofFn a).reverse.prod
  | 0, a => by simp [Fin.dfoldl_zero]
  | n + 1, a => by
      rw [Fin.dfoldl_succ_last]
      rw [List.ofFn_succ']
      change a (Fin.last n) *
          Fin.dfoldl n (fun _ => G) (fun i acc => a i.castSucc * acc) 1 = _
      rw [reverseDfoldl_eq_reverse_ofFn_prod (fun i => a i.castSucc)]
      simp

/-- 同时在单格四个顶点改变 connector 后，反序四边词只是原四边词在左下角处的共轭。-/
private theorem rebaseCellBoundary
    {G : Type*} [Group G]
    (bottomLeft bottomRight topRight topLeft : G)
    (bottom right top left : G) :
    (rebaseEdge bottomLeft topLeft left)⁻¹ *
          (rebaseEdge topLeft topRight top)⁻¹ *
          rebaseEdge bottomRight topRight right *
          rebaseEdge bottomLeft bottomRight bottom =
      bottomLeft⁻¹ * (left⁻¹ * top⁻¹ * right * bottom) * bottomLeft := by
  rw [← rebaseEdge_inv bottomLeft topLeft left,
    ← rebaseEdge_inv topLeft topRight top]
  exact rebaseEdge_cycle_four bottomLeft bottomRight topRight topLeft
    bottom right top⁻¹ left⁻¹

/-- 单格四边关系在任意四个顶点 gauge 下仍为单位元。-/
private theorem rebaseCellBoundary_eq_one
    {G : Type*} [Group G]
    (bottomLeft bottomRight topRight topLeft : G)
    (bottom right top left : G)
    (hcell : left⁻¹ * top⁻¹ * right * bottom = 1) :
    (rebaseEdge bottomLeft topLeft left)⁻¹ *
          (rebaseEdge topLeft topRight top)⁻¹ *
          rebaseEdge bottomRight topRight right *
          rebaseEdge bottomLeft bottomRight bottom = 1 := by
  rw [rebaseCellBoundary, hcell]
  simp

/-- 任一网格单格的 Pushout 四边关系可按四个角的任意 transition 同时换连接。-/
theorem BinaryOpenCoverSquareSubdivision.gridCellPushoutEdgeWord_rebase_eq_one
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j : Fin D.steps)
    (bottomLeft bottomRight topRight topLeft :
      binaryVanKampenPushout U V hxU hxV) :
    (rebaseEdge bottomLeft topLeft
        (Monoid.PushoutI.of (D.label i j)
          (D.gridCellBasedVerticalEdgeInPiece hxU hxV hU hV i j 0)))⁻¹ *
      (rebaseEdge topLeft topRight
        (Monoid.PushoutI.of (D.label i j)
          (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i j 1)))⁻¹ *
      rebaseEdge bottomRight topRight
        (Monoid.PushoutI.of (D.label i j)
          (D.gridCellBasedVerticalEdgeInPiece hxU hxV hU hV i j 1)) *
      rebaseEdge bottomLeft bottomRight
        (Monoid.PushoutI.of (D.label i j)
          (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i j 0)) = 1 := by
  apply rebaseCellBoundary_eq_one
  exact D.gridCellPushoutEdgeWord_eq_one hxU hxV hU hV i j

/-- 连续两次端点 gauge 等于分别乘合起点、终点 transition 后的一次 gauge。-/
private theorem rebaseEdge_rebase
    {G : Type*} [Group G]
    (outerStart outerEnd innerStart innerEnd edge : G) :
    rebaseEdge outerStart outerEnd
        (rebaseEdge innerStart innerEnd edge) =
      rebaseEdge (innerStart * outerStart) (innerEnd * outerEnd) edge := by
  simp [rebaseEdge, mul_assoc]

/-- 一条公共边关系在条带当前 connector frame 下继续成立，并给出下一格左侧顶点的合成 transition。-/
theorem rebaseEdge_relation_in_frame
    {G : Type*} [Group G]
    (outerStart outerEnd innerStart innerEnd leftEdge rightEdge : G)
    (h : leftEdge = rebaseEdge innerStart innerEnd rightEdge) :
    rebaseEdge outerStart outerEnd leftEdge =
      rebaseEdge (innerStart * outerStart) (innerEnd * outerEnd) rightEdge := by
  rw [h, rebaseEdge_rebase]

/-- 水平内部边在任意已有条带 frame 下的传播公式。-/
theorem BinaryOpenCoverSquareSubdivision.horizontalInternalEdge_relation_in_frame
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (bottomFrame topFrame : binaryVanKampenPushout U V hxU hxV) :
    let T := D.horizontalInternalEdgeTransitions hxU hxV hUV hU hV
      i k j hshared
    rebaseEdge bottomFrame topFrame
        (Monoid.PushoutI.of (D.label i j)
          (D.gridCellBasedVerticalEdgeInPiece hxU hxV hU hV i j 1)) =
      rebaseEdge (T.startChange * bottomFrame) (T.endChange * topFrame)
        (Monoid.PushoutI.of (D.label k j)
          (D.gridCellBasedVerticalEdgeInPiece hxU hxV hU hV k j 0)) := by
  dsimp only
  apply rebaseEdge_relation_in_frame
  exact D.horizontalInternalEdge_relation hxU hxV hUV hU hV
    i k j hshared

/-- 竖直内部边在任意已有条带 frame 下的传播公式。-/
theorem BinaryOpenCoverSquareSubdivision.verticalInternalEdge_relation_in_frame
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (leftFrame rightFrame : binaryVanKampenPushout U V hxU hxV) :
    let T := D.verticalInternalEdgeTransitions hxU hxV hUV hU hV
      i j l hshared
    rebaseEdge leftFrame rightFrame
        (Monoid.PushoutI.of (D.label i j)
          (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i j 1)) =
      rebaseEdge (T.startChange * leftFrame) (T.endChange * rightFrame)
        (Monoid.PushoutI.of (D.label i l)
          (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i l 0)) := by
  dsimp only
  apply rebaseEdge_relation_in_frame
  exact D.verticalInternalEdge_relation hxU hxV hUV hU hV
    i j l hshared

end SandronesLibrary.Topology
