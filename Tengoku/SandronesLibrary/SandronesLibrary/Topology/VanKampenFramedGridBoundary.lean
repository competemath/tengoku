/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.VanKampenMixedVertexCoherence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# van Kampen 网格的 framed 行与外边界关系

本文件为小格四个顶点配置群值 frames，以中央 transition coherence 保证相邻格的 frame 相容；随后
先按列粘合单格边界，再按行粘合完整行边界，得到整张有限网格的四侧非交换 perimeter relation。

当前条目：

* `topology.fundamental-group.van-kampen-framed-grid-boundary`。

row-prefix 状态只是在 07a/07b 拆批之间可见的实现接口；08 以后只消费完整行投影。本文件不证明某条
外侧 holonomy 为一，也不证明 kernel、单射或 van Kampen 同构。
-/

open Set
open scoped unitInterval

noncomputable section

namespace SandronesLibrary.Topology

variable {X : Type*} [TopologicalSpace X]

/-- 带有当前 focus 的非交换边界词及其乘积为一的关系。

> **Entry**: topology.fundamental-group.van-kampen-framed-grid-boundary-/
structure FocusedBoundary (G : Type*) [Group G] where
  before : G
  focus : G
  after : G
  relation : before * focus * after = 1

/-- 在聚焦边界右侧再粘一个单格，并把 focus 推进到新单格右边。

新单格边界以旧 focus 的逆元开始。非交换次序给出新的
`before = old.after * old.before * top⁻¹`、`after = bottom`。-/
private def FocusedBoundary.attachRight
    {G : Type*} [Group G] (B : FocusedBoundary G)
    (top right bottom : G)
    (hcell : B.focus⁻¹ * top⁻¹ * right * bottom = 1) :
    FocusedBoundary G where
  before := B.after * B.before * top⁻¹
  focus := right
  after := bottom
  relation := by
    have h := twoCellBoundary_glue B.before B.focus B.after 1
      (top⁻¹ * right * bottom) B.relation (by simpa [mul_assoc] using hcell)
    simpa [mul_assoc] using h

@[simp] private theorem FocusedBoundary.attachRight_before
    {G : Type*} [Group G] (B : FocusedBoundary G)
    (top right bottom : G)
    (hcell : B.focus⁻¹ * top⁻¹ * right * bottom = 1) :
    (B.attachRight top right bottom hcell).before =
      B.after * B.before * top⁻¹ := rfl

@[simp] private theorem FocusedBoundary.attachRight_focus
    {G : Type*} [Group G] (B : FocusedBoundary G)
    (top right bottom : G)
    (hcell : B.focus⁻¹ * top⁻¹ * right * bottom = 1) :
    (B.attachRight top right bottom hcell).focus = right := rfl

@[simp] private theorem FocusedBoundary.attachRight_after
    {G : Type*} [Group G] (B : FocusedBoundary G)
    (top right bottom : G)
    (hcell : B.focus⁻¹ * top⁻¹ * right * bottom = 1) :
    (B.attachRight top right bottom hcell).after = bottom := rfl

/-- 任意单格在四顶点 frame 下给出以其右边为 focus 的初始条带状态。-/
private noncomputable def BinaryOpenCoverSquareSubdivision.gridCellFocusedBoundary
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j : Fin D.steps)
    (bottomLeft bottomRight topRight topLeft :
      binaryVanKampenPushout U V hxU hxV) :
    FocusedBoundary (binaryVanKampenPushout U V hxU hxV) where
  before :=
    (rebaseEdge bottomLeft topLeft
      (Monoid.PushoutI.of (D.label i j)
        (D.gridCellBasedVerticalEdgeInPiece hxU hxV hU hV i j 0)))⁻¹ *
    (rebaseEdge topLeft topRight
      (Monoid.PushoutI.of (D.label i j)
        (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i j 1)))⁻¹
  focus := rebaseEdge bottomRight topRight
    (Monoid.PushoutI.of (D.label i j)
      (D.gridCellBasedVerticalEdgeInPiece hxU hxV hU hV i j 1))
  after := rebaseEdge bottomLeft bottomRight
    (Monoid.PushoutI.of (D.label i j)
      (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i j 0))
  relation := by
    simpa [mul_assoc] using
      D.gridCellPushoutEdgeWord_rebase_eq_one hxU hxV hU hV i j
        bottomLeft bottomRight topRight topLeft

/-- 当前聚焦条带沿真实水平内部边向右附加下一格。-/
private noncomputable def BinaryOpenCoverSquareSubdivision.attachHorizontalGridCell
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (B : FocusedBoundary (binaryVanKampenPushout U V hxU hxV))
    (bottomFrame topFrame rightBottomFrame rightTopFrame :
      binaryVanKampenPushout U V hxU hxV)
    (hfocus : B.focus = rebaseEdge bottomFrame topFrame
      (Monoid.PushoutI.of (D.label i j)
        (D.gridCellBasedVerticalEdgeInPiece hxU hxV hU hV i j 1))) :
    FocusedBoundary (binaryVanKampenPushout U V hxU hxV) := by
  let T := D.horizontalInternalEdgeTransitions hxU hxV hUV hU hV
    i k j hshared
  let newBottomLeft := T.startChange * bottomFrame
  let newTopLeft := T.endChange * topFrame
  let top := rebaseEdge newTopLeft rightTopFrame
    (Monoid.PushoutI.of (D.label k j)
      (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV k j 1))
  let right := rebaseEdge rightBottomFrame rightTopFrame
    (Monoid.PushoutI.of (D.label k j)
      (D.gridCellBasedVerticalEdgeInPiece hxU hxV hU hV k j 1))
  let bottom := rebaseEdge newBottomLeft rightBottomFrame
    (Monoid.PushoutI.of (D.label k j)
      (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV k j 0))
  apply B.attachRight top right bottom
  rw [hfocus]
  rw [D.horizontalInternalEdge_relation_in_frame hxU hxV hUV hU hV
    i k j hshared bottomFrame topFrame]
  exact D.gridCellPushoutEdgeWord_rebase_eq_one hxU hxV hU hV k j
    newBottomLeft rightBottomFrame rightTopFrame newTopLeft

@[simp] private theorem BinaryOpenCoverSquareSubdivision.gridCellFocusedBoundary_focus
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j : Fin D.steps)
    (bottomLeft bottomRight topRight topLeft :
      binaryVanKampenPushout U V hxU hxV) :
    (D.gridCellFocusedBoundary hxU hxV hU hV i j
      bottomLeft bottomRight topRight topLeft).focus =
      rebaseEdge bottomRight topRight
        (Monoid.PushoutI.of (D.label i j)
          (D.gridCellBasedVerticalEdgeInPiece hxU hxV hU hV i j 1)) := rfl

@[simp] private theorem BinaryOpenCoverSquareSubdivision.attachHorizontalGridCell_focus
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (B : FocusedBoundary (binaryVanKampenPushout U V hxU hxV))
    (bottomFrame topFrame rightBottomFrame rightTopFrame :
      binaryVanKampenPushout U V hxU hxV)
    (hfocus : B.focus = rebaseEdge bottomFrame topFrame
      (Monoid.PushoutI.of (D.label i j)
        (D.gridCellBasedVerticalEdgeInPiece hxU hxV hU hV i j 1))) :
    (D.attachHorizontalGridCell hxU hxV hUV hU hV i k j hshared B
      bottomFrame topFrame rightBottomFrame rightTopFrame hfocus).focus =
      rebaseEdge rightBottomFrame rightTopFrame
        (Monoid.PushoutI.of (D.label k j)
          (D.gridCellBasedVerticalEdgeInPiece hxU hxV hU hV k j 1)) := by
  rfl
private theorem mul_eq_one_rotate
    {G : Type*} [Group G] (a b : G) (h : a * b = 1) : b * a = 1 := by
  have hc := congrArg (fun x => a⁻¹ * x * a) h
  simpa [mul_assoc] using hc
/-- 中央 transition 方块作用于任意既有 cell-side frame 后仍保持传播兼容。-/
private theorem edgeTransitions_gridVertex_square_apply_frame
    {G : Type*} [Group G]
    (horizontalBottom verticalRight verticalLeft horizontalTop : EdgeTransitions G)
    (hSquare : verticalRight.startChange * horizontalBottom.endChange =
      horizontalTop.startChange * verticalLeft.endChange)
    (frame : G) :
    verticalRight.startChange * (horizontalBottom.endChange * frame) =
      horizontalTop.startChange * (verticalLeft.endChange * frame) := by
  rw [← mul_assoc, hSquare, mul_assoc]

/-- 一个单格用于规范化四条边的四角 frames。-/
structure CellVertexFrames (G : Type*) where
  bottomLeft : G
  bottomRight : G
  topRight : G
  topLeft : G

/-- 两个水平相邻单格的 frames 与公共边 transition 相容。-/
structure HorizontalCellFramesCompatible
    {G : Type*} [Group G] (T : EdgeTransitions G)
    (left right : CellVertexFrames G) : Prop where
  bottom : right.bottomLeft = T.startChange * left.bottomRight
  top : right.topLeft = T.endChange * left.topRight

/-- 沿一列的竖直内部边 transition，把下格上侧 frames 提升为上格下侧 frames；
上格顶部两端暂由下一层水平递归指定。-/
def CellVertexFrames.liftAcrossVertical
    {G : Type*} [Group G] (lower : CellVertexFrames G)
    (vertical : EdgeTransitions G) (upperTopRight upperTopLeft : G) :
    CellVertexFrames G where
  bottomLeft := vertical.startChange * lower.topLeft
  bottomRight := vertical.endChange * lower.topRight
  topRight := upperTopRight
  topLeft := upperTopLeft

/-- 下行 frames 水平相容、中央 transition 方块相容且上行顶部 frames 相容时，
逐列竖直提升得到的上行四角 frames 也水平相容。
@isnad1 id=horizont.3h11v.s7.caf0a08fb1c3 from=translated src=- shape=ca3d3e71 vocab=e6576cea
-/
theorem horizontalCellFramesCompatible_liftAcrossVertical
    {G : Type*} [Group G]
    (horizontalBottom horizontalTop verticalLeft verticalRight : EdgeTransitions G)
    (leftLower rightLower : CellVertexFrames G)
    (leftUpperTopRight leftUpperTopLeft rightUpperTopRight rightUpperTopLeft : G)
    (hLower : HorizontalCellFramesCompatible horizontalBottom leftLower rightLower)
    (hSquare : verticalRight.startChange * horizontalBottom.endChange =
      horizontalTop.startChange * verticalLeft.endChange)
    (hUpperTop : rightUpperTopLeft =
      horizontalTop.endChange * leftUpperTopRight) :
    HorizontalCellFramesCompatible horizontalTop
      (leftLower.liftAcrossVertical verticalLeft leftUpperTopRight leftUpperTopLeft)
      (rightLower.liftAcrossVertical verticalRight rightUpperTopRight rightUpperTopLeft) := by
  constructor
  · change verticalRight.startChange * rightLower.topLeft =
      horizontalTop.startChange * (verticalLeft.endChange * leftLower.topRight)
    rw [hLower.top]
    exact edgeTransitions_gridVertex_square_apply_frame
      horizontalBottom verticalRight verticalLeft horizontalTop hSquare leftLower.topRight
  · exact hUpperTop

/-- 给定一列四角 frames 的单行前缀状态；`focus` 始终是当前最右格按其右侧 frames
规范化后的真实右边。-/
structure BinaryOpenCoverSquareSubdivision.FramedHorizontalRowPrefixState
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (j rightIndex : Fin D.steps)
    (frames : Fin D.steps → CellVertexFrames
      (binaryVanKampenPushout U V hxU hxV)) where
  boundary : FocusedBoundary (binaryVanKampenPushout U V hxU hxV)
  focus_eq : boundary.focus =
    rebaseEdge (frames rightIndex).bottomRight (frames rightIndex).topRight
      (Monoid.PushoutI.of (φ := binaryOpenCoverIntersectionMaps U V hxU hxV)
        (D.label rightIndex j)
        (D.gridCellBasedVerticalEdgeInPiece hxU hxV hU hV rightIndex j 1) :
        binaryVanKampenPushout U V hxU hxV)
  after_eq : boundary.after =
    rebaseEdge (frames rightIndex).bottomLeft (frames rightIndex).bottomRight
      (Monoid.PushoutI.of (φ := binaryOpenCoverIntersectionMaps U V hxU hxV)
        (D.label rightIndex j)
        (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV rightIndex j 0) :
        binaryVanKampenPushout U V hxU hxV)
  leftEdge : binaryVanKampenPushout U V hxU hxV
  topWord : binaryVanKampenPushout U V hxU hxV
  bottomPrefix : binaryVanKampenPushout U V hxU hxV
  before_eq : boundary.before = bottomPrefix * leftEdge⁻¹ * topWord⁻¹

/-- 任意水平相容的四角 frames 上，从第 `0` 格递归粘合到编号 `p` 的单行前缀。-/
noncomputable def BinaryOpenCoverSquareSubdivision.framedHorizontalRowPrefixState
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
        (frames i) (frames k)) :
    (p : ℕ) → (hp : p < D.steps) →
      D.FramedHorizontalRowPrefixState hxU hxV hU hV j ⟨p, hp⟩ frames
  | 0, hp => by
      let i : Fin D.steps := ⟨0, hp⟩
      let F := frames i
      let B := D.gridCellFocusedBoundary hxU hxV hU hV i j
        F.bottomLeft F.bottomRight F.topRight F.topLeft
      exact {
        boundary := B
        focus_eq := by rfl
        after_eq := by rfl
        leftEdge := rebaseEdge F.bottomLeft F.topLeft
          (Monoid.PushoutI.of (D.label i j)
            (D.gridCellBasedVerticalEdgeInPiece hxU hxV hU hV i j 0))
        topWord := rebaseEdge F.topLeft F.topRight
          (Monoid.PushoutI.of (D.label i j)
            (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i j 1))
        bottomPrefix := 1
        before_eq := by
          simp [B, F, BinaryOpenCoverSquareSubdivision.gridCellFocusedBoundary] }
  | p + 1, hp => by
      have hp' : p < D.steps := Nat.lt_trans (Nat.lt_succ_self p) hp
      let i : Fin D.steps := ⟨p, hp'⟩
      let k : Fin D.steps := ⟨p + 1, hp⟩
      have hshared : i.succ = k.castSucc := by apply Fin.ext; rfl
      let previous := D.framedHorizontalRowPrefixState hxU hxV hUV hU hV
        j frames hcompat p hp'
      let Fi := frames i
      let Fk := frames k
      have hfocus : previous.boundary.focus = rebaseEdge Fi.bottomRight Fi.topRight
          (Monoid.PushoutI.of
            (φ := binaryOpenCoverIntersectionMaps U V hxU hxV) (D.label i j)
            (D.gridCellBasedVerticalEdgeInPiece hxU hxV hU hV i j 1)) := by
        simpa [i, Fi, previous] using previous.focus_eq
      let next := D.attachHorizontalGridCell hxU hxV hUV hU hV
        i k j hshared previous.boundary
        Fi.bottomRight Fi.topRight Fk.bottomRight Fk.topRight hfocus
      let T := D.horizontalInternalEdgeTransitions hxU hxV hUV hU hV
        i k j hshared
      have hframes := hcompat i k hshared
      let top := rebaseEdge Fk.topLeft Fk.topRight
        (Monoid.PushoutI.of (D.label k j)
          (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV k j 1))
      exact {
        boundary := next
        focus_eq := by rfl
        after_eq := by
          change rebaseEdge (T.startChange * Fi.bottomRight) Fk.bottomRight
              (Monoid.PushoutI.of
                (φ := binaryOpenCoverIntersectionMaps U V hxU hxV) (D.label k j)
                (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV k j 0)) = _
          rw [← hframes.bottom]
        leftEdge := previous.leftEdge
        topWord := top * previous.topWord
        bottomPrefix := previous.boundary.after * previous.bottomPrefix
        before_eq := by
          rw [show next.before = previous.boundary.after * previous.boundary.before *
              (rebaseEdge (T.endChange * Fi.topRight) Fk.topRight
                (Monoid.PushoutI.of
                  (φ := binaryOpenCoverIntersectionMaps U V hxU hxV) (D.label k j)
                  (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV k j 1)))⁻¹ by rfl]
          rw [← hframes.top]
          rw [previous.before_eq]
          simp [top, Fk, mul_assoc] }

/-- 水平相容 frames 上的完整单行状态。-/
noncomputable def BinaryOpenCoverSquareSubdivision.framedHorizontalFullRowState
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
        (frames i) (frames k)) :
    D.FramedHorizontalRowPrefixState hxU hxV hU hV j
      ⟨D.steps - 1, Nat.sub_lt D.steps_pos Nat.zero_lt_one⟩ frames :=
  D.framedHorizontalRowPrefixState hxU hxV hUV hU hV j frames hcompat
    (D.steps - 1) (Nat.sub_lt D.steps_pos Nat.zero_lt_one)

/-- The left edge of a framed horizontal prefix is always the framed left edge
of its first cell; extending the prefix only changes the right focus.-/
private theorem BinaryOpenCoverSquareSubdivision.framedHorizontalRowPrefixState_leftEdge
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
        (frames i) (frames k)) :
    ∀ (p : ℕ) (hp : p < D.steps),
      (D.framedHorizontalRowPrefixState hxU hxV hUV hU hV
        j frames hcompat p hp).leftEdge =
      rebaseEdge (frames ⟨0, D.steps_pos⟩).bottomLeft
        (frames ⟨0, D.steps_pos⟩).topLeft
        (Monoid.PushoutI.of (D.label ⟨0, D.steps_pos⟩ j)
          (D.gridCellBasedVerticalEdgeInPiece
            hxU hxV hU hV ⟨0, D.steps_pos⟩ j 0))
  | 0, _ => rfl
  | p + 1, hp => by
      have hp' : p < D.steps := Nat.lt_trans (Nat.lt_succ_self p) hp
      change
        (D.framedHorizontalRowPrefixState hxU hxV hUV hU hV
          j frames hcompat p hp').leftEdge = _
      exact D.framedHorizontalRowPrefixState_leftEdge
        hxU hxV hUV hU hV j frames hcompat p hp'

/-- The left edge of a completed framed row is the framed left edge of its
first cell.  This is the public projection; the prefix recursion remains an
implementation detail of the completed-row constructor.
@isnad1 id=eq.6h8v.s11.db0503dc1e03 from=translated src=- shape=31bb98a9 vocab=7407308f
-/
theorem BinaryOpenCoverSquareSubdivision.framedHorizontalFullRowState_leftEdge
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
        (frames i) (frames k)) :
    (D.framedHorizontalFullRowState hxU hxV hUV hU hV
      j frames hcompat).leftEdge =
      rebaseEdge (frames ⟨0, D.steps_pos⟩).bottomLeft
        (frames ⟨0, D.steps_pos⟩).topLeft
        (Monoid.PushoutI.of (D.label ⟨0, D.steps_pos⟩ j)
          (D.gridCellBasedVerticalEdgeInPiece
            hxU hxV hU hV ⟨0, D.steps_pos⟩ j 0)) := by
  exact D.framedHorizontalRowPrefixState_leftEdge
    hxU hxV hUV hU hV j frames hcompat
    (D.steps - 1) (Nat.sub_lt D.steps_pos Nat.zero_lt_one)

/-- 任意水平相容 frames 上，完整单行仍满足标准矩形外边界关系。
@isnad1 id=other.6h8v.s11.0d74bde99e96 from=translated src=- shape=2d5d15d5 vocab=8c353537
-/
theorem BinaryOpenCoverSquareSubdivision.framedHorizontalFullRowState_standard_relation
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
        (frames i) (frames k)) :
    let S := D.framedHorizontalFullRowState hxU hxV hUV hU hV j frames hcompat
    S.leftEdge⁻¹ * S.topWord⁻¹ * S.boundary.focus *
        (S.boundary.after * S.bottomPrefix) = 1 := by
  let S := D.framedHorizontalFullRowState hxU hxV hUV hU hV j frames hcompat
  have h := S.boundary.relation
  rw [S.before_eq] at h
  have hblocks : S.bottomPrefix *
      (S.leftEdge⁻¹ * S.topWord⁻¹ * S.boundary.focus * S.boundary.after) = 1 := by
    simpa [mul_assoc] using h
  have hrot := mul_eq_one_rotate S.bottomPrefix
    (S.leftEdge⁻¹ * S.topWord⁻¹ * S.boundary.focus * S.boundary.after) hblocks
  simpa [mul_assoc] using hrot

/-- 单行规范 frame family 在自然编号 `p` 处的四角值：每格右侧取单位元，
非首格左侧取前一条水平 internal transition。-/
private noncomputable def BinaryOpenCoverSquareSubdivision.canonicalHorizontalCellFramesAt
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (j : Fin D.steps) :
    (p : ℕ) → (hp : p < D.steps) →
      CellVertexFrames (binaryVanKampenPushout U V hxU hxV)
  | 0, _ => { bottomLeft := 1, bottomRight := 1, topRight := 1, topLeft := 1 }
  | p + 1, hp =>
      let hp' : p < D.steps := Nat.lt_trans (Nat.lt_succ_self p) hp
      let i : Fin D.steps := ⟨p, hp'⟩
      let k : Fin D.steps := ⟨p + 1, hp⟩
      let hshared : i.succ = k.castSucc := by apply Fin.ext; rfl
      let T := D.horizontalInternalEdgeTransitions hxU hxV hUV hU hV
        i k j hshared
      { bottomLeft := T.startChange
        bottomRight := 1
        topRight := 1
        topLeft := T.endChange }

/-- 上述自然编号定义组成完整的单行 frame family。-/
private noncomputable def BinaryOpenCoverSquareSubdivision.canonicalHorizontalCellFrames
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (j : Fin D.steps) :
    Fin D.steps → CellVertexFrames (binaryVanKampenPushout U V hxU hxV) :=
  fun i => D.canonicalHorizontalCellFramesAt hxU hxV hUV hU hV j i.val i.isLt

@[simp] private theorem BinaryOpenCoverSquareSubdivision.canonicalHorizontalCellFrames_bottomRight
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (j i : Fin D.steps) :
    (D.canonicalHorizontalCellFrames hxU hxV hUV hU hV j i).bottomRight = 1 := by
  rcases i with ⟨_ | p, hp⟩
  · rfl
  · rfl

@[simp] private theorem BinaryOpenCoverSquareSubdivision.canonicalHorizontalCellFrames_topRight
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (j i : Fin D.steps) :
    (D.canonicalHorizontalCellFrames hxU hxV hUV hU hV j i).topRight = 1 := by
  rcases i with ⟨_ | p, hp⟩
  · rfl
  · rfl

/-- 规范单行 frames 与每条真实水平 internal transition 相容。-/
private theorem BinaryOpenCoverSquareSubdivision.canonicalHorizontalCellFrames_compatible
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (j : Fin D.steps) (i k : Fin D.steps) (hshared : i.succ = k.castSucc) :
    HorizontalCellFramesCompatible
      (D.horizontalInternalEdgeTransitions hxU hxV hUV hU hV i k j hshared)
      (D.canonicalHorizontalCellFrames hxU hxV hUV hU hV j i)
      (D.canonicalHorizontalCellFrames hxU hxV hUV hU hV j k) := by
  rcases i with ⟨iv, hiv⟩
  rcases k with ⟨kv, hkv⟩
  have hval : iv + 1 = kv := congrArg Fin.val hshared
  change iv + 1 = kv at hval
  subst kv
  constructor
  · rw [D.canonicalHorizontalCellFrames_bottomRight]
    simp only [mul_one]
    rfl
  · rw [D.canonicalHorizontalCellFrames_topRight]
    simp only [mul_one]
    rfl

/-- 沿相邻两行之间的逐列竖直 transitions 提升整行 frames；新行顶部采用其规范水平
frame family 的顶部两端。-/
private noncomputable def BinaryOpenCoverSquareSubdivision.liftHorizontalRowFrames
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (j l : Fin D.steps) (hVertical : j.succ = l.castSucc)
    (lowerFrames : Fin D.steps → CellVertexFrames
      (binaryVanKampenPushout U V hxU hxV)) :
    Fin D.steps → CellVertexFrames (binaryVanKampenPushout U V hxU hxV) :=
  fun i =>
    let Vt := D.verticalInternalEdgeTransitions hxU hxV hUV hU hV
      i j l hVertical
    let canonicalTop := D.canonicalHorizontalCellFrames hxU hxV hUV hU hV l i
    (lowerFrames i).liftAcrossVertical Vt canonicalTop.topRight canonicalTop.topLeft

/-- 水平相容的一行经逐列竖直提升后仍为水平相容的一行。-/
private theorem BinaryOpenCoverSquareSubdivision.liftHorizontalRowFrames_compatible
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (j l : Fin D.steps) (hVertical : j.succ = l.castSucc)
    (lowerFrames : Fin D.steps → CellVertexFrames
      (binaryVanKampenPushout U V hxU hxV))
    (hLower : ∀ (i k : Fin D.steps) (hHorizontal : i.succ = k.castSucc),
      HorizontalCellFramesCompatible
        (D.horizontalInternalEdgeTransitions hxU hxV hUV hU hV i k j hHorizontal)
        (lowerFrames i) (lowerFrames k))
    (i k : Fin D.steps) (hHorizontal : i.succ = k.castSucc) :
    HorizontalCellFramesCompatible
      (D.horizontalInternalEdgeTransitions hxU hxV hUV hU hV i k l hHorizontal)
      (D.liftHorizontalRowFrames hxU hxV hUV hU hV
        j l hVertical lowerFrames i)
      (D.liftHorizontalRowFrames hxU hxV hUV hU hV
        j l hVertical lowerFrames k) := by
  apply horizontalCellFramesCompatible_liftAcrossVertical
    (D.horizontalInternalEdgeTransitions hxU hxV hUV hU hV i k j hHorizontal)
    (D.horizontalInternalEdgeTransitions hxU hxV hUV hU hV i k l hHorizontal)
    (D.verticalInternalEdgeTransitions hxU hxV hUV hU hV i j l hVertical)
    (D.verticalInternalEdgeTransitions hxU hxV hUV hU hV k j l hVertical)
    (lowerFrames i) (lowerFrames k)
    ((D.canonicalHorizontalCellFrames hxU hxV hUV hU hV l i).topRight)
    ((D.canonicalHorizontalCellFrames hxU hxV hUV hU hV l i).topLeft)
    ((D.canonicalHorizontalCellFrames hxU hxV hUV hU hV l k).topRight)
    ((D.canonicalHorizontalCellFrames hxU hxV hUV hU hV l k).topLeft)
  · exact hLower i k hHorizontal
  · exact D.centralInternalTransitions_square hxU hxV hUV hU hV
      i k j l hHorizontal hVertical
  · exact (D.canonicalHorizontalCellFrames_compatible hxU hxV hUV hU hV
      l i k hHorizontal).top

/-- 从底行开始逐行竖直提升得到第 `p` 行的规范二维 frames。-/
private noncomputable def BinaryOpenCoverSquareSubdivision.gridRowFramesAt
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V) :
    (p : ℕ) → (hp : p < D.steps) →
      Fin D.steps → CellVertexFrames (binaryVanKampenPushout U V hxU hxV)
  | 0, hp =>
      D.canonicalHorizontalCellFrames hxU hxV hUV hU hV ⟨0, hp⟩
  | p + 1, hp =>
      let hp' : p < D.steps := Nat.lt_trans (Nat.lt_succ_self p) hp
      let j : Fin D.steps := ⟨p, hp'⟩
      let l : Fin D.steps := ⟨p + 1, hp⟩
      let hVertical : j.succ = l.castSucc := by apply Fin.ext; rfl
      D.liftHorizontalRowFrames hxU hxV hUV hU hV j l hVertical
        (D.gridRowFramesAt hxU hxV hUV hU hV p hp')

/-- 每一递归生成的二维行 frame family 都与该行全部水平 internal transitions 相容。-/
private theorem BinaryOpenCoverSquareSubdivision.gridRowFramesAt_compatible
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V) :
    ∀ (p : ℕ) (hp : p < D.steps)
      (i k : Fin D.steps) (hHorizontal : i.succ = k.castSucc),
      HorizontalCellFramesCompatible
        (D.horizontalInternalEdgeTransitions hxU hxV hUV hU hV
          i k ⟨p, hp⟩ hHorizontal)
        (D.gridRowFramesAt hxU hxV hUV hU hV p hp i)
        (D.gridRowFramesAt hxU hxV hUV hU hV p hp k)
  | 0, hp, i, k, hHorizontal =>
      D.canonicalHorizontalCellFrames_compatible hxU hxV hUV hU hV
        ⟨0, hp⟩ i k hHorizontal
  | p + 1, hp, i, k, hHorizontal => by
      have hp' : p < D.steps := Nat.lt_trans (Nat.lt_succ_self p) hp
      let j : Fin D.steps := ⟨p, hp'⟩
      let l : Fin D.steps := ⟨p + 1, hp⟩
      have hVertical : j.succ = l.castSucc := by apply Fin.ext; rfl
      apply D.liftHorizontalRowFrames_compatible hxU hxV hUV hU hV
        j l hVertical (D.gridRowFramesAt hxU hxV hUV hU hV p hp')
      · intro i' k' hHorizontal'
        exact D.gridRowFramesAt_compatible hxU hxV hUV hU hV
          p hp' i' k' hHorizontal'

/-- 第 `p` 行在递归二维 frames 上的完整 framed-row 状态。-/
private noncomputable def BinaryOpenCoverSquareSubdivision.gridFramedFullRowStateAt
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (p : ℕ) (hp : p < D.steps) :
    D.FramedHorizontalRowPrefixState hxU hxV hU hV ⟨p, hp⟩
      ⟨D.steps - 1, Nat.sub_lt D.steps_pos Nat.zero_lt_one⟩
      (D.gridRowFramesAt hxU hxV hUV hU hV p hp) :=
  D.framedHorizontalFullRowState hxU hxV hUV hU hV ⟨p, hp⟩
    (D.gridRowFramesAt hxU hxV hUV hU hV p hp)
    (D.gridRowFramesAt_compatible hxU hxV hUV hU hV p hp)

/-- 每一行在递归二维 frames 上都满足标准矩形外边界关系。-/
private theorem BinaryOpenCoverSquareSubdivision.gridFramedFullRowStateAt_standard_relation
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (p : ℕ) (hp : p < D.steps) :
    let S := D.gridFramedFullRowStateAt hxU hxV hUV hU hV p hp
    S.leftEdge⁻¹ * S.topWord⁻¹ * S.boundary.focus *
        (S.boundary.after * S.bottomPrefix) = 1 := by
  exact D.framedHorizontalFullRowState_standard_relation hxU hxV hUV hU hV
    ⟨p, hp⟩ (D.gridRowFramesAt hxU hxV hUV hU hV p hp)
    (D.gridRowFramesAt_compatible hxU hxV hUV hU hV p hp)

/-- 相邻两行中，同一列下格的规范化上边严格等于上格的规范化下边。-/
private theorem BinaryOpenCoverSquareSubdivision.gridRowFramesAt_vertical_edge
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (p : ℕ) (hp : p + 1 < D.steps) (i : Fin D.steps) :
    let hp' : p < D.steps := Nat.lt_trans (Nat.lt_succ_self p) hp
    let j : Fin D.steps := ⟨p, hp'⟩
    let l : Fin D.steps := ⟨p + 1, hp⟩
    let lower := D.gridRowFramesAt hxU hxV hUV hU hV p hp' i
    let upper := D.gridRowFramesAt hxU hxV hUV hU hV (p + 1) hp i
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
  let lowerFrames := D.gridRowFramesAt hxU hxV hUV hU hV p hp'
  have h := D.verticalInternalEdge_relation_in_frame hxU hxV hUV hU hV
    i j l hVertical (lowerFrames i).topLeft (lowerFrames i).topRight
  simpa [BinaryOpenCoverSquareSubdivision.gridRowFramesAt,
    BinaryOpenCoverSquareSubdivision.liftHorizontalRowFrames,
    CellVertexFrames.liftAcrossVertical, lowerFrames, j, l, hp'] using h

/-- 相邻两行任意列前缀中，下行上边反序词等于上行下边反序词。-/
private theorem BinaryOpenCoverSquareSubdivision.gridFramedRowPrefix_topWord_eq_next_bottomWord
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (p : ℕ) (hp : p + 1 < D.steps) :
    ∀ (q : ℕ) (hq : q < D.steps),
    let hp' : p < D.steps := Nat.lt_trans (Nat.lt_succ_self p) hp
    let lowerFrames := D.gridRowFramesAt hxU hxV hUV hU hV p hp'
    let upperFrames := D.gridRowFramesAt hxU hxV hUV hU hV (p + 1) hp
    let lower := D.framedHorizontalRowPrefixState hxU hxV hUV hU hV
      ⟨p, hp'⟩ lowerFrames
      (D.gridRowFramesAt_compatible hxU hxV hUV hU hV p hp') q hq
    let upper := D.framedHorizontalRowPrefixState hxU hxV hUV hU hV
      ⟨p + 1, hp⟩ upperFrames
      (D.gridRowFramesAt_compatible hxU hxV hUV hU hV (p + 1) hp) q hq
    lower.topWord = upper.boundary.after * upper.bottomPrefix
  | 0, hq => by
      let hp' : p < D.steps := Nat.lt_trans (Nat.lt_succ_self p) hp
      let i : Fin D.steps := ⟨0, hq⟩
      let lowerFrames := D.gridRowFramesAt hxU hxV hUV hU hV p hp'
      let upperFrames := D.gridRowFramesAt hxU hxV hUV hU hV (p + 1) hp
      let lower := D.framedHorizontalRowPrefixState hxU hxV hUV hU hV
        ⟨p, hp'⟩ lowerFrames
        (D.gridRowFramesAt_compatible hxU hxV hUV hU hV p hp') 0 hq
      let upper := D.framedHorizontalRowPrefixState hxU hxV hUV hU hV
        ⟨p + 1, hp⟩ upperFrames
        (D.gridRowFramesAt_compatible hxU hxV hUV hU hV (p + 1) hp) 0 hq
      change lower.topWord = upper.boundary.after * upper.bottomPrefix
      rw [upper.after_eq]
      change rebaseEdge (lowerFrames i).topLeft (lowerFrames i).topRight
          (Monoid.PushoutI.of (D.label i ⟨p, hp'⟩)
            (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i ⟨p, hp'⟩ 1)) =
        rebaseEdge (upperFrames i).bottomLeft (upperFrames i).bottomRight
          (Monoid.PushoutI.of (D.label i ⟨p + 1, hp⟩)
            (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i ⟨p + 1, hp⟩ 0)) * 1
      simpa using D.gridRowFramesAt_vertical_edge hxU hxV hUV hU hV p hp i
  | q + 1, hq => by
      have hq' : q < D.steps := Nat.lt_trans (Nat.lt_succ_self q) hq
      let hp' : p < D.steps := Nat.lt_trans (Nat.lt_succ_self p) hp
      let lowerFrames := D.gridRowFramesAt hxU hxV hUV hU hV p hp'
      let upperFrames := D.gridRowFramesAt hxU hxV hUV hU hV (p + 1) hp
      let lowerCompat := D.gridRowFramesAt_compatible hxU hxV hUV hU hV p hp'
      let upperCompat := D.gridRowFramesAt_compatible hxU hxV hUV hU hV (p + 1) hp
      let lowerPrev := D.framedHorizontalRowPrefixState hxU hxV hUV hU hV
        ⟨p, hp'⟩ lowerFrames lowerCompat q hq'
      let upperPrev := D.framedHorizontalRowPrefixState hxU hxV hUV hU hV
        ⟨p + 1, hp⟩ upperFrames upperCompat q hq'
      let lowerNext := D.framedHorizontalRowPrefixState hxU hxV hUV hU hV
        ⟨p, hp'⟩ lowerFrames lowerCompat (q + 1) hq
      let upperNext := D.framedHorizontalRowPrefixState hxU hxV hUV hU hV
        ⟨p + 1, hp⟩ upperFrames upperCompat (q + 1) hq
      let k : Fin D.steps := ⟨q + 1, hq⟩
      have ih := D.gridFramedRowPrefix_topWord_eq_next_bottomWord
        hxU hxV hUV hU hV p hp q hq'
      have hedge := D.gridRowFramesAt_vertical_edge hxU hxV hUV hU hV p hp k
      have hLowerTop : lowerNext.topWord =
          rebaseEdge (lowerFrames k).topLeft (lowerFrames k).topRight
            (Monoid.PushoutI.of
              (D.label k ⟨p, hp'⟩)
              (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV
                k ⟨p, hp'⟩ 1)) * lowerPrev.topWord := by
        rfl
      have hUpperPrefix : upperNext.bottomPrefix =
          upperPrev.boundary.after * upperPrev.bottomPrefix := by
        rfl
      change lowerNext.topWord = upperNext.boundary.after * upperNext.bottomPrefix
      change lowerPrev.topWord =
        upperPrev.boundary.after * upperPrev.bottomPrefix at ih
      rw [hLowerTop, upperNext.after_eq, hUpperPrefix]
      rw [hedge, ih]

/-- 相邻两条完整行中，下行完整上边词严格等于上行完整下边词。-/
private theorem BinaryOpenCoverSquareSubdivision.gridFramedFullRow_topWord_eq_next_bottomWord
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (p : ℕ) (hp : p + 1 < D.steps) :
    let hp' : p < D.steps := Nat.lt_trans (Nat.lt_succ_self p) hp
    let lower := D.gridFramedFullRowStateAt hxU hxV hUV hU hV p hp'
    let upper := D.gridFramedFullRowStateAt hxU hxV hUV hU hV (p + 1) hp
    lower.topWord = upper.boundary.after * upper.bottomPrefix := by
  exact D.gridFramedRowPrefix_topWord_eq_next_bottomWord hxU hxV hUV hU hV
    p hp (D.steps - 1) (Nat.sub_lt D.steps_pos Nat.zero_lt_one)

/-- 两条标准矩形行边界沿相反定向的共同横边粘合，得到合并矩形的标准外边界次序。-/
private theorem twoRowBoundaries_glue
    {G : Type*} [Group G]
    (lowerLeft lowerTop lowerRight lowerBottom : G)
    (upperLeft upperTop upperRight upperBottom : G)
    (hLower : lowerLeft⁻¹ * lowerTop⁻¹ * lowerRight * lowerBottom = 1)
    (hUpper : upperLeft⁻¹ * upperTop⁻¹ * upperRight * upperBottom = 1)
    (hshared : upperBottom = lowerTop) :
    lowerLeft⁻¹ * upperLeft⁻¹ * upperTop⁻¹ * upperRight *
        lowerRight * lowerBottom = 1 := by
  have hglue := twoCellBoundary_glue
    lowerLeft⁻¹ lowerTop⁻¹ (lowerRight * lowerBottom)
    (upperLeft⁻¹ * upperTop⁻¹ * upperRight) 1
    (by simpa [mul_assoc] using hLower)
    (by rw [inv_inv, ← hshared]; simpa [mul_assoc] using hUpper)
  have hrotate := mul_eq_one_rotate
    ((upperLeft⁻¹ * upperTop⁻¹ * upperRight) * (lowerRight * lowerBottom))
    lowerLeft⁻¹ (by simpa [mul_assoc] using hglue)
  simpa [mul_assoc] using hrotate

/-- 从底行到当前行的矩形边界状态。顶边词作为类型参数，因而状态在
类型上就记录它的最高行；其余三个词沿左、右、下外边界排列。-/
private structure GridRowPrefixState (G : Type*) [Group G] (topWord : G) where
  leftWord : G
  rightWord : G
  bottomWord : G
  relation : leftWord⁻¹ * topWord⁻¹ * rightWord * bottomWord = 1

/-- 从第零行开始逐行粘合，得到截至第 `p` 行的整个矩形边界状态。-/
private noncomputable def BinaryOpenCoverSquareSubdivision.gridRowPrefixStateAt
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V) :
    (p : ℕ) → (hp : p < D.steps) →
      let row := D.gridFramedFullRowStateAt hxU hxV hUV hU hV p hp
      GridRowPrefixState (binaryVanKampenPushout U V hxU hxV) row.topWord
  | 0, hp =>
      let row := D.gridFramedFullRowStateAt hxU hxV hUV hU hV 0 hp
      { leftWord := row.leftEdge
        rightWord := row.boundary.focus
        bottomWord := row.boundary.after * row.bottomPrefix
        relation := D.gridFramedFullRowStateAt_standard_relation
          hxU hxV hUV hU hV 0 hp }
  | p + 1, hp =>
      let hp' : p < D.steps := Nat.lt_trans (Nat.lt_succ_self p) hp
      let lower := D.gridRowPrefixStateAt hxU hxV hUV hU hV p hp'
      let upper := D.gridFramedFullRowStateAt hxU hxV hUV hU hV (p + 1) hp
      let lowerRow := D.gridFramedFullRowStateAt hxU hxV hUV hU hV p hp'
      let hshared : upper.boundary.after * upper.bottomPrefix = lowerRow.topWord :=
        (D.gridFramedFullRow_topWord_eq_next_bottomWord
          hxU hxV hUV hU hV p hp).symm
      { leftWord := upper.leftEdge * lower.leftWord
        rightWord := upper.boundary.focus * lower.rightWord
        bottomWord := lower.bottomWord
        relation := by
          have hglue := twoRowBoundaries_glue
            lower.leftWord lowerRow.topWord lower.rightWord lower.bottomWord
            upper.leftEdge upper.topWord upper.boundary.focus
              (upper.boundary.after * upper.bottomPrefix)
            lower.relation
            (D.gridFramedFullRowStateAt_standard_relation
              hxU hxV hUV hU hV (p + 1) hp)
            hshared
          simpa [mul_assoc] using hglue }

/-- 从底行到第 `p` 行，沿左外侧自上而下出现的规范化竖边词。递归次序与合并矩形的
左边界方向一致。-/
noncomputable def BinaryOpenCoverSquareSubdivision.gridLeftBoundaryWordAt
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V) :
    (p : ℕ) → (hp : p < D.steps) → binaryVanKampenPushout U V hxU hxV
  | 0, hp =>
      (D.gridFramedFullRowStateAt hxU hxV hUV hU hV 0 hp).leftEdge
  | p + 1, hp =>
      let hp' : p < D.steps := Nat.lt_trans (Nat.lt_succ_self p) hp
      let upper := D.gridFramedFullRowStateAt hxU hxV hUV hU hV (p + 1) hp
      upper.leftEdge * D.gridLeftBoundaryWordAt hxU hxV hUV hU hV p hp'

/-- 从底行到第 `p` 行，沿右外侧按各行自下而上的规范化竖边词。乘积次序与合并矩形的
标准边界关系一致。-/
noncomputable def BinaryOpenCoverSquareSubdivision.gridRightBoundaryWordAt
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V) :
    (p : ℕ) → (hp : p < D.steps) → binaryVanKampenPushout U V hxU hxV
  | 0, hp =>
      (D.gridFramedFullRowStateAt hxU hxV hUV hU hV 0 hp).boundary.focus
  | p + 1, hp =>
      let hp' : p < D.steps := Nat.lt_trans (Nat.lt_succ_self p) hp
      let upper := D.gridFramedFullRowStateAt hxU hxV hUV hU hV (p + 1) hp
      upper.boundary.focus * D.gridRightBoundaryWordAt hxU hxV hUV hU hV p hp'

/-- 整张方格的下外侧词，即第零行完整的下边词。-/
noncomputable def BinaryOpenCoverSquareSubdivision.gridBottomBoundaryWord
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V) :
    binaryVanKampenPushout U V hxU hxV :=
  let row := D.gridFramedFullRowStateAt hxU hxV hUV hU hV 0 D.steps_pos
  row.boundary.after * row.bottomPrefix

/-- 整张方格的上外侧词，即最后一行完整的上边词。-/
noncomputable def BinaryOpenCoverSquareSubdivision.gridTopBoundaryWord
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V) :
    binaryVanKampenPushout U V hxU hxV :=
  (D.gridFramedFullRowStateAt hxU hxV hUV hU hV
    (D.steps - 1) (Nat.sub_lt D.steps_pos Nat.zero_lt_one)).topWord

private theorem BinaryOpenCoverSquareSubdivision.gridRowPrefixStateAt_leftWord
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V) :
    ∀ (p : ℕ) (hp : p < D.steps),
      (D.gridRowPrefixStateAt hxU hxV hUV hU hV p hp).leftWord =
        D.gridLeftBoundaryWordAt hxU hxV hUV hU hV p hp
  | 0, _ => rfl
  | p + 1, hp => by
      have hp' : p < D.steps := Nat.lt_trans (Nat.lt_succ_self p) hp
      let upper := D.gridFramedFullRowStateAt hxU hxV hUV hU hV (p + 1) hp
      change upper.leftEdge *
          (D.gridRowPrefixStateAt hxU hxV hUV hU hV p hp').leftWord =
        upper.leftEdge * D.gridLeftBoundaryWordAt hxU hxV hUV hU hV p hp'
      rw [D.gridRowPrefixStateAt_leftWord hxU hxV hUV hU hV p hp']

private theorem BinaryOpenCoverSquareSubdivision.gridRowPrefixStateAt_rightWord
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V) :
    ∀ (p : ℕ) (hp : p < D.steps),
      (D.gridRowPrefixStateAt hxU hxV hUV hU hV p hp).rightWord =
        D.gridRightBoundaryWordAt hxU hxV hUV hU hV p hp
  | 0, _ => rfl
  | p + 1, hp => by
      have hp' : p < D.steps := Nat.lt_trans (Nat.lt_succ_self p) hp
      let upper := D.gridFramedFullRowStateAt hxU hxV hUV hU hV (p + 1) hp
      change upper.boundary.focus *
          (D.gridRowPrefixStateAt hxU hxV hUV hU hV p hp').rightWord =
        upper.boundary.focus * D.gridRightBoundaryWordAt hxU hxV hUV hU hV p hp'
      rw [D.gridRowPrefixStateAt_rightWord hxU hxV hUV hU hV p hp']

private theorem BinaryOpenCoverSquareSubdivision.gridRowPrefixStateAt_bottomWord
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V) :
    ∀ (p : ℕ) (hp : p < D.steps),
      (D.gridRowPrefixStateAt hxU hxV hUV hU hV p hp).bottomWord =
        D.gridBottomBoundaryWord hxU hxV hUV hU hV
  | 0, hp => by
      simp only [BinaryOpenCoverSquareSubdivision.gridRowPrefixStateAt,
        BinaryOpenCoverSquareSubdivision.gridBottomBoundaryWord]
  | p + 1, hp => by
      have hp' : p < D.steps := Nat.lt_trans (Nat.lt_succ_self p) hp
      change (D.gridRowPrefixStateAt hxU hxV hUV hU hV p hp').bottomWord = _
      exact D.gridRowPrefixStateAt_bottomWord hxU hxV hUV hU hV p hp'

/-- 完整方格的四侧词版边界关系。这里的 top 是最高一行，bottom 是第零行，left/right
分别是沿所有行累积的两条外侧。
@isnad1 id=other.5h6v.s10.87fb03632d1d from=translated src=- shape=bbf3f1f7 vocab=0f354aff
-/
theorem BinaryOpenCoverSquareSubdivision.gridPerimeterWords_standard_relation
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V) :
    let last : ℕ := D.steps - 1
    let hlast : last < D.steps := Nat.sub_lt D.steps_pos Nat.zero_lt_one
    (D.gridLeftBoundaryWordAt hxU hxV hUV hU hV last hlast)⁻¹ *
        (D.gridTopBoundaryWord hxU hxV hUV hU hV)⁻¹ *
        D.gridRightBoundaryWordAt hxU hxV hUV hU hV last hlast *
        D.gridBottomBoundaryWord hxU hxV hUV hU hV = 1 := by
  let last : ℕ := D.steps - 1
  let hlast : last < D.steps := Nat.sub_lt D.steps_pos Nat.zero_lt_one
  let S := D.gridRowPrefixStateAt hxU hxV hUV hU hV last hlast
  let top := D.gridFramedFullRowStateAt hxU hxV hUV hU hV last hlast
  dsimp only
  rw [← D.gridRowPrefixStateAt_leftWord hxU hxV hUV hU hV last hlast,
    ← D.gridRowPrefixStateAt_rightWord hxU hxV hUV hU hV last hlast,
    ← D.gridRowPrefixStateAt_bottomWord hxU hxV hUV hU hV last hlast]
  exact S.relation

/-- 整张有限方格在递归 frames 上满足单一的四边外边界关系；所有内部横边和竖边
均已在构造状态的过程中消去。
@isnad1 id=other.5h6v.s10.87fb03632d1d from=translated src=- shape=bbf3f1f7 vocab=0f354aff
-/
theorem BinaryOpenCoverSquareSubdivision.gridFullBoundary_standard_relation
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V) :
    let last : ℕ := D.steps - 1
    let hlast : last < D.steps := Nat.sub_lt D.steps_pos Nat.zero_lt_one
    (D.gridLeftBoundaryWordAt hxU hxV hUV hU hV last hlast)⁻¹ *
        (D.gridTopBoundaryWord hxU hxV hUV hU hV)⁻¹ *
        D.gridRightBoundaryWordAt hxU hxV hUV hU hV last hlast *
        D.gridBottomBoundaryWord hxU hxV hUV hU hV = 1 := by
  exact D.gridPerimeterWords_standard_relation hxU hxV hUV hU hV

end SandronesLibrary.Topology
