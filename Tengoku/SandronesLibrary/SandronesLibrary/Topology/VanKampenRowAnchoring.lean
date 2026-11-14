/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.VanKampenNormalizedGridGauge

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# van Kampen 单行 frames 的右锚定

本文件证明在一行 frames 的底部和顶部统一右乘 gauges 只会共轭重基边，因而保持所有已归一化横边
为一。选择 gauges 使最右两个 frames 达到指定值，即得到保持水平相容的右锚定行；同时证明固定一端
frame 时另一端 frame 的归一化唯一性。

当前条目：

* `topology.fundamental-group.van-kampen-row-anchoring`。

行级右乘和锚定构造细节为 private；下一模块只消费最终右锚定 frames 及高层性质。本文件不构造二维
网格，不证明左边界为一、kernel、单射或 van Kampen 同构。
-/

open Set
open scoped unitInterval

noncomputable section

namespace SandronesLibrary.Topology

variable {X : Type*} [TopologicalSpace X]

/-- 分别在一个单格的底部两角和顶部两角统一右乘 gauge。

> **Entry**: topology.fundamental-group.van-kampen-row-anchoring-/
def CellVertexFrames.mulRight
    {G : Type*} [Group G] (F : CellVertexFrames G)
    (bottomGauge topGauge : G) : CellVertexFrames G where
  bottomLeft := F.bottomLeft * bottomGauge
  bottomRight := F.bottomRight * bottomGauge
  topRight := F.topRight * topGauge
  topLeft := F.topLeft * topGauge

/-- 同时右移一条边两端的 frame，只把规范化边元素整体共轭。-/
theorem rebaseEdge_mulRight
    {G : Type*} [Group G] (startFrame endFrame edge gauge : G) :
    rebaseEdge (startFrame * gauge) (endFrame * gauge) edge =
      gauge⁻¹ * rebaseEdge startFrame endFrame edge * gauge := by
  simp [rebaseEdge, mul_assoc]

/-- 已归一化为单位元的边在两端统一右乘任意 gauge 后仍归一化为单位元。-/
theorem rebaseEdge_mulRight_eq_one
    {G : Type*} [Group G] (startFrame endFrame edge gauge : G)
    (h : rebaseEdge startFrame endFrame edge = 1) :
    rebaseEdge (startFrame * gauge) (endFrame * gauge) edge = 1 := by
  rw [rebaseEdge_mulRight, h]
  simp

/-- 水平相邻 cell frames 的相容性在底部和顶部各自统一右乘 gauge 后保持。-/
theorem HorizontalCellFramesCompatible.mulRight
    {G : Type*} [Group G] {T : EdgeTransitions G}
    {left right : CellVertexFrames G}
    (h : HorizontalCellFramesCompatible T left right)
    (bottomGauge topGauge : G) :
    HorizontalCellFramesCompatible T
      (left.mulRight bottomGauge topGauge)
      (right.mulRight bottomGauge topGauge) := by
  constructor
  · change right.bottomLeft * bottomGauge =
      T.startChange * (left.bottomRight * bottomGauge)
    rw [h.bottom, mul_assoc]
  · change right.topLeft * topGauge =
      T.endChange * (left.topRight * topGauge)
    rw [h.top, mul_assoc]

/-- 一整行 frames 分别在底部、顶部统一右乘 gauge。-/
private def rowFramesMulRight
    {G : Type*} [Group G] (frames : Fin n → CellVertexFrames G)
    (bottomGauge topGauge : G) : Fin n → CellVertexFrames G :=
  fun i => (frames i).mulRight bottomGauge topGauge

/-- 水平相容的整行在统一右移底部、顶部 gauges 后仍水平相容。-/
private theorem rowFramesMulRight_compatible
    {G : Type*} [Group G]
    (transitions : ∀ (i k : Fin n), i.succ = k.castSucc → EdgeTransitions G)
    (frames : Fin n → CellVertexFrames G)
    (hframes : ∀ (i k : Fin n) (hshared : i.succ = k.castSucc),
      HorizontalCellFramesCompatible (transitions i k hshared) (frames i) (frames k))
    (bottomGauge topGauge : G)
    (i k : Fin n) (hshared : i.succ = k.castSucc) :
    HorizontalCellFramesCompatible (transitions i k hshared)
      (rowFramesMulRight frames bottomGauge topGauge i)
      (rowFramesMulRight frames bottomGauge topGauge k) :=
  (hframes i k hshared).mulRight bottomGauge topGauge

/-- 通过底部、顶部各自统一右移，把一整行最右格的两个右侧 frames 调整到指定值。-/
private def anchorRowFramesRight
    {G : Type*} [Group G] (frames : Fin n → CellVertexFrames G)
    (hn : 0 < n) (desiredBottomRight desiredTopRight : G) :
    Fin n → CellVertexFrames G :=
  let last : Fin n := ⟨n - 1, Nat.sub_lt hn Nat.zero_lt_one⟩
  rowFramesMulRight frames
    ((frames last).bottomRight⁻¹ * desiredBottomRight)
    ((frames last).topRight⁻¹ * desiredTopRight)

/-- 右锚定后的最右底部 frame 严格等于指定值。-/
@[simp] private theorem anchorRowFramesRight_last_bottomRight
    {G : Type*} [Group G] (frames : Fin n → CellVertexFrames G)
    (hn : 0 < n) (desiredBottomRight desiredTopRight : G) :
    let last : Fin n := ⟨n - 1, Nat.sub_lt hn Nat.zero_lt_one⟩
    (anchorRowFramesRight frames hn desiredBottomRight desiredTopRight last).bottomRight =
      desiredBottomRight := by
  dsimp [anchorRowFramesRight, rowFramesMulRight, CellVertexFrames.mulRight]
  simp

/-- 右锚定后的最右顶部 frame 严格等于指定值。-/
@[simp] private theorem anchorRowFramesRight_last_topRight
    {G : Type*} [Group G] (frames : Fin n → CellVertexFrames G)
    (hn : 0 < n) (desiredBottomRight desiredTopRight : G) :
    let last : Fin n := ⟨n - 1, Nat.sub_lt hn Nat.zero_lt_one⟩
    (anchorRowFramesRight frames hn desiredBottomRight desiredTopRight last).topRight =
      desiredTopRight := by
  dsimp [anchorRowFramesRight, rowFramesMulRight, CellVertexFrames.mulRight]
  simp

/-- 右锚定保持整行的水平 transition 相容性。-/
private theorem anchorRowFramesRight_compatible
    {G : Type*} [Group G]
    (transitions : ∀ (i k : Fin n), i.succ = k.castSucc → EdgeTransitions G)
    (frames : Fin n → CellVertexFrames G)
    (hframes : ∀ (i k : Fin n) (hshared : i.succ = k.castSucc),
      HorizontalCellFramesCompatible (transitions i k hshared) (frames i) (frames k))
    (hn : 0 < n) (desiredBottomRight desiredTopRight : G)
    (i k : Fin n) (hshared : i.succ = k.castSucc) :
    HorizontalCellFramesCompatible (transitions i k hshared)
      (anchorRowFramesRight frames hn desiredBottomRight desiredTopRight i)
      (anchorRowFramesRight frames hn desiredBottomRight desiredTopRight k) := by
  apply rowFramesMulRight_compatible transitions frames hframes

/-- 在给定最右下 frame 后，把一行 gauge-normalized frames 锚定到最右边：最右上 frame
定义为真实右竖边元素乘最右下 frame，因此最右竖边同时被归一化。-/
noncomputable def BinaryOpenCoverSquareSubdivision.rightAnchoredRowFrames
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (j : Fin D.steps) (desiredBottomRight : binaryVanKampenPushout U V hxU hxV) :
    Fin D.steps → CellVertexFrames (binaryVanKampenPushout U V hxU hxV) :=
  let last : Fin D.steps :=
    ⟨D.steps - 1, Nat.sub_lt D.steps_pos Nat.zero_lt_one⟩
  let rightEdge : binaryVanKampenPushout U V hxU hxV :=
    Monoid.PushoutI.of (D.label last j)
      (D.gridCellBasedVerticalEdgeInPiece hxU hxV hU hV last j 1)
  anchorRowFramesRight
    (D.gaugeNormalizedRowFrames hxU hxV hUV hU hV j)
    D.steps_pos desiredBottomRight (rightEdge * desiredBottomRight)

/-- 右锚定行仍与全部真实水平 internal transitions 相容。-/
theorem BinaryOpenCoverSquareSubdivision.rightAnchoredRowFrames_compatible
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (j : Fin D.steps) (desiredBottomRight : binaryVanKampenPushout U V hxU hxV)
    (i k : Fin D.steps) (hshared : i.succ = k.castSucc) :
    HorizontalCellFramesCompatible
      (D.horizontalInternalEdgeTransitions hxU hxV hUV hU hV i k j hshared)
      (D.rightAnchoredRowFrames hxU hxV hUV hU hV j desiredBottomRight i)
      (D.rightAnchoredRowFrames hxU hxV hUV hU hV j desiredBottomRight k) := by
  unfold BinaryOpenCoverSquareSubdivision.rightAnchoredRowFrames
  apply anchorRowFramesRight_compatible
    (fun i k h => D.horizontalInternalEdgeTransitions hxU hxV hUV hU hV i k j h)
    (D.gaugeNormalizedRowFrames hxU hxV hUV hU hV j)
    (D.gaugeNormalizedRowFrames_compatible hxU hxV hUV hU hV j)

/-- 右锚定保持每格上下横边的单位元归一化。-/
theorem BinaryOpenCoverSquareSubdivision.rightAnchoredRowFrames_horizontal_edges
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (j : Fin D.steps) (desiredBottomRight : binaryVanKampenPushout U V hxU hxV)
    (i : Fin D.steps) :
    let F := D.rightAnchoredRowFrames hxU hxV hUV hU hV j desiredBottomRight i
    rebaseEdge F.bottomLeft F.bottomRight
        (Monoid.PushoutI.of (D.label i j)
          (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i j 0)) = 1 ∧
      rebaseEdge F.topLeft F.topRight
        (Monoid.PushoutI.of (D.label i j)
          (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i j 1)) = 1 := by
  let baseFrames := D.gaugeNormalizedRowFrames hxU hxV hUV hU hV j
  let last : Fin D.steps :=
    ⟨D.steps - 1, Nat.sub_lt D.steps_pos Nat.zero_lt_one⟩
  let rightEdge : binaryVanKampenPushout U V hxU hxV :=
    Monoid.PushoutI.of (D.label last j)
      (D.gridCellBasedVerticalEdgeInPiece hxU hxV hU hV last j 1)
  let bottomGauge := (baseFrames last).bottomRight⁻¹ * desiredBottomRight
  let topGauge := (baseFrames last).topRight⁻¹ *
    (rightEdge * desiredBottomRight)
  have hbase := D.gaugeNormalizedRowFrames_horizontal_edges
    hxU hxV hUV hU hV j i
  change rebaseEdge
      ((baseFrames i).bottomLeft * bottomGauge)
      ((baseFrames i).bottomRight * bottomGauge)
      (Monoid.PushoutI.of (D.label i j)
        (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i j 0)) = 1 ∧
    rebaseEdge
      ((baseFrames i).topLeft * topGauge)
      ((baseFrames i).topRight * topGauge)
      (Monoid.PushoutI.of (D.label i j)
        (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i j 1)) = 1
  exact ⟨rebaseEdge_mulRight_eq_one _ _ _ bottomGauge hbase.1,
    rebaseEdge_mulRight_eq_one _ _ _ topGauge hbase.2⟩

/-- 右锚定行的最右真实竖边严格归一化为单位元。-/
theorem BinaryOpenCoverSquareSubdivision.rightAnchoredRowFrames_right_edge_eq_one
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (j : Fin D.steps) (desiredBottomRight : binaryVanKampenPushout U V hxU hxV) :
    let last : Fin D.steps :=
      ⟨D.steps - 1, Nat.sub_lt D.steps_pos Nat.zero_lt_one⟩
    let F := D.rightAnchoredRowFrames hxU hxV hUV hU hV j desiredBottomRight last
    rebaseEdge F.bottomRight F.topRight
      (Monoid.PushoutI.of (D.label last j)
        (D.gridCellBasedVerticalEdgeInPiece hxU hxV hU hV last j 1)) = 1 := by
  let last : Fin D.steps :=
    ⟨D.steps - 1, Nat.sub_lt D.steps_pos Nat.zero_lt_one⟩
  let rightEdge : binaryVanKampenPushout U V hxU hxV :=
    Monoid.PushoutI.of (D.label last j)
      (D.gridCellBasedVerticalEdgeInPiece hxU hxV hU hV last j 1)
  dsimp only
  unfold BinaryOpenCoverSquareSubdivision.rightAnchoredRowFrames
  rw [anchorRowFramesRight_last_bottomRight,
    anchorRowFramesRight_last_topRight]
  change rebaseEdge desiredBottomRight (rightEdge * desiredBottomRight) rightEdge = 1
  exact rebaseEdge_mul_start_eq_one desiredBottomRight rightEdge

/-- 同一条边在相同右端 frame 下有两个单位元归一化时，两个左端 frames 必须相等。-/
theorem rebaseEdge_startFrame_unique
    {G : Type*} [Group G] (firstStart secondStart endFrame edge : G)
    (hfirst : rebaseEdge firstStart endFrame edge = 1)
    (hsecond : rebaseEdge secondStart endFrame edge = 1) :
    firstStart = secondStart := by
  have h : (endFrame⁻¹ * edge) * firstStart =
      (endFrame⁻¹ * edge) * secondStart := by
    simpa [rebaseEdge, mul_assoc] using hfirst.trans hsecond.symm
  exact mul_left_cancel h

/-- 同一条边在相同左端 frame 下有两个单位元归一化时，两个右端 frames 必须相等。-/
theorem rebaseEdge_endFrame_unique
    {G : Type*} [Group G] (startFrame firstEnd secondEnd edge : G)
    (hfirst : rebaseEdge startFrame firstEnd edge = 1)
    (hsecond : rebaseEdge startFrame secondEnd edge = 1) :
    firstEnd = secondEnd := by
  have hfirst' : edge * startFrame = firstEnd := by
    have h := congrArg (fun z => firstEnd * z) hfirst
    simpa [rebaseEdge, mul_assoc] using h
  have hsecond' : edge * startFrame = secondEnd := by
    have h := congrArg (fun z => secondEnd * z) hsecond
    simpa [rebaseEdge, mul_assoc] using h
  exact hfirst'.symm.trans hsecond'

end SandronesLibrary.Topology
