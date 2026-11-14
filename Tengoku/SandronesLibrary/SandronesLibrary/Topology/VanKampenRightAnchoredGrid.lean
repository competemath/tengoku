/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.VanKampenRowAnchoring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# van Kampen 右锚定网格与左边界消失

本文件沿最右列递归选择各行锚点，并用中央 transition coherence 将竖直 frame 相容逐格向左传播，
构造二维右锚定 frames。完整行左右边相等且右边为一，因而逐行左边也为一；最终完整左边界 holonomy
严格消失。

当前条目：

* `topology.fundamental-group.van-kampen-right-anchored-grid`。

本文件不读取 row-prefix 名称，止于左边界消去；尚未建立 kernel 字母词、单射或 van Kampen 同构。
-/

open Set
open scoped unitInterval

noncomputable section

namespace SandronesLibrary.Topology

variable {X : Type*} [TopologicalSpace X]

/-- 一条竖直共享横边的下行上边和上行下边都归一化为单位元；若上行右端 frame 已等于
竖直 transition 对下行右端 frame 的提升，则上行左端 frame 也唯一等于相应提升。

> **Entry**: topology.fundamental-group.van-kampen-right-anchored-grid-/
private theorem verticalFrames_start_of_right
    {G : Type*} [Group G]
    (vertical : EdgeTransitions G)
    (lowerStart lowerEnd upperStart upperEnd lowerEdge upperEdge : G)
    (hedge : lowerEdge = rebaseEdge vertical.startChange vertical.endChange upperEdge)
    (hlower : rebaseEdge lowerStart lowerEnd lowerEdge = 1)
    (hupper : rebaseEdge upperStart upperEnd upperEdge = 1)
    (hright : upperEnd = vertical.endChange * lowerEnd) :
    upperStart = vertical.startChange * lowerStart := by
  have htransport := rebaseEdge_relation_in_frame lowerStart lowerEnd
    vertical.startChange vertical.endChange lowerEdge upperEdge hedge
  have hexpected : rebaseEdge
      (vertical.startChange * lowerStart)
      (vertical.endChange * lowerEnd) upperEdge = 1 := by
    rw [← htransport]
    exact hlower
  rw [← hright] at hexpected
  exact rebaseEdge_startFrame_unique upperStart
    (vertical.startChange * lowerStart) upperEnd upperEdge hupper hexpected

/-- 中央 transition 方块中，若右格左端网格顶点已经满足竖直 frame 提升关系，则该关系可
反向传播到左格右端网格顶点。-/
private theorem verticalFrames_descend_across_horizontal
    {G : Type*} [Group G]
    (horizontalLower horizontalUpper verticalLeft verticalRight : EdgeTransitions G)
    (leftLower rightLower leftUpper rightUpper : CellVertexFrames G)
    (hLower : HorizontalCellFramesCompatible horizontalLower leftLower rightLower)
    (hUpper : HorizontalCellFramesCompatible horizontalUpper leftUpper rightUpper)
    (hSquare : verticalRight.startChange * horizontalLower.endChange =
      horizontalUpper.startChange * verticalLeft.endChange)
    (hRightStart : rightUpper.bottomLeft =
      verticalRight.startChange * rightLower.topLeft) :
    leftUpper.bottomRight = verticalLeft.endChange * leftLower.topRight := by
  have h : horizontalUpper.startChange * leftUpper.bottomRight =
      horizontalUpper.startChange * (verticalLeft.endChange * leftLower.topRight) := by
    calc
      horizontalUpper.startChange * leftUpper.bottomRight =
          rightUpper.bottomLeft := hUpper.bottom.symm
      _ = verticalRight.startChange * rightLower.topLeft := hRightStart
      _ = verticalRight.startChange *
          (horizontalLower.endChange * leftLower.topRight) := by rw [hLower.top]
      _ = (verticalRight.startChange * horizontalLower.endChange) *
          leftLower.topRight := by rw [mul_assoc]
      _ = (horizontalUpper.startChange * verticalLeft.endChange) *
          leftLower.topRight := by rw [hSquare]
      _ = horizontalUpper.startChange *
          (verticalLeft.endChange * leftLower.topRight) := by rw [mul_assoc]
  exact mul_left_cancel h

/-- 相邻两行在同一单格四个角上的竖直 frame 提升相容性。-/
structure VerticalCellFramesCompatible
    {G : Type*} [Group G] (vertical : EdgeTransitions G)
    (lower upper : CellVertexFrames G) : Prop where
  left : upper.bottomLeft = vertical.startChange * lower.topLeft
  right : upper.bottomRight = vertical.endChange * lower.topRight

/-- 已知同一单格右端竖直相容，且上下共享横边分别归一化为单位元时，竖直边关系唯一确定
左端相容性。-/
private theorem verticalCellFramesCompatible_of_right
    {G : Type*} [Group G]
    (vertical : EdgeTransitions G) (lower upper : CellVertexFrames G)
    (lowerEdge upperEdge : G)
    (hedge : lowerEdge = rebaseEdge vertical.startChange vertical.endChange upperEdge)
    (hlower : rebaseEdge lower.topLeft lower.topRight lowerEdge = 1)
    (hupper : rebaseEdge upper.bottomLeft upper.bottomRight upperEdge = 1)
    (hright : upper.bottomRight = vertical.endChange * lower.topRight) :
    VerticalCellFramesCompatible vertical lower upper := by
  exact ⟨verticalFrames_start_of_right vertical
    lower.topLeft lower.topRight upper.bottomLeft upper.bottomRight
    lowerEdge upperEdge hedge hlower hupper hright, hright⟩

/-- 水平相邻两格中，右格已竖直相容时，中央 coherence 先给出左格右端相容；再利用左格
共享横边的单位元归一化，得到左格完整竖直相容。-/
private theorem verticalCellFramesCompatible_descend
    {G : Type*} [Group G]
    (horizontalLower horizontalUpper verticalLeft verticalRight : EdgeTransitions G)
    (leftLower rightLower leftUpper rightUpper : CellVertexFrames G)
    (leftLowerEdge leftUpperEdge : G)
    (hHorizontalLower : HorizontalCellFramesCompatible
      horizontalLower leftLower rightLower)
    (hHorizontalUpper : HorizontalCellFramesCompatible
      horizontalUpper leftUpper rightUpper)
    (hSquare : verticalRight.startChange * horizontalLower.endChange =
      horizontalUpper.startChange * verticalLeft.endChange)
    (hRight : VerticalCellFramesCompatible verticalRight rightLower rightUpper)
    (hLeftEdge : leftLowerEdge =
      rebaseEdge verticalLeft.startChange verticalLeft.endChange leftUpperEdge)
    (hLeftLower : rebaseEdge leftLower.topLeft leftLower.topRight leftLowerEdge = 1)
    (hLeftUpper : rebaseEdge leftUpper.bottomLeft leftUpper.bottomRight leftUpperEdge = 1) :
    VerticalCellFramesCompatible verticalLeft leftLower leftUpper := by
  have hrightEndpoint : leftUpper.bottomRight =
      verticalLeft.endChange * leftLower.topRight :=
    verticalFrames_descend_across_horizontal
      horizontalLower horizontalUpper verticalLeft verticalRight
      leftLower rightLower leftUpper rightUpper
      hHorizontalLower hHorizontalUpper hSquare hRight.left
  exact verticalCellFramesCompatible_of_right verticalLeft leftLower leftUpper
    leftLowerEdge leftUpperEdge hLeftEdge hLeftLower hLeftUpper hrightEndpoint

/-- 在实际细分网格中，右侧单格的竖直 frame 相容性可沿一个中央顶点向左传播。
这里把抽象下降引理所需的 transition 方块、共享边关系和两条单位元归一化全部由
`BinaryOpenCoverSquareSubdivision` 的真实接口提供。-/
private theorem BinaryOpenCoverSquareSubdivision.verticalCellFramesCompatible_descend
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j l : Fin D.steps)
    (hHorizontal : i.succ = k.castSucc) (hVertical : j.succ = l.castSucc)
    (lowerFrames upperFrames : Fin D.steps →
      CellVertexFrames (binaryVanKampenPushout U V hxU hxV))
    (hLower : HorizontalCellFramesCompatible
      (D.horizontalInternalEdgeTransitions hxU hxV hUV hU hV i k j hHorizontal)
      (lowerFrames i) (lowerFrames k))
    (hUpper : HorizontalCellFramesCompatible
      (D.horizontalInternalEdgeTransitions hxU hxV hUV hU hV i k l hHorizontal)
      (upperFrames i) (upperFrames k))
    (hRight : VerticalCellFramesCompatible
      (D.verticalInternalEdgeTransitions hxU hxV hUV hU hV k j l hVertical)
      (lowerFrames k) (upperFrames k))
    (hLowerEdge : rebaseEdge (lowerFrames i).topLeft (lowerFrames i).topRight
      (Monoid.PushoutI.of (D.label i j)
        (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i j 1)) = 1)
    (hUpperEdge : rebaseEdge (upperFrames i).bottomLeft (upperFrames i).bottomRight
      (Monoid.PushoutI.of (D.label i l)
        (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i l 0)) = 1) :
    VerticalCellFramesCompatible
      (D.verticalInternalEdgeTransitions hxU hxV hUV hU hV i j l hVertical)
      (lowerFrames i) (upperFrames i) := by
  apply SandronesLibrary.Topology.verticalCellFramesCompatible_descend
    (D.horizontalInternalEdgeTransitions hxU hxV hUV hU hV i k j hHorizontal)
    (D.horizontalInternalEdgeTransitions hxU hxV hUV hU hV i k l hHorizontal)
    (D.verticalInternalEdgeTransitions hxU hxV hUV hU hV i j l hVertical)
    (D.verticalInternalEdgeTransitions hxU hxV hUV hU hV k j l hVertical)
    (lowerFrames i) (lowerFrames k) (upperFrames i) (upperFrames k)
    (Monoid.PushoutI.of (D.label i j)
      (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i j 1))
    (Monoid.PushoutI.of (D.label i l)
      (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i l 0))
  · exact hLower
  · exact hUpper
  · exact D.centralInternalTransitions_square hxU hxV hUV hU hV
      i k j l hHorizontal hVertical
  · exact hRight
  · exact D.verticalInternalEdge_relation hxU hxV hUV hU hV i j l hVertical
  · exact hLowerEdge
  · exact hUpperEdge

/-- 若相邻两行在每格的共享横边都已归一化，且两行分别水平相容，那么最右格的竖直
frame 相容性会沿有限列反向归纳传播到全部格子。-/
private theorem BinaryOpenCoverSquareSubdivision.verticalCellFramesCompatible_all_of_last
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (j l : Fin D.steps) (hVertical : j.succ = l.castSucc)
    (lowerFrames upperFrames : Fin D.steps →
      CellVertexFrames (binaryVanKampenPushout U V hxU hxV))
    (hLower : ∀ (i k : Fin D.steps) (hHorizontal : i.succ = k.castSucc),
      HorizontalCellFramesCompatible
        (D.horizontalInternalEdgeTransitions hxU hxV hUV hU hV i k j hHorizontal)
        (lowerFrames i) (lowerFrames k))
    (hUpper : ∀ (i k : Fin D.steps) (hHorizontal : i.succ = k.castSucc),
      HorizontalCellFramesCompatible
        (D.horizontalInternalEdgeTransitions hxU hxV hUV hU hV i k l hHorizontal)
        (upperFrames i) (upperFrames k))
    (hLowerEdge : ∀ i : Fin D.steps,
      rebaseEdge (lowerFrames i).topLeft (lowerFrames i).topRight
        (Monoid.PushoutI.of (D.label i j)
          (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i j 1)) = 1)
    (hUpperEdge : ∀ i : Fin D.steps,
      rebaseEdge (upperFrames i).bottomLeft (upperFrames i).bottomRight
        (Monoid.PushoutI.of (D.label i l)
          (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i l 0)) = 1)
    (hLast : let last : Fin D.steps :=
        ⟨D.steps - 1, Nat.sub_lt D.steps_pos Nat.zero_lt_one⟩
      VerticalCellFramesCompatible
        (D.verticalInternalEdgeTransitions hxU hxV hUV hU hV last j l hVertical)
        (lowerFrames last) (upperFrames last)) :
    ∀ i : Fin D.steps,
      VerticalCellFramesCompatible
        (D.verticalInternalEdgeTransitions hxU hxV hUV hU hV i j l hVertical)
        (lowerFrames i) (upperFrames i) := by
  let n := D.steps - 1
  have hsteps : n + 1 = D.steps := Nat.sub_add_cancel D.steps_pos
  let castIndex : Fin (n + 1) → Fin D.steps := Fin.cast hsteps
  let P : Fin (n + 1) → Prop := fun i =>
    VerticalCellFramesCompatible
      (D.verticalInternalEdgeTransitions hxU hxV hUV hU hV
        (castIndex i) j l hVertical)
      (lowerFrames (castIndex i)) (upperFrames (castIndex i))
  have hall : ∀ i : Fin (n + 1), P i := by
    apply Fin.reverseInduction
    · have hlastIndex : castIndex (Fin.last n) =
          (⟨D.steps - 1, Nat.sub_lt D.steps_pos Nat.zero_lt_one⟩ : Fin D.steps) := by
          apply Fin.ext
          simp [castIndex, n]
      simpa [P, hlastIndex] using hLast
    · intro i hi
      let left : Fin D.steps := castIndex i.castSucc
      let right : Fin D.steps := castIndex i.succ
      have hHorizontal : left.succ = right.castSucc := by
        apply Fin.ext
        simp [left, right, castIndex]
      exact D.verticalCellFramesCompatible_descend hxU hxV hUV hU hV
        left right j l hHorizontal hVertical lowerFrames upperFrames
        (hLower left right hHorizontal) (hUpper left right hHorizontal) hi
        (hLowerEdge left) (hUpperEdge left)
  intro i
  have hi := hall (Fin.cast hsteps.symm i)
  simpa [P, castIndex] using hi

/-- 两个相邻的右锚定行中，若上行指定的最右下 frame 正是竖直 transition 对下行最右上
frame 的提升，则最右格满足完整竖直 frame 相容性。-/
private theorem BinaryOpenCoverSquareSubdivision.rightAnchoredRows_last_vertical_compatible
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (j l : Fin D.steps) (hVertical : j.succ = l.castSucc)
    (lowerBottomRight upperBottomRight : binaryVanKampenPushout U V hxU hxV)
    (hAnchor : let last : Fin D.steps :=
        ⟨D.steps - 1, Nat.sub_lt D.steps_pos Nat.zero_lt_one⟩
      let vertical := D.verticalInternalEdgeTransitions hxU hxV hUV hU hV
        last j l hVertical
      upperBottomRight = vertical.endChange *
        (D.rightAnchoredRowFrames hxU hxV hUV hU hV
          j lowerBottomRight last).topRight) :
    let last : Fin D.steps :=
      ⟨D.steps - 1, Nat.sub_lt D.steps_pos Nat.zero_lt_one⟩
    VerticalCellFramesCompatible
      (D.verticalInternalEdgeTransitions hxU hxV hUV hU hV last j l hVertical)
      (D.rightAnchoredRowFrames hxU hxV hUV hU hV j lowerBottomRight last)
      (D.rightAnchoredRowFrames hxU hxV hUV hU hV l upperBottomRight last) := by
  let last : Fin D.steps :=
    ⟨D.steps - 1, Nat.sub_lt D.steps_pos Nat.zero_lt_one⟩
  let lower := D.rightAnchoredRowFrames hxU hxV hUV hU hV
    j lowerBottomRight last
  let upper := D.rightAnchoredRowFrames hxU hxV hUV hU hV
    l upperBottomRight last
  let vertical := D.verticalInternalEdgeTransitions hxU hxV hUV hU hV
    last j l hVertical
  apply verticalCellFramesCompatible_of_right vertical lower upper
    (Monoid.PushoutI.of (D.label last j)
      (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV last j 1))
    (Monoid.PushoutI.of (D.label last l)
      (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV last l 0))
  · exact D.verticalInternalEdge_relation hxU hxV hUV hU hV
      last j l hVertical
  · exact (D.rightAnchoredRowFrames_horizontal_edges hxU hxV hUV hU hV
      j lowerBottomRight last).2
  · exact (D.rightAnchoredRowFrames_horizontal_edges hxU hxV hUV hU hV
      l upperBottomRight last).1
  · change upper.bottomRight = vertical.endChange * lower.topRight
    have hupper : upper.bottomRight = upperBottomRight := by
      simp [upper, BinaryOpenCoverSquareSubdivision.rightAnchoredRowFrames, last]
    rw [hupper]
    exact hAnchor

/-- 按真实最右竖直 transition 对齐两个相邻右锚定行后，两行在全部列上都竖直相容。-/
private theorem BinaryOpenCoverSquareSubdivision.rightAnchoredRows_vertical_compatible
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (j l : Fin D.steps) (hVertical : j.succ = l.castSucc)
    (lowerBottomRight upperBottomRight : binaryVanKampenPushout U V hxU hxV)
    (hAnchor : let last : Fin D.steps :=
        ⟨D.steps - 1, Nat.sub_lt D.steps_pos Nat.zero_lt_one⟩
      let vertical := D.verticalInternalEdgeTransitions hxU hxV hUV hU hV
        last j l hVertical
      upperBottomRight = vertical.endChange *
        (D.rightAnchoredRowFrames hxU hxV hUV hU hV
          j lowerBottomRight last).topRight) :
    ∀ i : Fin D.steps,
      VerticalCellFramesCompatible
        (D.verticalInternalEdgeTransitions hxU hxV hUV hU hV i j l hVertical)
        (D.rightAnchoredRowFrames hxU hxV hUV hU hV j lowerBottomRight i)
        (D.rightAnchoredRowFrames hxU hxV hUV hU hV l upperBottomRight i) := by
  apply D.verticalCellFramesCompatible_all_of_last hxU hxV hUV hU hV
    j l hVertical
    (D.rightAnchoredRowFrames hxU hxV hUV hU hV j lowerBottomRight)
    (D.rightAnchoredRowFrames hxU hxV hUV hU hV l upperBottomRight)
  · exact D.rightAnchoredRowFrames_compatible hxU hxV hUV hU hV
      j lowerBottomRight
  · exact D.rightAnchoredRowFrames_compatible hxU hxV hUV hU hV
      l upperBottomRight
  · intro i
    exact (D.rightAnchoredRowFrames_horizontal_edges hxU hxV hUV hU hV
      j lowerBottomRight i).2
  · intro i
    exact (D.rightAnchoredRowFrames_horizontal_edges hxU hxV hUV hU hV
      l upperBottomRight i).1
  · exact D.rightAnchoredRows_last_vertical_compatible hxU hxV hUV hU hV
      j l hVertical lowerBottomRight upperBottomRight hAnchor

/-- 从底行开始逐行选择最右锚点：底行最右下 frame 取 `1`；每个后继行最右下 frame
由真实最右竖直 transition 提升前一行最右上 frame。-/
noncomputable def BinaryOpenCoverSquareSubdivision.rightAnchoredGridRowFramesAt
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V) :
    (p : ℕ) → (hp : p < D.steps) → Fin D.steps →
      CellVertexFrames (binaryVanKampenPushout U V hxU hxV)
  | 0, hp => D.rightAnchoredRowFrames hxU hxV hUV hU hV ⟨0, hp⟩ 1
  | p + 1, hp =>
      let hp' : p < D.steps := Nat.lt_trans (Nat.lt_succ_self p) hp
      let j : Fin D.steps := ⟨p, hp'⟩
      let l : Fin D.steps := ⟨p + 1, hp⟩
      let hVertical : j.succ = l.castSucc := by apply Fin.ext; rfl
      let last : Fin D.steps :=
        ⟨D.steps - 1, Nat.sub_lt D.steps_pos Nat.zero_lt_one⟩
      let lower := D.rightAnchoredGridRowFramesAt hxU hxV hUV hU hV p hp'
      let vertical := D.verticalInternalEdgeTransitions hxU hxV hUV hU hV
        last j l hVertical
      D.rightAnchoredRowFrames hxU hxV hUV hU hV l
        (vertical.endChange * (lower last).topRight)

/-- 已右锚定的一行，以它自身最右下 frame 再调用右锚定接口时定义保持不变。-/
private theorem BinaryOpenCoverSquareSubdivision.rightAnchoredRowFrames_reanchor
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (j : Fin D.steps) (desiredBottomRight : binaryVanKampenPushout U V hxU hxV) :
    let last : Fin D.steps :=
      ⟨D.steps - 1, Nat.sub_lt D.steps_pos Nat.zero_lt_one⟩
    let frames := D.rightAnchoredRowFrames hxU hxV hUV hU hV j desiredBottomRight
    D.rightAnchoredRowFrames hxU hxV hUV hU hV j (frames last).bottomRight = frames := by
  let last : Fin D.steps :=
    ⟨D.steps - 1, Nat.sub_lt D.steps_pos Nat.zero_lt_one⟩
  let frames := D.rightAnchoredRowFrames hxU hxV hUV hU hV j desiredBottomRight
  have hlast : (frames last).bottomRight = desiredBottomRight := by
    simp [frames, BinaryOpenCoverSquareSubdivision.rightAnchoredRowFrames, last]
  dsimp only
  rw [hlast]

/-- 二维右锚定递归生成的每一行都与该行全部真实水平 transitions 相容。
@isnad1 id=horizont.7h9v.s8.22680147cce8 from=translated src=- shape=a05c7552 vocab=119bcc51
-/
theorem BinaryOpenCoverSquareSubdivision.rightAnchoredGridRowFramesAt_compatible
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (p : ℕ) (hp : p < D.steps)
    (i k : Fin D.steps) (hHorizontal : i.succ = k.castSucc) :
    HorizontalCellFramesCompatible
      (D.horizontalInternalEdgeTransitions hxU hxV hUV hU hV
        i k ⟨p, hp⟩ hHorizontal)
      (D.rightAnchoredGridRowFramesAt hxU hxV hUV hU hV p hp i)
      (D.rightAnchoredGridRowFramesAt hxU hxV hUV hU hV p hp k) := by
  cases p with
  | zero =>
      exact D.rightAnchoredRowFrames_compatible hxU hxV hUV hU hV
        ⟨0, hp⟩ 1 i k hHorizontal
  | succ p =>
      exact D.rightAnchoredRowFrames_compatible hxU hxV hUV hU hV
        ⟨p + 1, hp⟩
        ((D.verticalInternalEdgeTransitions hxU hxV hUV hU hV
            ⟨D.steps - 1, Nat.sub_lt D.steps_pos Nat.zero_lt_one⟩
            ⟨p, Nat.lt_trans (Nat.lt_succ_self p) hp⟩ ⟨p + 1, hp⟩
            (by apply Fin.ext; rfl)).endChange *
          (D.rightAnchoredGridRowFramesAt hxU hxV hUV hU hV p
            (Nat.lt_trans (Nat.lt_succ_self p) hp)
            ⟨D.steps - 1, Nat.sub_lt D.steps_pos Nat.zero_lt_one⟩).topRight)
        i k hHorizontal

/-- 二维右锚定递归中，每对相邻行在全部列上满足竖直 frame 相容性。
@isnad1 id=other.6h8v.s8.b2d4724752bd from=translated src=- shape=aa87cce0 vocab=90a1c3cc
-/
theorem BinaryOpenCoverSquareSubdivision.rightAnchoredGridRowFramesAt_vertical_compatible
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (p : ℕ) (hp : p + 1 < D.steps) (i : Fin D.steps) :
    let hp' : p < D.steps := Nat.lt_trans (Nat.lt_succ_self p) hp
    let j : Fin D.steps := ⟨p, hp'⟩
    let l : Fin D.steps := ⟨p + 1, hp⟩
    let hVertical : j.succ = l.castSucc := by apply Fin.ext; rfl
    VerticalCellFramesCompatible
      (D.verticalInternalEdgeTransitions hxU hxV hUV hU hV i j l hVertical)
      (D.rightAnchoredGridRowFramesAt hxU hxV hUV hU hV p hp' i)
      (D.rightAnchoredGridRowFramesAt hxU hxV hUV hU hV (p + 1) hp i) := by
  let hp' : p < D.steps := Nat.lt_trans (Nat.lt_succ_self p) hp
  let j : Fin D.steps := ⟨p, hp'⟩
  let l : Fin D.steps := ⟨p + 1, hp⟩
  have hVertical : j.succ = l.castSucc := by apply Fin.ext; rfl
  let last : Fin D.steps :=
    ⟨D.steps - 1, Nat.sub_lt D.steps_pos Nat.zero_lt_one⟩
  let lower := D.rightAnchoredGridRowFramesAt hxU hxV hUV hU hV p hp'
  let vertical := D.verticalInternalEdgeTransitions hxU hxV hUV hU hV
    last j l hVertical
  have hAll := D.rightAnchoredRows_vertical_compatible hxU hxV hUV hU hV
    j l hVertical (lower last).bottomRight
    (vertical.endChange * (lower last).topRight)
  have hlowerAnchor : D.rightAnchoredRowFrames hxU hxV hUV hU hV
      j (lower last).bottomRight = lower := by
    cases p with
    | zero =>
        exact D.rightAnchoredRowFrames_reanchor hxU hxV hUV hU hV
          j 1
    | succ p =>
        exact D.rightAnchoredRowFrames_reanchor hxU hxV hUV hU hV
          j ((D.verticalInternalEdgeTransitions hxU hxV hUV hU hV last
            ⟨p, Nat.lt_trans (Nat.lt_succ_self p) hp'⟩ j
            (by apply Fin.ext; rfl)).endChange *
              (D.rightAnchoredGridRowFramesAt hxU hxV hUV hU hV p
                (Nat.lt_trans (Nat.lt_succ_self p) hp') last).topRight)
  have hAnchor : vertical.endChange * (lower last).topRight =
      vertical.endChange *
        (D.rightAnchoredRowFrames hxU hxV hUV hU hV
          j (lower last).bottomRight last).topRight := by
    rw [hlowerAnchor]
  have hi := hAll hAnchor i
  rw [hlowerAnchor] at hi
  simpa [BinaryOpenCoverSquareSubdivision.rightAnchoredGridRowFramesAt,
    hp', j, l, hVertical, last, lower, vertical] using hi

/-- 二维右锚定递归中，每行每格的上下横边都严格归一化为单位元。
@isnad1 id=other.6h8v.s12.b30d3e5c577b from=translated src=- shape=d2a223dd vocab=c154be75
-/
theorem BinaryOpenCoverSquareSubdivision.rightAnchoredGridRowFramesAt_horizontal_edges
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (p : ℕ) (hp : p < D.steps) (i : Fin D.steps) :
    let F := D.rightAnchoredGridRowFramesAt hxU hxV hUV hU hV p hp i
    rebaseEdge F.bottomLeft F.bottomRight
        (Monoid.PushoutI.of (D.label i ⟨p, hp⟩)
          (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i ⟨p, hp⟩ 0)) = 1 ∧
      rebaseEdge F.topLeft F.topRight
        (Monoid.PushoutI.of (D.label i ⟨p, hp⟩)
          (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i ⟨p, hp⟩ 1)) = 1 := by
  cases p with
  | zero =>
      exact D.rightAnchoredRowFrames_horizontal_edges hxU hxV hUV hU hV
        ⟨0, hp⟩ 1 i
  | succ p =>
      exact D.rightAnchoredRowFrames_horizontal_edges hxU hxV hUV hU hV
        ⟨p + 1, hp⟩ _ i

/-- 二维右锚定递归的每一行最右真实竖边都严格归一化为单位元。
@isnad1 id=other.6h7v.s11.0c6a4f0d8824 from=translated src=- shape=0da5a0e7 vocab=2dc5c17e
-/
theorem BinaryOpenCoverSquareSubdivision.rightAnchoredGridRowFramesAt_right_edge_eq_one
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (p : ℕ) (hp : p < D.steps) :
    let last : Fin D.steps :=
      ⟨D.steps - 1, Nat.sub_lt D.steps_pos Nat.zero_lt_one⟩
    let F := D.rightAnchoredGridRowFramesAt hxU hxV hUV hU hV p hp last
    rebaseEdge F.bottomRight F.topRight
      (Monoid.PushoutI.of (D.label last ⟨p, hp⟩)
        (D.gridCellBasedVerticalEdgeInPiece hxU hxV hU hV last ⟨p, hp⟩ 1)) = 1 := by
  cases p with
  | zero =>
      exact D.rightAnchoredRowFrames_right_edge_eq_one hxU hxV hUV hU hV
        ⟨0, hp⟩ 1
  | succ p =>
      exact D.rightAnchoredRowFrames_right_edge_eq_one hxU hxV hUV hU hV
        ⟨p + 1, hp⟩ _

/-- The left edge exposed by a right-anchored full-row state is the actual
leftmost vertical cell edge, rebased by the frames at the first column.  This
is the public projection theorem for downstream users of a completed row; they
do not need to unfold the prefix recursion used to construct that row.
@isnad1 id=other.6h7v.s12.d8ad241a0154 from=translated src=- shape=41858b66 vocab=8c253633
-/
theorem BinaryOpenCoverSquareSubdivision.rightAnchoredGridFullRow_leftEdge_eq_leftmost
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (p : ℕ) (hp : p < D.steps) :
    let frames := D.rightAnchoredGridRowFramesAt hxU hxV hUV hU hV p hp
    let compat := D.rightAnchoredGridRowFramesAt_compatible
      hxU hxV hUV hU hV p hp
    (D.framedHorizontalFullRowState hxU hxV hUV hU hV
        ⟨p, hp⟩ frames compat).leftEdge =
      rebaseEdge (frames ⟨0, D.steps_pos⟩).bottomLeft
        (frames ⟨0, D.steps_pos⟩).topLeft
        (Monoid.PushoutI.of (D.label ⟨0, D.steps_pos⟩ ⟨p, hp⟩)
          (D.gridCellBasedVerticalEdgeInPiece hxU hxV hU hV
            ⟨0, D.steps_pos⟩ ⟨p, hp⟩ 0)) := by
  exact D.framedHorizontalFullRowState_leftEdge
    hxU hxV hUV hU hV ⟨p, hp⟩
    (D.rightAnchoredGridRowFramesAt hxU hxV hUV hU hV p hp)
    (D.rightAnchoredGridRowFramesAt_compatible hxU hxV hUV hU hV p hp)

/-- 二维右锚定网格的每一整行左侧真实竖边也严格归一化为单位元。-/
private theorem BinaryOpenCoverSquareSubdivision.rightAnchoredGridFullRow_leftEdge_eq_one
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (p : ℕ) (hp : p < D.steps) :
    let frames := D.rightAnchoredGridRowFramesAt hxU hxV hUV hU hV p hp
    let compat := D.rightAnchoredGridRowFramesAt_compatible
      hxU hxV hUV hU hV p hp
    let S := D.framedHorizontalFullRowState hxU hxV hUV hU hV
      ⟨p, hp⟩ frames compat
    S.leftEdge = 1 := by
  let frames := D.rightAnchoredGridRowFramesAt hxU hxV hUV hU hV p hp
  let compat := D.rightAnchoredGridRowFramesAt_compatible
    hxU hxV hUV hU hV p hp
  let S := D.framedHorizontalFullRowState hxU hxV hUV hU hV
    ⟨p, hp⟩ frames compat
  have hlr := D.framedFullRow_leftEdge_eq_rightEdge hxU hxV hUV hU hV
    ⟨p, hp⟩ frames compat
    (D.rightAnchoredGridRowFramesAt_horizontal_edges hxU hxV hUV hU hV p hp)
  have hright := D.rightAnchoredGridRowFramesAt_right_edge_eq_one
    hxU hxV hUV hU hV p hp
  change S.leftEdge = S.boundary.focus at hlr
  change rebaseEdge
      (frames ⟨D.steps - 1, Nat.sub_lt D.steps_pos Nat.zero_lt_one⟩).bottomRight
      (frames ⟨D.steps - 1, Nat.sub_lt D.steps_pos Nat.zero_lt_one⟩).topRight
      (Monoid.PushoutI.of
        (D.label ⟨D.steps - 1, Nat.sub_lt D.steps_pos Nat.zero_lt_one⟩ ⟨p, hp⟩)
        (D.gridCellBasedVerticalEdgeInPiece hxU hxV hU hV
          ⟨D.steps - 1, Nat.sub_lt D.steps_pos Nat.zero_lt_one⟩ ⟨p, hp⟩ 1)) = 1
    at hright
  exact hlr.trans (S.focus_eq.trans hright)

/-- 从底行到第 `p` 行，按右锚定二维 frame 状态累积左外侧竖边词。-/
noncomputable def BinaryOpenCoverSquareSubdivision.rightAnchoredGridLeftBoundaryWordAt
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V) :
    (p : ℕ) → (hp : p < D.steps) → binaryVanKampenPushout U V hxU hxV
  | 0, hp =>
      let frames := D.rightAnchoredGridRowFramesAt hxU hxV hUV hU hV 0 hp
      let compat := D.rightAnchoredGridRowFramesAt_compatible
        hxU hxV hUV hU hV 0 hp
      (D.framedHorizontalFullRowState hxU hxV hUV hU hV
        ⟨0, hp⟩ frames compat).leftEdge
  | p + 1, hp =>
      let hp' : p < D.steps := Nat.lt_trans (Nat.lt_succ_self p) hp
      let frames := D.rightAnchoredGridRowFramesAt hxU hxV hUV hU hV (p + 1) hp
      let compat := D.rightAnchoredGridRowFramesAt_compatible
        hxU hxV hUV hU hV (p + 1) hp
      (D.framedHorizontalFullRowState hxU hxV hUV hU hV
        ⟨p + 1, hp⟩ frames compat).leftEdge *
        D.rightAnchoredGridLeftBoundaryWordAt hxU hxV hUV hU hV p hp'

/-- The recursive left-boundary word is the reverse edge-chain product of the
full-row left edges from row zero through row `p`.-/
private theorem BinaryOpenCoverSquareSubdivision.rightAnchoredGridLeftBoundaryWordAt_eq_reverseRows
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V) :
    ∀ (p : ℕ) (hp : p < D.steps),
      D.rightAnchoredGridLeftBoundaryWordAt hxU hxV hUV hU hV p hp =
        reverseEdgeChainProduct (List.ofFn fun r : Fin (p + 1) =>
          let hr : r.val < D.steps :=
            lt_of_le_of_lt (Nat.le_of_lt_succ r.isLt) hp
          let frames := D.rightAnchoredGridRowFramesAt
            hxU hxV hUV hU hV r.val hr
          let compat := D.rightAnchoredGridRowFramesAt_compatible
            hxU hxV hUV hU hV r.val hr
          (1, (D.framedHorizontalFullRowState hxU hxV hUV hU hV
            ⟨r.val, hr⟩ frames compat).leftEdge)) := by
  intro p
  induction p with
  | zero =>
      intro hp
      rw [BinaryOpenCoverSquareSubdivision.rightAnchoredGridLeftBoundaryWordAt]
      simp only [List.ofFn_succ, List.ofFn_zero, reverseEdgeChainProduct]
      simp
  | succ p ih =>
      intro hp
      have hp' : p < D.steps := Nat.lt_trans (Nat.lt_succ_self p) hp
      rw [BinaryOpenCoverSquareSubdivision.rightAnchoredGridLeftBoundaryWordAt]
      rw [List.ofFn_succ', List.concat_eq_append,
        reverseEdgeChainProduct_append]
      simp only [reverseEdgeChainProduct]
      rw [ih hp']
      congr 1
      simp

/-- Full-height specialization of the preceding row enumeration, indexed
directly by `Fin D.steps`.
@isnad1 id=eq.5h6v.s10.5fd9991fc0a2 from=translated src=- shape=6d6ce0bd vocab=e0cbbd63
-/
theorem BinaryOpenCoverSquareSubdivision.rightAnchoredGridFullLeftBoundary_eq_reverseRows
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V) :
    D.rightAnchoredGridLeftBoundaryWordAt hxU hxV hUV hU hV
        (D.steps - 1) (Nat.sub_lt D.steps_pos Nat.zero_lt_one) =
      reverseEdgeChainProduct (List.ofFn fun r : Fin D.steps =>
        let frames := D.rightAnchoredGridRowFramesAt
          hxU hxV hUV hU hV r.val r.isLt
        let compat := D.rightAnchoredGridRowFramesAt_compatible
          hxU hxV hUV hU hV r.val r.isLt
        (1, (D.framedHorizontalFullRowState hxU hxV hUV hU hV
          r frames compat).leftEdge)) := by
  have hlen : D.steps - 1 + 1 = D.steps :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt D.steps_pos))
  have h := D.rightAnchoredGridLeftBoundaryWordAt_eq_reverseRows
    hxU hxV hUV hU hV (D.steps - 1)
      (Nat.sub_lt D.steps_pos Nat.zero_lt_one)
  rw [h]
  apply congrArg reverseEdgeChainProduct
  rw [List.ofFn_congr hlen]
  apply congrArg List.ofFn
  funext r
  congr

/-- 右锚定二维网格任意高度前缀的完整左边界 holonomy 都严格等于单位元。-/
private theorem BinaryOpenCoverSquareSubdivision.rightAnchoredGridLeftBoundaryWordAt_eq_one
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V) :
    ∀ (p : ℕ) (hp : p < D.steps),
      D.rightAnchoredGridLeftBoundaryWordAt hxU hxV hUV hU hV p hp = 1
  | 0, hp =>
      D.rightAnchoredGridFullRow_leftEdge_eq_one hxU hxV hUV hU hV 0 hp
  | p + 1, hp => by
      have hp' : p < D.steps := Nat.lt_trans (Nat.lt_succ_self p) hp
      rw [BinaryOpenCoverSquareSubdivision.rightAnchoredGridLeftBoundaryWordAt,
        D.rightAnchoredGridFullRow_leftEdge_eq_one hxU hxV hUV hU hV (p + 1) hp,
        D.rightAnchoredGridLeftBoundaryWordAt_eq_one hxU hxV hUV hU hV p hp']
      exact one_mul 1

/-- 整张有限方格在右锚定二维 frame 下的左边界 holonomy 为单位元。
@isnad1 id=eq.5h6v.s8.caa3bdca5ec4 from=translated src=- shape=5e096210 vocab=4f70158b
-/
theorem BinaryOpenCoverSquareSubdivision.rightAnchoredGridFullLeftBoundary_eq_one
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V) :
    D.rightAnchoredGridLeftBoundaryWordAt hxU hxV hUV hU hV
      (D.steps - 1) (Nat.sub_lt D.steps_pos Nat.zero_lt_one) = 1 :=
  D.rightAnchoredGridLeftBoundaryWordAt_eq_one hxU hxV hUV hU hV
    (D.steps - 1) (Nat.sub_lt D.steps_pos Nat.zero_lt_one)

end SandronesLibrary.Topology
