/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.VanKampenLeftBoundaryCocycle

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# van Kampen 左边界 combined frames 与网格 potentials

本文件把逐边 cell-to-letter transitions 与二维右锚定 cell frames 合成，证明它们在同一 block 内相邻
细边及相邻 block 的全局网格索引处严格相容；同时把四个方向的统一内部边 transitions 刻画为标准
grid-cell potentials，并记录 block 首末 letter connectors 送回环境空间后的端点公式。

本文件不证明跨 block transition cocycle，不执行有限 telescope，也不证明 kernel 平凡、规范同态
单射或最终 van Kampen 同构。

当前条目：`topology.fundamental-group.van-kampen-combined-frames`。
-/

open Set
open scoped unitInterval

noncomputable section

namespace SandronesLibrary.Topology

variable {X : Type*} [TopologicalSpace X]

/-- 相邻细边的逐边 transitions 与二维右锚定 cell frames 合成后，在共享顶点严格相容。

> **Entry**: topology.fundamental-group.van-kampen-combined-frames
@isnad1 id=other.6h10v.s10.0a2984fa75cf from=translated src=- shape=20cd1a9a vocab=e337a8df
-/
theorem PathConcatAlignedSquareSubdivision.combinedLeftBoundaryFrames_adjacent
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (Fhom : Path.Homotopy
      (binaryVanKampenLetterConcatLoop hxU hxV letters) (Path.refl x₀))
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V
      letters.reverse.length)
    (i : Fin letters.reverse.length)
    (s t : Fin (pathConcatSegmentGridLength letters.reverse.length A.factor i))
    (hshared : s.succ = t.castSucc) :
    let col : Fin A.subdivision.steps := ⟨0, A.subdivision.steps_pos⟩
    let lower := A.segmentGridEdgeIndex i s
    let upper := A.segmentGridEdgeIndex i t
    let lowerT := A.leftBoundaryCellToLetterTransitions
      hxU hxV hUV hU hV letters Fhom i s
    let upperT := A.leftBoundaryCellToLetterTransitions
      hxU hxV hUV hU hV letters Fhom i t
    let lowerF := A.subdivision.rightAnchoredGridRowFramesAt
      hxU hxV hUV hU hV lower.val lower.isLt col
    let upperF := A.subdivision.rightAnchoredGridRowFramesAt
      hxU hxV hUV hU hV upper.val upper.isLt col
    lowerT.endChange * lowerF.topLeft =
      upperT.startChange * upperF.bottomLeft := by
  dsimp only
  let col : Fin A.subdivision.steps := ⟨0, A.subdivision.steps_pos⟩
  let lower := A.segmentGridEdgeIndex i s
  let upper := A.segmentGridEdgeIndex i t
  let hrows : lower.succ = upper.castSucc :=
    A.segmentGridEdgeIndex_succ_eq_castSucc i s t hshared
  have hval : lower.val + 1 = upper.val := congrArg Fin.val hrows
  have hp : lower.val + 1 < A.subdivision.steps := by
    rw [hval]
    exact upper.isLt
  let vertical := A.subdivision.verticalInternalEdgeTransitions
    hxU hxV hUV hU hV col lower upper hrows
  let lowerT := A.leftBoundaryCellToLetterTransitions
    hxU hxV hUV hU hV letters Fhom i s
  let upperT := A.leftBoundaryCellToLetterTransitions
    hxU hxV hUV hU hV letters Fhom i t
  let lowerF := A.subdivision.rightAnchoredGridRowFramesAt
    hxU hxV hUV hU hV lower.val lower.isLt col
  let upperF := A.subdivision.rightAnchoredGridRowFramesAt
    hxU hxV hUV hU hV upper.val upper.isLt col
  have htransition := A.leftBoundaryCellToLetterTransitions_adjacent
    hxU hxV hUV hU hV letters Fhom i s t hshared
  have hf := A.subdivision.rightAnchoredGridRowFramesAt_vertical_compatible
    hxU hxV hUV hU hV lower.val hp col
  have hleft := hf.left
  have hframe : upperF.bottomLeft = vertical.startChange * lowerF.topLeft := by
    simpa [vertical, lowerF, upperF, hval] using hleft
  calc
    lowerT.endChange * lowerF.topLeft =
        (upperT.startChange * vertical.startChange) * lowerF.topLeft := by
      rw [htransition]
    _ = upperT.startChange * (vertical.startChange * lowerF.topLeft) := by
      rw [mul_assoc]
    _ = upperT.startChange * upperF.bottomLeft := by rw [← hframe]

/-- 相邻 concat blocks 的最后一条与第一条细网格边在全局网格中严格相邻。
@isnad1 id=other.2h4v.s7.611aa18b427e from=translated src=- shape=17e4c746 vocab=939e7440
-/
theorem pathConcatSegmentGridEdgeIndex_block_adjacent
    (n k : ℕ) (hk : 0 < k) (i j : Fin n)
    (hshared : i.succ = j.castSucc) :
    let Li := pathConcatSegmentGridLength n k i
    let hi := pathConcatSegmentGridLength_pos n k hk i
    let hj := pathConcatSegmentGridLength_pos n k hk j
    (pathConcatSegmentGridEdgeIndex n k i (finLastOfPos Li hi)).succ =
      (pathConcatSegmentGridEdgeIndex n k j ⟨0, hj⟩).castSucc := by
  dsimp only
  let Li := pathConcatSegmentGridLength n k i
  let hi := pathConcatSegmentGridLength_pos n k hk i
  let hj := pathConcatSegmentGridLength_pos n k hk j
  let si := finLastOfPos Li hi
  have hsi : si.succ = Fin.last Li := by
    apply Fin.ext
    simp [si, finLastOfPos]
    omega
  calc
    (pathConcatSegmentGridEdgeIndex n k i si).succ =
        pathConcatSegmentGridIndex n k i si.succ :=
      pathConcatSegmentGridEdgeIndex_succ n k i si
    _ = pathConcatSegmentGridIndex n k i (Fin.last Li) := by rw [hsi]
    _ = pathConcatBreakpointGridIndex n k i.succ :=
      pathConcatSegmentGridIndex_last n k i
    _ = pathConcatBreakpointGridIndex n k j.castSucc := by rw [hshared]
    _ = pathConcatSegmentGridIndex n k j 0 :=
      (pathConcatSegmentGridIndex_zero n k j).symm
    _ = (pathConcatSegmentGridEdgeIndex n k j ⟨0, hj⟩).castSucc :=
      (pathConcatSegmentGridEdgeIndex_castSucc n k j ⟨0, hj⟩).symm

/-- 上一全局索引关系 transport 到 concat 对齐方形细分的真实行索引。
@isnad1 id=other.1h8v.s7.dd14c667fb49 from=translated src=- shape=68c34577 vocab=39af8f7b
-/
theorem PathConcatAlignedSquareSubdivision.segmentGridEdgeIndex_block_adjacent
    {H : C(unitInterval × unitInterval, X)} {U V : Set X} {n : ℕ}
    (A : PathConcatAlignedSquareSubdivision H U V n) (i j : Fin n)
    (hshared : i.succ = j.castSucc) :
    let Li := pathConcatSegmentGridLength n A.factor i
    let hi := pathConcatSegmentGridLength_pos n A.factor A.factor_pos i
    let hj := pathConcatSegmentGridLength_pos n A.factor A.factor_pos j
    (A.segmentGridEdgeIndex i (finLastOfPos Li hi)).succ =
      (A.segmentGridEdgeIndex j ⟨0, hj⟩).castSucc := by
  dsimp only
  apply Fin.ext
  unfold PathConcatAlignedSquareSubdivision.segmentGridEdgeIndex
  simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_cast]
  exact congrArg Fin.val
    (pathConcatSegmentGridEdgeIndex_block_adjacent
      n A.factor A.factor_pos i j hshared)

/-- 相邻 concat blocks 的二维右锚定 frames 在共享断点处满足同一 vertical transition 关系。
@isnad1 id=other.6h9v.s10.9d171738ec93 from=translated src=- shape=238c1a53 vocab=dfd81d29
-/
theorem PathConcatAlignedSquareSubdivision.rightAnchoredBlockFrames_adjacent
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (Fhom : Path.Homotopy
      (binaryVanKampenLetterConcatLoop hxU hxV letters) (Path.refl x₀))
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V
      letters.reverse.length)
    (i j : Fin letters.reverse.length) (hshared : i.succ = j.castSucc) :
    let Li := pathConcatSegmentGridLength letters.reverse.length A.factor i
    let hi := pathConcatSegmentGridLength_pos letters.reverse.length A.factor
      A.factor_pos i
    let hj := pathConcatSegmentGridLength_pos letters.reverse.length A.factor
      A.factor_pos j
    let col : Fin A.subdivision.steps := ⟨0, A.subdivision.steps_pos⟩
    let lower := A.segmentGridEdgeIndex i (finLastOfPos Li hi)
    let upper := A.segmentGridEdgeIndex j ⟨0, hj⟩
    let vertical := A.subdivision.verticalInternalEdgeTransitions
      hxU hxV hUV hU hV col lower upper
        (A.segmentGridEdgeIndex_block_adjacent i j hshared)
    let lowerF := A.subdivision.rightAnchoredGridRowFramesAt
      hxU hxV hUV hU hV lower.val lower.isLt col
    let upperF := A.subdivision.rightAnchoredGridRowFramesAt
      hxU hxV hUV hU hV upper.val upper.isLt col
    upperF.bottomLeft = vertical.startChange * lowerF.topLeft := by
  dsimp only
  let Li := pathConcatSegmentGridLength letters.reverse.length A.factor i
  let hi := pathConcatSegmentGridLength_pos letters.reverse.length A.factor
    A.factor_pos i
  let hj := pathConcatSegmentGridLength_pos letters.reverse.length A.factor
    A.factor_pos j
  let col : Fin A.subdivision.steps := ⟨0, A.subdivision.steps_pos⟩
  let lower := A.segmentGridEdgeIndex i (finLastOfPos Li hi)
  let upper := A.segmentGridEdgeIndex j ⟨0, hj⟩
  let hrows : lower.succ = upper.castSucc :=
    A.segmentGridEdgeIndex_block_adjacent i j hshared
  have hval : lower.val + 1 = upper.val := congrArg Fin.val hrows
  have hp : lower.val + 1 < A.subdivision.steps := by
    rw [hval]
    exact upper.isLt
  let vertical := A.subdivision.verticalInternalEdgeTransitions
    hxU hxV hUV hU hV col lower upper hrows
  let lowerF := A.subdivision.rightAnchoredGridRowFramesAt
    hxU hxV hUV hU hV lower.val lower.isLt col
  let upperF := A.subdivision.rightAnchoredGridRowFramesAt
    hxU hxV hUV hU hV upper.val upper.isLt col
  have hf := A.subdivision.rightAnchoredGridRowFramesAt_vertical_compatible
    hxU hxV hUV hU hV lower.val hp col
  have hleft := hf.left
  simpa [vertical, lowerF, upperF, hval] using hleft

namespace BinaryOpenCoverSquareSubdivision

/-- 异标签竖直公共边的起点 transition，严格是下、上两格 comparison potentials 的比值。
该公式冻结 `verticalSwitchEdgeTransitions` 中容易混淆的非交换乘法方向。-/
private theorem verticalSwitchEdgeTransitions_start_eq_comparisonPotentials
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (hswitch : D.label i j ≠ D.label i l) :
    let CB := D.verticalSwitchBottomConnectorComparison
      hxU hxV hUV hU hV i j l hshared hswitch
    let CT := D.verticalSwitchTopConnectorComparison
      hxU hxV hUV hU hV i j l hshared hswitch
    let T := D.verticalSwitchEdgeTransitions
      hxU hxV hUV hU hV i j l hshared hswitch
    T.startChange = transitionFromPotentials
      ((Monoid.PushoutI.of (D.label i j) CB.startChange :
        binaryVanKampenPushout U V hxU hxV)⁻¹)
      ((Monoid.PushoutI.of (D.label i l) CT.startChange :
        binaryVanKampenPushout U V hxU hxV)⁻¹) := by
  simp [BinaryOpenCoverSquareSubdivision.verticalSwitchEdgeTransitions,
    transitionFromPotentials]

/-- 竖直同标签公共边的实际右端版本：任意交集点分别识别为下格右上角与上格右下角时，
transition 是两格标准 grid-cell potentials 的比值。-/
private theorem verticalCommonEdgeTransitions_end_eq_gridCellPotentials
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (hlabel : D.label i j = D.label i l) (z : ↥(U ∩ V))
    (hzBottom : binaryOpenCoverIntersectionToPiece U V (D.label i j) z =
      D.gridCellVertexInPiece i j 1 1)
    (hzTop : binaryOpenCoverIntersectionToPiece U V (D.label i l) z =
      D.gridCellVertexInPiece i l 1 0) :
    let T := D.verticalCommonEdgeTransitions hxU hxV hU hV
      i j l hshared hlabel
    T.endChange = transitionFromPotentials
      (D.gridCellVertexPotentialFromIntersection
        hxU hxV hUV hU hV z i j 1 1 hzBottom)
      (D.gridCellVertexPotentialFromIntersection
        hxU hxV hUV hU hV z i l 1 0 hzTop) := by
  let C := D.verticalCommonEdgeConnectorComparison hxU hxV hU hV
    i j l hshared hlabel
  let f := (Monoid.PushoutI.of
    (φ := binaryOpenCoverIntersectionMaps U V hxU hxV) (D.label i j) :
    FundamentalGroup (binaryOpenCoverPiece U V (D.label i j))
      (binaryOpenCoverBasepoint hxU hxV (D.label i j)) →*
      binaryVanKampenPushout U V hxU hxV)
  have hzTop' : binaryOpenCoverIntersectionToPiece U V (D.label i j) z =
      D.gridCellVertexInPieceOfLabel i l 1 0 (D.label i j) hlabel.symm := by
    apply Subtype.ext
    rw [coe_binaryOpenCoverIntersectionToPiece,
      D.coe_gridCellVertexInPieceOfLabel]
    simpa only [coe_binaryOpenCoverIntersectionToPiece] using
      congrArg Subtype.val hzTop
  have href : C.edgeTarget =
      binaryOpenCoverIntersectionToPiece U V (D.label i j) z :=
    (D.verticalCommonEdge_target_eq_bottom i j l hshared hlabel).trans
      hzBottom.symm
  let reference :=
    (binaryOpenCoverIntersectionConnectorInPiece hxU hxV hUV (D.label i j) z).cast
      (binaryOpenCoverBasepoint_eq_intersectionToPiece hxU hxV (D.label i j)) href
  change (f C.endChange)⁻¹ = _
  rw [C.map_endChange_inv_eq_potentials f reference]
  congr 1
  · unfold BinaryOpenCoverSquareSubdivision.gridCellVertexPotentialFromIntersection
    change f (connectorChange reference C.leftEnd) =
      f (connectorChange
        ((binaryOpenCoverIntersectionConnectorInPiece hxU hxV hUV
          (D.label i j) z).cast
            (binaryOpenCoverBasepoint_eq_intersectionToPiece hxU hxV (D.label i j))
            hzBottom.symm)
        (D.gridCellVertexConnectorInPiece hxU hxV hU hV i j 1 1))
    apply congrArg f
    rw [show C.leftEnd =
      (D.gridCellVertexConnectorInPiece hxU hxV hU hV i j 1 1).cast rfl
        (D.verticalCommonEdge_target_eq_bottom i j l hshared hlabel) by rfl]
    exact connectorChange_cast_four_endpoints_right _ _
      (binaryOpenCoverBasepoint_eq_intersectionToPiece hxU hxV (D.label i j))
      hzBottom href (D.verticalCommonEdge_target_eq_bottom i j l hshared hlabel)
  · let explicitTop := D.gridCellVertexPotentialFromIntersectionOfLabel
      hxU hxV hUV hU hV z i l 1 0 (D.label i j) hlabel.symm hzTop'
    have hactual := D.gridCellVertexPotentialFromIntersectionOfLabel_eq
      hxU hxV hUV hU hV z i l 1 0
      (D.label i j) (D.label i l) hlabel.symm rfl hzTop' hzTop
    calc
      f (connectorChange reference C.rightEnd) = explicitTop := by
        unfold explicitTop
        unfold BinaryOpenCoverSquareSubdivision.gridCellVertexPotentialFromIntersectionOfLabel
        apply congrArg f
        rw [show C.rightEnd =
          (D.gridCellVertexConnectorInPieceOfLabel hxU hxV hU hV
            i l 1 0 (D.label i j) hlabel.symm).cast rfl
              (D.verticalCommonEdge_target_eq_top
                i j l hshared hlabel) by rfl]
        exact connectorChange_cast_four_endpoints_right _ _
          (binaryOpenCoverBasepoint_eq_intersectionToPiece hxU hxV (D.label i j))
          hzTop' href (D.verticalCommonEdge_target_eq_top i j l hshared hlabel)
      _ = D.gridCellVertexPotentialFromIntersectionOfLabel hxU hxV hUV hU hV
          z i l 1 0 (D.label i l) rfl hzTop := hactual
      _ = D.gridCellVertexPotentialFromIntersection
          hxU hxV hUV hU hV z i l 1 0 hzTop := rfl

/-- 异标签竖直公共边下格的右端 comparison potential transport 到给定交集顶点后，是下格右上角的
标准 grid-cell potential。-/
private theorem verticalSwitchBottom_endPotential_eq_gridCellPotential
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (hswitch : D.label i j ≠ D.label i l) (z : ↥(U ∩ V))
    (hz : binaryOpenCoverIntersectionToPiece U V (D.label i j) z =
      D.gridCellVertexInPiece i j 1 1) :
    let C := D.verticalSwitchBottomConnectorComparison
      hxU hxV hUV hU hV i j l hshared hswitch
    ((Monoid.PushoutI.of (D.label i j) C.endChange :
      binaryVanKampenPushout U V hxU hxV)⁻¹) =
      D.gridCellVertexPotentialFromIntersection
        hxU hxV hUV hU hV z i j 1 1 hz := by
  dsimp only
  rw [D.verticalSwitchBottom_endPotential_eq_vertexPotential
    hxU hxV hUV hU hV i j l hshared hswitch,
    D.gridCellVertexPotentialFromIntersection_eq_vertexPotential]
  apply binaryOpenCoverVertexPotentialFromIntersection_cast
    hxU hxV hUV (D.label i j)
  · apply Subtype.ext
    have hs := congrArg Subtype.val
      (D.verticalSwitchEdge_bottom_target_eq i j l hshared hswitch)
    have hzval := congrArg Subtype.val hz
    simp only [coe_binaryOpenCoverIntersectionToPiece,
      D.coe_gridCellVertexInPieceOfLabel] at hs
    simp only [coe_binaryOpenCoverIntersectionToPiece] at hzval
    exact hs.trans hzval.symm
  · apply Path.ext
    funext u
    apply Subtype.ext
    rw [Path.cast_coe]
    rfl
  · apply Subtype.ext
    change ((binaryOpenCoverIntersectionToPiece U V (D.label i j)
      (⟨squareGridVertex H D.steps D.steps_pos i.succ j.succ, by
        simpa [squareGridVertex, Set.Icc.convexComb_one] using
          D.verticalSwitchEdge_mem_intersection i j l hshared hswitch 1⟩ :
        ↥(U ∩ V)) : binaryOpenCoverPiece U V (D.label i j)) : X) =
      (D.gridCellVertexInPiece i j 1 1 : X)
    have hs := congrArg Subtype.val
      (D.verticalSwitchEdge_bottom_target_eq i j l hshared hswitch)
    simpa only [coe_binaryOpenCoverIntersectionToPiece,
      D.coe_gridCellVertexInPieceOfLabel] using hs

/-- 上格右端的对称版本。-/
private theorem verticalSwitchTop_endPotential_eq_gridCellPotential
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (hswitch : D.label i j ≠ D.label i l) (z : ↥(U ∩ V))
    (hz : binaryOpenCoverIntersectionToPiece U V (D.label i l) z =
      D.gridCellVertexInPiece i l 1 0) :
    let C := D.verticalSwitchTopConnectorComparison
      hxU hxV hUV hU hV i j l hshared hswitch
    ((Monoid.PushoutI.of (D.label i l) C.endChange :
      binaryVanKampenPushout U V hxU hxV)⁻¹) =
      D.gridCellVertexPotentialFromIntersection
        hxU hxV hUV hU hV z i l 1 0 hz := by
  dsimp only
  rw [D.verticalSwitchTop_endPotential_eq_vertexPotential
    hxU hxV hUV hU hV i j l hshared hswitch,
    D.gridCellVertexPotentialFromIntersection_eq_vertexPotential]
  apply binaryOpenCoverVertexPotentialFromIntersection_cast
    hxU hxV hUV (D.label i l)
  · apply Subtype.ext
    have hs := congrArg Subtype.val
      (D.verticalSwitchEdge_top_target_eq i j l hshared hswitch)
    have hzval := congrArg Subtype.val hz
    simp only [coe_binaryOpenCoverIntersectionToPiece,
      D.coe_gridCellVertexInPieceOfLabel] at hs
    simp only [coe_binaryOpenCoverIntersectionToPiece] at hzval
    exact hs.trans hzval.symm
  · apply Path.ext
    funext u
    apply Subtype.ext
    rw [Path.cast_coe]
    rfl
  · apply Subtype.ext
    change ((binaryOpenCoverIntersectionToPiece U V (D.label i l)
      (⟨squareGridVertex H D.steps D.steps_pos i.succ j.succ, by
        simpa [squareGridVertex, Set.Icc.convexComb_one] using
          D.verticalSwitchEdge_mem_intersection i j l hshared hswitch 1⟩ :
        ↥(U ∩ V)) : binaryOpenCoverPiece U V (D.label i l)) : X) =
      (D.gridCellVertexInPiece i l 1 0 : X)
    have hs := congrArg Subtype.val
      (D.verticalSwitchEdge_top_target_eq i j l hshared hswitch)
    simpa only [coe_binaryOpenCoverIntersectionToPiece,
      D.coe_gridCellVertexInPieceOfLabel] using hs

/-- 只要共享右端点另知属于交集，真实竖直内部边的终点 transition 无论两格标签是否相同，都由
该交集点处下格右上角与上格右下角的标准 grid-cell potentials 给出。
@isnad1 id=other.8h10v.s9.a09583379cec from=translated src=- shape=9213f146 vocab=0df710fc
-/
theorem verticalInternalEdgeTransitions_end_eq_gridCellPotentials
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (z : ↥(U ∩ V))
    (hzBottom : binaryOpenCoverIntersectionToPiece U V (D.label i j) z =
      D.gridCellVertexInPiece i j 1 1)
    (hzTop : binaryOpenCoverIntersectionToPiece U V (D.label i l) z =
      D.gridCellVertexInPiece i l 1 0) :
    let T := D.verticalInternalEdgeTransitions
      hxU hxV hUV hU hV i j l hshared
    T.endChange = transitionFromPotentials
      (D.gridCellVertexPotentialFromIntersection
        hxU hxV hUV hU hV z i j 1 1 hzBottom)
      (D.gridCellVertexPotentialFromIntersection
        hxU hxV hUV hU hV z i l 1 0 hzTop) := by
  by_cases hlabel : D.label i j = D.label i l
  · rw [BinaryOpenCoverSquareSubdivision.verticalInternalEdgeTransitions,
      dite_eq_left hlabel]
    exact D.verticalCommonEdgeTransitions_end_eq_gridCellPotentials
      hxU hxV hUV hU hV i j l hshared hlabel z hzBottom hzTop
  · rw [BinaryOpenCoverSquareSubdivision.verticalInternalEdgeTransitions,
      dite_eq_right hlabel]
    dsimp only
    rw [D.verticalSwitchEdgeTransitions_end_potential
      hxU hxV hUV hU hV i j l hshared hlabel]
    rw [D.verticalSwitchBottom_endPotential_eq_gridCellPotential
        hxU hxV hUV hU hV i j l hshared hlabel z hzBottom,
      D.verticalSwitchTop_endPotential_eq_gridCellPotential
        hxU hxV hUV hU hV i j l hshared hlabel z hzTop]

/-- 水平同标签公共边的实际下端版本：任意交集点分别识别为左格右下角与右格左下角时，
transition 是两格标准 grid-cell potentials 的比值。-/
private theorem horizontalCommonEdgeTransitions_start_eq_gridCellPotentials
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (hlabel : D.label i j = D.label k j)
    (z : ↥(U ∩ V))
    (hzLeft : binaryOpenCoverIntersectionToPiece U V (D.label i j) z =
      D.gridCellVertexInPiece i j 1 0)
    (hzRight : binaryOpenCoverIntersectionToPiece U V (D.label k j) z =
      D.gridCellVertexInPiece k j 0 0) :
    let T := D.horizontalCommonEdgeTransitions hxU hxV hU hV
      i k j hshared hlabel
    T.startChange = transitionFromPotentials
      (D.gridCellVertexPotentialFromIntersection
        hxU hxV hUV hU hV z i j 1 0 hzLeft)
      (D.gridCellVertexPotentialFromIntersection
        hxU hxV hUV hU hV z k j 0 0 hzRight) := by
  let C := D.horizontalCommonEdgeConnectorComparison hxU hxV hU hV
    i k j hshared hlabel
  let f := (Monoid.PushoutI.of
    (φ := binaryOpenCoverIntersectionMaps U V hxU hxV) (D.label i j) :
    FundamentalGroup (binaryOpenCoverPiece U V (D.label i j))
      (binaryOpenCoverBasepoint hxU hxV (D.label i j)) →*
      binaryVanKampenPushout U V hxU hxV)
  have hzRight' : binaryOpenCoverIntersectionToPiece U V (D.label i j) z =
      D.gridCellVertexInPieceOfLabel k j 0 0 (D.label i j) hlabel.symm := by
    apply Subtype.ext
    rw [coe_binaryOpenCoverIntersectionToPiece,
      D.coe_gridCellVertexInPieceOfLabel]
    simpa only [coe_binaryOpenCoverIntersectionToPiece] using
      congrArg Subtype.val hzRight
  have href : C.edgeSource =
      binaryOpenCoverIntersectionToPiece U V (D.label i j) z :=
    (D.horizontalCommonEdge_source_eq_left i k j hshared hlabel).trans
      hzLeft.symm
  let reference :=
    (binaryOpenCoverIntersectionConnectorInPiece hxU hxV hUV (D.label i j) z).cast
      (binaryOpenCoverBasepoint_eq_intersectionToPiece hxU hxV (D.label i j)) href
  change (f C.startChange)⁻¹ = _
  rw [C.map_startChange_inv_eq_potentials f reference]
  congr 1
  · unfold BinaryOpenCoverSquareSubdivision.gridCellVertexPotentialFromIntersection
    change f (connectorChange reference C.leftStart) =
      f (connectorChange
        ((binaryOpenCoverIntersectionConnectorInPiece hxU hxV hUV
          (D.label i j) z).cast
            (binaryOpenCoverBasepoint_eq_intersectionToPiece hxU hxV (D.label i j))
            hzLeft.symm)
        (D.gridCellVertexConnectorInPiece hxU hxV hU hV i j 1 0))
    apply congrArg f
    rw [show C.leftStart =
      (D.gridCellVertexConnectorInPiece hxU hxV hU hV i j 1 0).cast rfl
        (D.horizontalCommonEdge_source_eq_left i k j hshared hlabel) by rfl]
    exact connectorChange_cast_four_endpoints_right _ _
      (binaryOpenCoverBasepoint_eq_intersectionToPiece hxU hxV (D.label i j))
      hzLeft href (D.horizontalCommonEdge_source_eq_left i k j hshared hlabel)
  · let explicitRight := D.gridCellVertexPotentialFromIntersectionOfLabel
      hxU hxV hUV hU hV z k j 0 0 (D.label i j) hlabel.symm hzRight'
    have hactual := D.gridCellVertexPotentialFromIntersectionOfLabel_eq
      hxU hxV hUV hU hV z k j 0 0
      (D.label i j) (D.label k j) hlabel.symm rfl hzRight' hzRight
    calc
      f (connectorChange reference C.rightStart) = explicitRight := by
        unfold explicitRight
        unfold BinaryOpenCoverSquareSubdivision.gridCellVertexPotentialFromIntersectionOfLabel
        apply congrArg f
        rw [show C.rightStart =
          (D.gridCellVertexConnectorInPieceOfLabel hxU hxV hU hV
            k j 0 0 (D.label i j) hlabel.symm).cast rfl
              (D.horizontalCommonEdge_source_eq_right
                i k j hshared hlabel) by rfl]
        exact connectorChange_cast_four_endpoints_right _ _
          (binaryOpenCoverBasepoint_eq_intersectionToPiece hxU hxV (D.label i j))
          hzRight' href (D.horizontalCommonEdge_source_eq_right i k j hshared hlabel)
      _ = D.gridCellVertexPotentialFromIntersectionOfLabel hxU hxV hUV hU hV
          z k j 0 0 (D.label k j) rfl hzRight := hactual
      _ = D.gridCellVertexPotentialFromIntersection
          hxU hxV hUV hU hV z k j 0 0 hzRight := rfl

/-- 异标签水平公共边的左格 comparison potential transport 到任意给定的共享交集下端点后，
就是左格右下角的标准 grid-cell potential。-/
private theorem horizontalSwitchLeft_startPotential_eq_gridCellPotential
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (hswitch : D.label i j ≠ D.label k j)
    (z : ↥(U ∩ V))
    (hz : binaryOpenCoverIntersectionToPiece U V (D.label i j) z =
      D.gridCellVertexInPiece i j 1 0) :
    let C := D.horizontalSwitchLeftConnectorComparison
      hxU hxV hUV hU hV i k j hshared hswitch
    ((Monoid.PushoutI.of (D.label i j) C.startChange :
      binaryVanKampenPushout U V hxU hxV)⁻¹) =
      D.gridCellVertexPotentialFromIntersection
        hxU hxV hUV hU hV z i j 1 0 hz := by
  dsimp only
  rw [D.horizontalSwitchLeft_startPotential_eq_vertexPotential
    hxU hxV hUV hU hV i k j hshared hswitch,
    D.gridCellVertexPotentialFromIntersection_eq_vertexPotential]
  apply binaryOpenCoverVertexPotentialFromIntersection_cast
    hxU hxV hUV (D.label i j)
  · apply Subtype.ext
    have hs := congrArg Subtype.val
      (D.horizontalSwitchEdge_left_source_eq i k j hshared hswitch)
    have hzval := congrArg Subtype.val hz
    simp only [coe_binaryOpenCoverIntersectionToPiece,
      D.coe_gridCellVertexInPieceOfLabel] at hs
    simp only [coe_binaryOpenCoverIntersectionToPiece] at hzval
    exact hs.trans hzval.symm
  · apply Path.ext
    funext u
    apply Subtype.ext
    rw [Path.cast_coe]
    rfl
  · apply Subtype.ext
    change ((binaryOpenCoverIntersectionToPiece U V (D.label i j)
      (⟨squareGridVertex H D.steps D.steps_pos i.succ j.castSucc, by
        simpa [squareGridVertex, Set.Icc.convexComb_zero] using
          D.horizontalSwitchEdge_mem_intersection i k j hshared hswitch 0⟩ :
        ↥(U ∩ V)) : binaryOpenCoverPiece U V (D.label i j)) : X) =
      (D.gridCellVertexInPiece i j 1 0 : X)
    have hs := congrArg Subtype.val
      (D.horizontalSwitchEdge_left_source_eq i k j hshared hswitch)
    simpa only [coe_binaryOpenCoverIntersectionToPiece,
      D.coe_gridCellVertexInPieceOfLabel] using hs

/-- 右格对称版本。-/
private theorem horizontalSwitchRight_startPotential_eq_gridCellPotential
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (hswitch : D.label i j ≠ D.label k j)
    (z : ↥(U ∩ V))
    (hz : binaryOpenCoverIntersectionToPiece U V (D.label k j) z =
      D.gridCellVertexInPiece k j 0 0) :
    let C := D.horizontalSwitchRightConnectorComparison
      hxU hxV hUV hU hV i k j hshared hswitch
    ((Monoid.PushoutI.of (D.label k j) C.startChange :
      binaryVanKampenPushout U V hxU hxV)⁻¹) =
      D.gridCellVertexPotentialFromIntersection
        hxU hxV hUV hU hV z k j 0 0 hz := by
  dsimp only
  rw [D.horizontalSwitchRight_startPotential_eq_vertexPotential
    hxU hxV hUV hU hV i k j hshared hswitch,
    D.gridCellVertexPotentialFromIntersection_eq_vertexPotential]
  apply binaryOpenCoverVertexPotentialFromIntersection_cast
    hxU hxV hUV (D.label k j)
  · apply Subtype.ext
    have hs := congrArg Subtype.val
      (D.horizontalSwitchEdge_right_source_eq i k j hshared hswitch)
    have hzval := congrArg Subtype.val hz
    simp only [coe_binaryOpenCoverIntersectionToPiece,
      D.coe_gridCellVertexInPieceOfLabel] at hs
    simp only [coe_binaryOpenCoverIntersectionToPiece] at hzval
    exact hs.trans hzval.symm
  · apply Path.ext
    funext u
    apply Subtype.ext
    rw [Path.cast_coe]
    rfl
  · apply Subtype.ext
    change ((binaryOpenCoverIntersectionToPiece U V (D.label k j)
      (⟨squareGridVertex H D.steps D.steps_pos i.succ j.castSucc, by
        simpa [squareGridVertex, Set.Icc.convexComb_zero] using
          D.horizontalSwitchEdge_mem_intersection i k j hshared hswitch 0⟩ :
        ↥(U ∩ V)) : binaryOpenCoverPiece U V (D.label k j)) : X) =
      (D.gridCellVertexInPiece k j 0 0 : X)
    have hs := congrArg Subtype.val
      (D.horizontalSwitchEdge_right_source_eq i k j hshared hswitch)
    simpa only [coe_binaryOpenCoverIntersectionToPiece,
      D.coe_gridCellVertexInPieceOfLabel] using hs

/-- 只要共享下端点另知属于交集，真实水平内部边的起点 transition 无论两格标签是否相同，都由
该交集点处左格右下角与右格左下角的标准 grid-cell potentials 给出。
@isnad1 id=other.8h10v.s9.dbe40ae22882 from=translated src=- shape=a4158cb6 vocab=88fa245f
-/
theorem horizontalInternalEdgeTransitions_start_eq_gridCellPotentials
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (z : ↥(U ∩ V))
    (hzLeft : binaryOpenCoverIntersectionToPiece U V (D.label i j) z =
      D.gridCellVertexInPiece i j 1 0)
    (hzRight : binaryOpenCoverIntersectionToPiece U V (D.label k j) z =
      D.gridCellVertexInPiece k j 0 0) :
    let T := D.horizontalInternalEdgeTransitions
      hxU hxV hUV hU hV i k j hshared
    T.startChange = transitionFromPotentials
      (D.gridCellVertexPotentialFromIntersection
        hxU hxV hUV hU hV z i j 1 0 hzLeft)
      (D.gridCellVertexPotentialFromIntersection
        hxU hxV hUV hU hV z k j 0 0 hzRight) := by
  by_cases hlabel : D.label i j = D.label k j
  · rw [BinaryOpenCoverSquareSubdivision.horizontalInternalEdgeTransitions,
      dite_eq_left hlabel]
    exact D.horizontalCommonEdgeTransitions_start_eq_gridCellPotentials
      hxU hxV hUV hU hV i k j hshared hlabel z hzLeft hzRight
  · rw [BinaryOpenCoverSquareSubdivision.horizontalInternalEdgeTransitions,
      dite_eq_right hlabel]
    dsimp only
    rw [D.horizontalSwitchEdgeTransitions_start_eq_comparisonPotentials
      hxU hxV hUV hU hV i k j hshared hlabel]
    rw [D.horizontalSwitchLeft_startPotential_eq_gridCellPotential
        hxU hxV hUV hU hV i k j hshared hlabel z hzLeft,
      D.horizontalSwitchRight_startPotential_eq_gridCellPotential
        hxU hxV hUV hU hV i k j hshared hlabel z hzRight]

/-- 水平同标签公共边的上端版本：任意交集点分别识别为左格右上角与右格左上角时，
transition 是两格标准 grid-cell potentials 的比值。-/
private theorem horizontalCommonEdgeTransitions_end_eq_gridCellPotentials
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (hlabel : D.label i j = D.label k j) (z : ↥(U ∩ V))
    (hzLeft : binaryOpenCoverIntersectionToPiece U V (D.label i j) z =
      D.gridCellVertexInPiece i j 1 1)
    (hzRight : binaryOpenCoverIntersectionToPiece U V (D.label k j) z =
      D.gridCellVertexInPiece k j 0 1) :
    let T := D.horizontalCommonEdgeTransitions hxU hxV hU hV
      i k j hshared hlabel
    T.endChange = transitionFromPotentials
      (D.gridCellVertexPotentialFromIntersection
        hxU hxV hUV hU hV z i j 1 1 hzLeft)
      (D.gridCellVertexPotentialFromIntersection
        hxU hxV hUV hU hV z k j 0 1 hzRight) := by
  let C := D.horizontalCommonEdgeConnectorComparison hxU hxV hU hV
    i k j hshared hlabel
  let f := (Monoid.PushoutI.of
    (φ := binaryOpenCoverIntersectionMaps U V hxU hxV) (D.label i j) :
    FundamentalGroup (binaryOpenCoverPiece U V (D.label i j))
      (binaryOpenCoverBasepoint hxU hxV (D.label i j)) →*
      binaryVanKampenPushout U V hxU hxV)
  have hzRight' : binaryOpenCoverIntersectionToPiece U V (D.label i j) z =
      D.gridCellVertexInPieceOfLabel k j 0 1 (D.label i j) hlabel.symm := by
    apply Subtype.ext
    rw [coe_binaryOpenCoverIntersectionToPiece,
      D.coe_gridCellVertexInPieceOfLabel]
    simpa only [coe_binaryOpenCoverIntersectionToPiece] using
      congrArg Subtype.val hzRight
  have href : C.edgeTarget =
      binaryOpenCoverIntersectionToPiece U V (D.label i j) z :=
    (D.horizontalCommonEdge_target_eq_left i k j hshared hlabel).trans
      hzLeft.symm
  let reference :=
    (binaryOpenCoverIntersectionConnectorInPiece hxU hxV hUV (D.label i j) z).cast
      (binaryOpenCoverBasepoint_eq_intersectionToPiece hxU hxV (D.label i j)) href
  change (f C.endChange)⁻¹ = _
  rw [C.map_endChange_inv_eq_potentials f reference]
  congr 1
  · unfold BinaryOpenCoverSquareSubdivision.gridCellVertexPotentialFromIntersection
    change f (connectorChange reference C.leftEnd) =
      f (connectorChange
        ((binaryOpenCoverIntersectionConnectorInPiece hxU hxV hUV
          (D.label i j) z).cast
            (binaryOpenCoverBasepoint_eq_intersectionToPiece hxU hxV (D.label i j))
            hzLeft.symm)
        (D.gridCellVertexConnectorInPiece hxU hxV hU hV i j 1 1))
    apply congrArg f
    rw [show C.leftEnd =
      (D.gridCellVertexConnectorInPiece hxU hxV hU hV i j 1 1).cast rfl
        (D.horizontalCommonEdge_target_eq_left i k j hshared hlabel) by rfl]
    exact connectorChange_cast_four_endpoints_right _ _
      (binaryOpenCoverBasepoint_eq_intersectionToPiece hxU hxV (D.label i j))
      hzLeft href (D.horizontalCommonEdge_target_eq_left i k j hshared hlabel)
  · let explicitRight := D.gridCellVertexPotentialFromIntersectionOfLabel
      hxU hxV hUV hU hV z k j 0 1 (D.label i j) hlabel.symm hzRight'
    have hactual := D.gridCellVertexPotentialFromIntersectionOfLabel_eq
      hxU hxV hUV hU hV z k j 0 1
      (D.label i j) (D.label k j) hlabel.symm rfl hzRight' hzRight
    calc
      f (connectorChange reference C.rightEnd) = explicitRight := by
        unfold explicitRight
        unfold BinaryOpenCoverSquareSubdivision.gridCellVertexPotentialFromIntersectionOfLabel
        apply congrArg f
        rw [show C.rightEnd =
          (D.gridCellVertexConnectorInPieceOfLabel hxU hxV hU hV
            k j 0 1 (D.label i j) hlabel.symm).cast rfl
              (D.horizontalCommonEdge_target_eq_right
                i k j hshared hlabel) by rfl]
        exact connectorChange_cast_four_endpoints_right _ _
          (binaryOpenCoverBasepoint_eq_intersectionToPiece hxU hxV (D.label i j))
          hzRight' href (D.horizontalCommonEdge_target_eq_right i k j hshared hlabel)
      _ = D.gridCellVertexPotentialFromIntersectionOfLabel hxU hxV hUV hU hV
          z k j 0 1 (D.label k j) rfl hzRight := hactual
      _ = D.gridCellVertexPotentialFromIntersection
          hxU hxV hUV hU hV z k j 0 1 hzRight := rfl

/-- 异标签水平公共边左格的上端 comparison potential transport 到给定交集顶点后，是左格右上角的
标准 grid-cell potential。-/
private theorem horizontalSwitchLeft_endPotential_eq_gridCellPotential
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (hswitch : D.label i j ≠ D.label k j) (z : ↥(U ∩ V))
    (hz : binaryOpenCoverIntersectionToPiece U V (D.label i j) z =
      D.gridCellVertexInPiece i j 1 1) :
    let C := D.horizontalSwitchLeftConnectorComparison
      hxU hxV hUV hU hV i k j hshared hswitch
    ((Monoid.PushoutI.of (D.label i j) C.endChange :
      binaryVanKampenPushout U V hxU hxV)⁻¹) =
      D.gridCellVertexPotentialFromIntersection
        hxU hxV hUV hU hV z i j 1 1 hz := by
  dsimp only
  rw [D.horizontalSwitchLeft_endPotential_eq_vertexPotential
    hxU hxV hUV hU hV i k j hshared hswitch,
    D.gridCellVertexPotentialFromIntersection_eq_vertexPotential]
  apply binaryOpenCoverVertexPotentialFromIntersection_cast
    hxU hxV hUV (D.label i j)
  · apply Subtype.ext
    have hs := congrArg Subtype.val
      (D.horizontalSwitchEdge_left_target_eq i k j hshared hswitch)
    have hzval := congrArg Subtype.val hz
    simp only [coe_binaryOpenCoverIntersectionToPiece,
      D.coe_gridCellVertexInPieceOfLabel] at hs
    simp only [coe_binaryOpenCoverIntersectionToPiece] at hzval
    exact hs.trans hzval.symm
  · apply Path.ext
    funext u
    apply Subtype.ext
    rw [Path.cast_coe]
    rfl
  · apply Subtype.ext
    change ((binaryOpenCoverIntersectionToPiece U V (D.label i j)
      (⟨squareGridVertex H D.steps D.steps_pos i.succ j.succ, by
        simpa [squareGridVertex, Set.Icc.convexComb_one] using
          D.horizontalSwitchEdge_mem_intersection i k j hshared hswitch 1⟩ :
        ↥(U ∩ V)) : binaryOpenCoverPiece U V (D.label i j)) : X) =
      (D.gridCellVertexInPiece i j 1 1 : X)
    have hs := congrArg Subtype.val
      (D.horizontalSwitchEdge_left_target_eq i k j hshared hswitch)
    simpa only [coe_binaryOpenCoverIntersectionToPiece,
      D.coe_gridCellVertexInPieceOfLabel] using hs

/-- 右格上端的对称版本。-/
private theorem horizontalSwitchRight_endPotential_eq_gridCellPotential
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (hswitch : D.label i j ≠ D.label k j) (z : ↥(U ∩ V))
    (hz : binaryOpenCoverIntersectionToPiece U V (D.label k j) z =
      D.gridCellVertexInPiece k j 0 1) :
    let C := D.horizontalSwitchRightConnectorComparison
      hxU hxV hUV hU hV i k j hshared hswitch
    ((Monoid.PushoutI.of (D.label k j) C.endChange :
      binaryVanKampenPushout U V hxU hxV)⁻¹) =
      D.gridCellVertexPotentialFromIntersection
        hxU hxV hUV hU hV z k j 0 1 hz := by
  dsimp only
  rw [D.horizontalSwitchRight_endPotential_eq_vertexPotential
    hxU hxV hUV hU hV i k j hshared hswitch,
    D.gridCellVertexPotentialFromIntersection_eq_vertexPotential]
  apply binaryOpenCoverVertexPotentialFromIntersection_cast
    hxU hxV hUV (D.label k j)
  · apply Subtype.ext
    have hs := congrArg Subtype.val
      (D.horizontalSwitchEdge_right_target_eq i k j hshared hswitch)
    have hzval := congrArg Subtype.val hz
    simp only [coe_binaryOpenCoverIntersectionToPiece,
      D.coe_gridCellVertexInPieceOfLabel] at hs
    simp only [coe_binaryOpenCoverIntersectionToPiece] at hzval
    exact hs.trans hzval.symm
  · apply Path.ext
    funext u
    apply Subtype.ext
    rw [Path.cast_coe]
    rfl
  · apply Subtype.ext
    change ((binaryOpenCoverIntersectionToPiece U V (D.label k j)
      (⟨squareGridVertex H D.steps D.steps_pos i.succ j.succ, by
        simpa [squareGridVertex, Set.Icc.convexComb_one] using
          D.horizontalSwitchEdge_mem_intersection i k j hshared hswitch 1⟩ :
        ↥(U ∩ V)) : binaryOpenCoverPiece U V (D.label k j)) : X) =
      (D.gridCellVertexInPiece k j 0 1 : X)
    have hs := congrArg Subtype.val
      (D.horizontalSwitchEdge_right_target_eq i k j hshared hswitch)
    simpa only [coe_binaryOpenCoverIntersectionToPiece,
      D.coe_gridCellVertexInPieceOfLabel] using hs

/-- 只要共享上端点另知属于交集，真实水平内部边的终点 transition 无论两格标签是否相同，都由
该交集点处左格右上角与右格左上角的标准 grid-cell potentials 给出。
@isnad1 id=other.8h10v.s9.418f16b32745 from=translated src=- shape=a4158cb6 vocab=b9438a0d
-/
theorem horizontalInternalEdgeTransitions_end_eq_gridCellPotentials
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (z : ↥(U ∩ V))
    (hzLeft : binaryOpenCoverIntersectionToPiece U V (D.label i j) z =
      D.gridCellVertexInPiece i j 1 1)
    (hzRight : binaryOpenCoverIntersectionToPiece U V (D.label k j) z =
      D.gridCellVertexInPiece k j 0 1) :
    let T := D.horizontalInternalEdgeTransitions
      hxU hxV hUV hU hV i k j hshared
    T.endChange = transitionFromPotentials
      (D.gridCellVertexPotentialFromIntersection
        hxU hxV hUV hU hV z i j 1 1 hzLeft)
      (D.gridCellVertexPotentialFromIntersection
        hxU hxV hUV hU hV z k j 0 1 hzRight) := by
  by_cases hlabel : D.label i j = D.label k j
  · rw [BinaryOpenCoverSquareSubdivision.horizontalInternalEdgeTransitions,
      dite_eq_left hlabel]
    exact D.horizontalCommonEdgeTransitions_end_eq_gridCellPotentials
      hxU hxV hUV hU hV i k j hshared hlabel z hzLeft hzRight
  · rw [BinaryOpenCoverSquareSubdivision.horizontalInternalEdgeTransitions,
      dite_eq_right hlabel]
    dsimp only
    rw [D.horizontalSwitchEdgeTransitions_end_eq_comparisonPotentials
      hxU hxV hUV hU hV i k j hshared hlabel]
    rw [D.horizontalSwitchLeft_endPotential_eq_gridCellPotential
        hxU hxV hUV hU hV i k j hshared hlabel z hzLeft,
      D.horizontalSwitchRight_endPotential_eq_gridCellPotential
        hxU hxV hUV hU hV i k j hshared hlabel z hzRight]

/-- 异标签竖直公共边的下格 comparison potential，transport 到任意给定的共享交集左端点后，
就是下格左上角的标准 grid-cell potential。-/
private theorem verticalSwitchBottom_startPotential_eq_gridCellPotential
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (hswitch : D.label i j ≠ D.label i l)
    (z : ↥(U ∩ V))
    (hz : binaryOpenCoverIntersectionToPiece U V (D.label i j) z =
      D.gridCellVertexInPiece i j 0 1) :
    let C := D.verticalSwitchBottomConnectorComparison
      hxU hxV hUV hU hV i j l hshared hswitch
    ((Monoid.PushoutI.of (D.label i j) C.startChange :
      binaryVanKampenPushout U V hxU hxV)⁻¹) =
      D.gridCellVertexPotentialFromIntersection
        hxU hxV hUV hU hV z i j 0 1 hz := by
  dsimp only
  rw [D.verticalSwitchBottom_startPotential_eq_vertexPotential
    hxU hxV hUV hU hV i j l hshared hswitch,
    D.gridCellVertexPotentialFromIntersection_eq_vertexPotential]
  apply binaryOpenCoverVertexPotentialFromIntersection_cast
    hxU hxV hUV (D.label i j)
  · apply Subtype.ext
    have hs := congrArg Subtype.val
      (D.verticalSwitchEdge_bottom_source_eq i j l hshared hswitch)
    have hzval := congrArg Subtype.val hz
    simp only [coe_binaryOpenCoverIntersectionToPiece,
      D.coe_gridCellVertexInPieceOfLabel] at hs
    simp only [coe_binaryOpenCoverIntersectionToPiece] at hzval
    exact hs.trans hzval.symm
  · apply Path.ext
    funext u
    apply Subtype.ext
    rw [Path.cast_coe]
    rfl
  · apply Subtype.ext
    change ((binaryOpenCoverIntersectionToPiece U V (D.label i j)
      (⟨squareGridVertex H D.steps D.steps_pos i.castSucc j.succ, by
        simpa [squareGridVertex, Set.Icc.convexComb_zero] using
          D.verticalSwitchEdge_mem_intersection i j l hshared hswitch 0⟩ :
        ↥(U ∩ V)) : binaryOpenCoverPiece U V (D.label i j)) : X) =
      (D.gridCellVertexInPiece i j 0 1 : X)
    have hs := congrArg Subtype.val
      (D.verticalSwitchEdge_bottom_source_eq i j l hshared hswitch)
    simpa only [coe_binaryOpenCoverIntersectionToPiece,
      D.coe_gridCellVertexInPieceOfLabel] using hs

/-- 上格对称版本：异标签竖直公共边的上格 comparison potential transport 到给定共享交集左端点
后，就是上格左下角的标准 grid-cell potential。-/
private theorem verticalSwitchTop_startPotential_eq_gridCellPotential
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (hswitch : D.label i j ≠ D.label i l)
    (z : ↥(U ∩ V))
    (hz : binaryOpenCoverIntersectionToPiece U V (D.label i l) z =
      D.gridCellVertexInPiece i l 0 0) :
    let C := D.verticalSwitchTopConnectorComparison
      hxU hxV hUV hU hV i j l hshared hswitch
    ((Monoid.PushoutI.of (D.label i l) C.startChange :
      binaryVanKampenPushout U V hxU hxV)⁻¹) =
      D.gridCellVertexPotentialFromIntersection
        hxU hxV hUV hU hV z i l 0 0 hz := by
  dsimp only
  rw [D.verticalSwitchTop_startPotential_eq_vertexPotential
    hxU hxV hUV hU hV i j l hshared hswitch,
    D.gridCellVertexPotentialFromIntersection_eq_vertexPotential]
  apply binaryOpenCoverVertexPotentialFromIntersection_cast
    hxU hxV hUV (D.label i l)
  · apply Subtype.ext
    have hs := congrArg Subtype.val
      (D.verticalSwitchEdge_top_source_eq i j l hshared hswitch)
    have hzval := congrArg Subtype.val hz
    simp only [coe_binaryOpenCoverIntersectionToPiece,
      D.coe_gridCellVertexInPieceOfLabel] at hs
    simp only [coe_binaryOpenCoverIntersectionToPiece] at hzval
    exact hs.trans hzval.symm
  · apply Path.ext
    funext u
    apply Subtype.ext
    rw [Path.cast_coe]
    rfl
  · apply Subtype.ext
    change ((binaryOpenCoverIntersectionToPiece U V (D.label i l)
      (⟨squareGridVertex H D.steps D.steps_pos i.castSucc j.succ, by
        simpa [squareGridVertex, Set.Icc.convexComb_zero] using
          D.verticalSwitchEdge_mem_intersection i j l hshared hswitch 0⟩ :
        ↥(U ∩ V)) : binaryOpenCoverPiece U V (D.label i l)) : X) =
      (D.gridCellVertexInPiece i l 0 0 : X)
    have hs := congrArg Subtype.val
      (D.verticalSwitchEdge_top_source_eq i j l hshared hswitch)
    simpa only [coe_binaryOpenCoverIntersectionToPiece,
      D.coe_gridCellVertexInPieceOfLabel] using hs

/-- 只要共享左端点另知属于交集，真实竖直内部边的起点 transition 无论两格标签是否相同，都由
该交集点处下格左上角与上格左下角的标准 grid-cell potentials 给出。
@isnad1 id=other.8h10v.s9.4e4d655cb9e5 from=translated src=- shape=9213f146 vocab=751cd9e9
-/
theorem verticalInternalEdgeTransitions_start_eq_gridCellPotentials
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (z : ↥(U ∩ V))
    (hzBottom : binaryOpenCoverIntersectionToPiece U V (D.label i j) z =
      D.gridCellVertexInPiece i j 0 1)
    (hzTop : binaryOpenCoverIntersectionToPiece U V (D.label i l) z =
      D.gridCellVertexInPiece i l 0 0) :
    let T := D.verticalInternalEdgeTransitions
      hxU hxV hUV hU hV i j l hshared
    T.startChange = transitionFromPotentials
      (D.gridCellVertexPotentialFromIntersection
        hxU hxV hUV hU hV z i j 0 1 hzBottom)
      (D.gridCellVertexPotentialFromIntersection
        hxU hxV hUV hU hV z i l 0 0 hzTop) := by
  by_cases hlabel : D.label i j = D.label i l
  · rw [BinaryOpenCoverSquareSubdivision.verticalInternalEdgeTransitions,
      dite_eq_left hlabel]
    exact D.verticalCommonEdgeTransitions_start_eq_gridCellPotentials
      hxU hxV hUV hU hV i j l hshared hlabel z hzBottom hzTop
  · rw [BinaryOpenCoverSquareSubdivision.verticalInternalEdgeTransitions,
      dite_eq_right hlabel]
    dsimp only
    rw [D.verticalSwitchEdgeTransitions_start_eq_comparisonPotentials
      hxU hxV hUV hU hV i j l hshared hlabel]
    rw [D.verticalSwitchBottom_startPotential_eq_gridCellPotential
        hxU hxV hUV hU hV i j l hshared hlabel z hzBottom,
      D.verticalSwitchTop_startPotential_eq_gridCellPotential
        hxU hxV hUV hU hV i j l hshared hlabel z hzTop]

end BinaryOpenCoverSquareSubdivision

/-- 一个 letter block 的最后一条细边所用 letter 终点 connector，送回环境空间后是公共基点常值
道路。
@isnad1 id=other.4h9v.s10.1b82ef2642dc from=translated src=- shape=9bb80d8b vocab=10116104
-/
@[simp] theorem PathConcatAlignedSquareSubdivision.coe_leftBoundaryBlockLastLetterEnd
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (Fhom : Path.Homotopy
      (binaryVanKampenLetterConcatLoop hxU hxV letters) (Path.refl x₀))
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V
      letters.reverse.length)
    (i : Fin letters.reverse.length) (u : unitInterval) :
    let L := pathConcatSegmentGridLength letters.reverse.length A.factor i
    let hL := pathConcatSegmentGridLength_pos letters.reverse.length A.factor
      A.factor_pos i
    ((A.leftBoundaryAlignedGridEdgeLetterEnd
      hxU hxV hU hV letters Fhom i (finLastOfPos L hL)) u : X) = x₀ := by
  dsimp only
  let L := pathConcatSegmentGridLength letters.reverse.length A.factor i
  let hL := pathConcatSegmentGridLength_pos letters.reverse.length A.factor
    A.factor_pos i
  let s := finLastOfPos L hL
  have hs : s.succ = Fin.last L := by
    apply Fin.ext
    simp [s, finLastOfPos]
    omega
  unfold PathConcatAlignedSquareSubdivision.leftBoundaryAlignedGridEdgeLetterEnd
  rw [Path.cast_coe, hs, binaryVanKampenLetterBlockGridConnector_last,
    Path.cast_coe]
  cases h : (letters.reverse.get i).1 <;> rfl

/-- 一个 letter block 的第一条细边所用 letter 起点 connector，送回环境空间后同样是公共基点
常值道路。
@isnad1 id=other.4h9v.s10.b695247af4b3 from=translated src=- shape=057d6d60 vocab=ee8c11c8
-/
@[simp] theorem PathConcatAlignedSquareSubdivision.coe_leftBoundaryBlockFirstLetterStart
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (Fhom : Path.Homotopy
      (binaryVanKampenLetterConcatLoop hxU hxV letters) (Path.refl x₀))
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V
      letters.reverse.length)
    (j : Fin letters.reverse.length) (u : unitInterval) :
    let hL := pathConcatSegmentGridLength_pos letters.reverse.length A.factor
      A.factor_pos j
    ((A.leftBoundaryAlignedGridEdgeLetterStart
      hxU hxV hU hV letters Fhom j ⟨0, hL⟩) u : X) = x₀ := by
  dsimp only
  have hz : (⟨0, pathConcatSegmentGridLength_pos letters.reverse.length A.factor
      A.factor_pos j⟩ : Fin
        (pathConcatSegmentGridLength letters.reverse.length A.factor j)).castSucc =
      (0 : Fin (pathConcatSegmentGridLength letters.reverse.length A.factor j + 1)) := rfl
  unfold PathConcatAlignedSquareSubdivision.leftBoundaryAlignedGridEdgeLetterStart
  rw [Path.cast_coe, hz, binaryVanKampenLetterBlockGridConnector_zero,
    Path.cast_coe]
  cases h : (letters.reverse.get j).1 <;> rfl

end SandronesLibrary.Topology
