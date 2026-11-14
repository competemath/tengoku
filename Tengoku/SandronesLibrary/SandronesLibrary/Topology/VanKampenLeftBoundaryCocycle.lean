/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.VanKampenLeftBoundaryTransport

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# van Kampen 左边界相邻细边的 transition cocycle

本文件证明同一 letter block 内相邻两条真实左边界细边的 cell-to-letter endpoint transitions，与
两格之间的真实竖直公共边 transition 满足共享顶点 cocycle。证明完整处理上下 cell 标签与固定
letter 标签之间的四种相等／不等分支，最终只公开统一的相邻性公式。

本文件不建立跨 letter block 的接缝相容，不构造 combined frames，不执行有限 telescope，也不证明
kernel 平凡、规范同态单射或最终 van Kampen 同构。

当前条目：`topology.fundamental-group.van-kampen-left-boundary-cocycle`。
-/

open Set
open scoped unitInterval

noncomputable section

namespace SandronesLibrary.Topology

variable {X : Type*} [TopologicalSpace X]

/-- 先做内层 connector 变化、再做外层 frame 变化，等于一次使用端点 frame 乘积的 rebase。

> **Entry**: topology.fundamental-group.van-kampen-left-boundary-cocycle-/
theorem rebaseEdge_rebaseEdge
    {G : Type*} [Group G]
    (outerStart outerEnd innerStart innerEnd edge : G) :
    rebaseEdge outerStart outerEnd
        (rebaseEdge innerStart innerEnd edge) =
      rebaseEdge (innerStart * outerStart) (innerEnd * outerEnd) edge := by
  simp [rebaseEdge, mul_assoc]

/-- 若逐边标签变化在共享顶点满足 cocycle，并且二维 cell frames 沿真实公共横边竖直相容，
则两者相乘得到的组合 frames 也在该顶点严格相容。-/
theorem combinedVertexFrames_compatible
    {G : Type*} [Group G]
    (vertical lowerToTarget upperToTarget : EdgeTransitions G)
    (lower upper : CellVertexFrames G)
    (hFrames : VerticalCellFramesCompatible vertical lower upper)
    (hTransitions : lowerToTarget.endChange =
      upperToTarget.startChange * vertical.startChange) :
    lowerToTarget.endChange * lower.topLeft =
      upperToTarget.startChange * upper.bottomLeft := by
  rw [hFrames.left, hTransitions, mul_assoc]

/-- 三组 edge transitions 若分别由“下 cell → target”、“上 cell → target”和
“下 cell → 上 cell”的同一套 vertex potentials 给出，则它们自动满足共享顶点 cocycle。-/
theorem edgeTransitions_cocycle_of_potentials
    {G : Type*} [Group G]
    (lowerPotential upperPotential targetPotential : G)
    (lowerToTarget upperToTarget vertical : EdgeTransitions G)
    (hlower : lowerToTarget.endChange =
      transitionFromPotentials lowerPotential targetPotential)
    (hupper : upperToTarget.startChange =
      transitionFromPotentials upperPotential targetPotential)
    (hvertical : vertical.startChange =
      transitionFromPotentials lowerPotential upperPotential) :
    lowerToTarget.endChange =
      upperToTarget.startChange * vertical.startChange := by
  rw [hlower, hupper, hvertical, transitionFromPotentials_mul]

namespace PathConcatAlignedSquareSubdivision

/-- 相邻左边界细边的两个 cell 标签相同、但都不同于固定 letter 标签时，逐边
cell-to-letter transitions 与真实竖直公共边 transition 满足共享顶点 cocycle。-/
private theorem leftBoundaryCellToLetterTransitions_adjacent_of_common_ne
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
    (hshared : s.succ = t.castSucc)
    (hs : A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
      (A.segmentGridEdgeIndex i s) ≠ (letters.reverse.get i).1)
    (ht : A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
      (A.segmentGridEdgeIndex i t) ≠ (letters.reverse.get i).1)
    (hlabel : A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
      (A.segmentGridEdgeIndex i s) =
      A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
        (A.segmentGridEdgeIndex i t)) :
    let col : Fin A.subdivision.steps := ⟨0, A.subdivision.steps_pos⟩
    let lower := A.segmentGridEdgeIndex i s
    let upper := A.segmentGridEdgeIndex i t
    let hrows : lower.succ = upper.castSucc :=
      A.segmentGridEdgeIndex_succ_eq_castSucc i s t hshared
    let lowerT := A.leftBoundaryCellToLetterTransitions
      hxU hxV hUV hU hV letters Fhom i s
    let upperT := A.leftBoundaryCellToLetterTransitions
      hxU hxV hUV hU hV letters Fhom i t
    let verticalT := A.subdivision.verticalCommonEdgeTransitions
      hxU hxV hU hV col lower upper hrows hlabel
    lowerT.endChange = upperT.startChange * verticalT.startChange := by
  dsimp only
  let qs := A.leftBoundaryAlignedGridEdge hxU hxV letters Fhom i s
  let qt := A.leftBoundaryAlignedGridEdge hxU hxV letters Fhom i t
  let hbs := A.leftBoundaryAlignedGridEdge_mem_cellPiece
    hxU hxV letters Fhom i s
  let hbt := A.leftBoundaryAlignedGridEdge_mem_cellPiece
    hxU hxV letters Fhom i t
  let hcs := A.leftBoundaryAlignedGridEdge_mem_letterPiece
    hxU hxV letters Fhom i s
  let hct := A.leftBoundaryAlignedGridEdge_mem_letterPiece
    hxU hxV letters Fhom i t
  let CBs := binaryOpenCoverDualPathConnectorComparison hxU hxV hUV
    qs hbs hcs hs hbs
    (A.leftBoundaryAlignedGridEdgeCellStart
      hxU hxV hU hV letters Fhom i s)
    (A.leftBoundaryAlignedGridEdgeCellEnd
      hxU hxV hU hV letters Fhom i s)
  let CCs := binaryOpenCoverDualPathConnectorComparison hxU hxV hUV
    qs hbs hcs hs hcs
    (A.leftBoundaryAlignedGridEdgeLetterStart
      hxU hxV hU hV letters Fhom i s)
    (A.leftBoundaryAlignedGridEdgeLetterEnd
      hxU hxV hU hV letters Fhom i s)
  let CBt := binaryOpenCoverDualPathConnectorComparison hxU hxV hUV
    qt hbt hct ht hbt
    (A.leftBoundaryAlignedGridEdgeCellStart
      hxU hxV hU hV letters Fhom i t)
    (A.leftBoundaryAlignedGridEdgeCellEnd
      hxU hxV hU hV letters Fhom i t)
  let CCt := binaryOpenCoverDualPathConnectorComparison hxU hxV hUV
    qt hbt hct ht hct
    (A.leftBoundaryAlignedGridEdgeLetterStart
      hxU hxV hU hV letters Fhom i t)
    (A.leftBoundaryAlignedGridEdgeLetterEnd
      hxU hxV hU hV letters Fhom i t)
  let lowerPotential : binaryVanKampenPushout U V hxU hxV :=
    (Monoid.PushoutI.of
      (A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
        (A.segmentGridEdgeIndex i s)) CBs.endChange)⁻¹
  let upperPotential : binaryVanKampenPushout U V hxU hxV :=
    (Monoid.PushoutI.of
      (A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
        (A.segmentGridEdgeIndex i t)) CBt.startChange)⁻¹
  let targetPotential : binaryVanKampenPushout U V hxU hxV :=
    (Monoid.PushoutI.of (letters.reverse.get i).1 CCs.endChange)⁻¹
  apply edgeTransitions_cocycle_of_potentials
    lowerPotential upperPotential targetPotential
  · exact A.leftBoundaryCellToLetterTransitions_end_potential_of_ne
      hxU hxV hUV hU hV letters Fhom i s hs
  · rw [A.leftBoundaryCellToLetterTransitions_start_potential_of_ne
      hxU hxV hUV hU hV letters Fhom i t ht]
    unfold targetPotential
    congr 1
    exact (A.leftBoundaryDualLetterPotential_adjacent
      hxU hxV hUV hU hV letters Fhom i s t hshared hs ht).symm
  · let col : Fin A.subdivision.steps := ⟨0, A.subdivision.steps_pos⟩
    let lower := A.segmentGridEdgeIndex i s
    let upper := A.segmentGridEdgeIndex i t
    let hrows : lower.succ = upper.castSucc :=
      A.segmentGridEdgeIndex_succ_eq_castSucc i s t hshared
    let z : ↥(U ∩ V) :=
      ⟨squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
          A.subdivision.steps_pos 0 lower.succ,
        mem_intersection_of_mem_binaryOpenCoverPieces_of_ne
          (by simpa using hbs 1) (by simpa using hcs 1) hs⟩
    let hzBottom : binaryOpenCoverIntersectionToPiece U V
        (A.subdivision.label col lower) z =
      A.subdivision.gridCellVertexInPiece col lower 0 1 := by
      calc
        binaryOpenCoverIntersectionToPiece U V
            (A.subdivision.label col lower) z =
            (⟨squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
                A.subdivision.steps_pos 0 lower.succ,
              by simpa using hbs 1⟩ :
              binaryOpenCoverPiece U V (A.subdivision.label col lower)) := by
                apply Subtype.ext
                rw [coe_binaryOpenCoverIntersectionToPiece]
        _ = A.subdivision.gridCellVertexInPiece col lower 0 1 :=
          A.leftBoundaryAlignedGridEdge_cellTarget_eq
            hxU hxV letters Fhom i s
    let hzTop : binaryOpenCoverIntersectionToPiece U V
        (A.subdivision.label col upper) z =
      A.subdivision.gridCellVertexInPiece col upper 0 0 := by
      calc
        binaryOpenCoverIntersectionToPiece U V
            (A.subdivision.label col upper) z =
            (⟨squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
                A.subdivision.steps_pos 0 upper.castSucc,
              by simpa using hbt 0⟩ :
              binaryOpenCoverPiece U V (A.subdivision.label col upper)) := by
                apply Subtype.ext
                rw [coe_binaryOpenCoverIntersectionToPiece]
                exact A.leftBoundary_segmentGridEdgeIndex_shared_vertex
                  i s t hshared
        _ = A.subdivision.gridCellVertexInPiece col upper 0 0 :=
          A.leftBoundaryAlignedGridEdge_cellSource_eq
            hxU hxV letters Fhom i t
    rw [A.subdivision.verticalCommonEdgeTransitions_start_eq_gridCellPotentials
      hxU hxV hUV hU hV col lower upper hrows hlabel z hzBottom hzTop]
    unfold lowerPotential upperPotential
    rw [A.leftBoundaryDualCellEndPotential_eq_gridCellPotential
      hxU hxV hUV hU hV letters Fhom i s hs]
    rw [A.leftBoundaryDualCellStartPotential_at_sharedVertex
      hxU hxV hUV hU hV letters Fhom i s t hshared ht]

/-- 混合 switch 分支所需的端点规范化：下方同标签 comparison 的终点与竖直切换边左端相同。-/
private theorem leftBoundarySameComparisonTarget_eq_switchSource
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
    (hshared : s.succ = t.castSucc)
    (hs : A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
      (A.segmentGridEdgeIndex i s) = (letters.reverse.get i).1)
    (ht : A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
      (A.segmentGridEdgeIndex i t) ≠ (letters.reverse.get i).1) :
    let col : Fin A.subdivision.steps := ⟨0, A.subdivision.steps_pos⟩
    let lower := A.segmentGridEdgeIndex i s
    let upper := A.segmentGridEdgeIndex i t
    let hrows : lower.succ = upper.castSucc :=
      A.segmentGridEdgeIndex_succ_eq_castSucc i s t hshared
    let hswitch : A.subdivision.label col lower ≠
        A.subdivision.label col upper := by
      intro h
      exact ht (h.symm.trans hs)
    let Csame := binaryOpenCoverSamePathConnectorComparison hxU hxV
      (A.leftBoundaryAlignedGridEdge hxU hxV letters Fhom i s)
      (A.leftBoundaryAlignedGridEdge_mem_cellPiece hxU hxV letters Fhom i s)
      (A.leftBoundaryAlignedGridEdge_mem_letterPiece hxU hxV letters Fhom i s)
      hs
      (A.leftBoundaryAlignedGridEdgeCellStart
        hxU hxV hU hV letters Fhom i s)
      (A.leftBoundaryAlignedGridEdgeCellEnd
        hxU hxV hU hV letters Fhom i s)
      (A.leftBoundaryAlignedGridEdgeLetterStart
        hxU hxV hU hV letters Fhom i s)
      (A.leftBoundaryAlignedGridEdgeLetterEnd
        hxU hxV hU hV letters Fhom i s)
    let Cbottom := A.subdivision.verticalSwitchBottomConnectorComparison
      hxU hxV hUV hU hV col lower upper hrows hswitch
    Csame.edgeTarget = Cbottom.edgeSource := by
  dsimp only
  rw [binaryOpenCoverSamePathConnectorComparison_edgeTarget]
  apply Subtype.ext
  unfold BinaryOpenCoverSquareSubdivision.verticalSwitchBottomConnectorComparison
  dsimp only [CommonEdgeConnectorComparison.edgeSource]
  rw [coe_binaryOpenCoverIntersectionToPiece]
  rfl

/-- 混合 switch 的下同上异分支中，下方逐边 transition 在共享交集顶点处由其 cell／letter 两套
connector potentials 给出。-/
private theorem leftBoundarySameTransitionEnd_eq_switchVertexPotentials
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
    (hshared : s.succ = t.castSucc)
    (hs : A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
      (A.segmentGridEdgeIndex i s) = (letters.reverse.get i).1)
    (ht : A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
      (A.segmentGridEdgeIndex i t) ≠ (letters.reverse.get i).1) :
    let col : Fin A.subdivision.steps := ⟨0, A.subdivision.steps_pos⟩
    let lower := A.segmentGridEdgeIndex i s
    let upper := A.segmentGridEdgeIndex i t
    let hrows : lower.succ = upper.castSucc :=
      A.segmentGridEdgeIndex_succ_eq_castSucc i s t hshared
    let hswitch : A.subdivision.label col lower ≠
        A.subdivision.label col upper := by
      intro h
      exact ht (h.symm.trans hs)
    let Csame := binaryOpenCoverSamePathConnectorComparison hxU hxV
      (A.leftBoundaryAlignedGridEdge hxU hxV letters Fhom i s)
      (A.leftBoundaryAlignedGridEdge_mem_cellPiece hxU hxV letters Fhom i s)
      (A.leftBoundaryAlignedGridEdge_mem_letterPiece hxU hxV letters Fhom i s)
      hs
      (A.leftBoundaryAlignedGridEdgeCellStart
        hxU hxV hU hV letters Fhom i s)
      (A.leftBoundaryAlignedGridEdgeCellEnd
        hxU hxV hU hV letters Fhom i s)
      (A.leftBoundaryAlignedGridEdgeLetterStart
        hxU hxV hU hV letters Fhom i s)
      (A.leftBoundaryAlignedGridEdgeLetterEnd
        hxU hxV hU hV letters Fhom i s)
    let z : ↥(U ∩ V) :=
      ⟨squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
          A.subdivision.steps_pos col.castSucc lower.succ, by
        simpa [squareGridVertex, Set.Icc.convexComb_zero] using
          A.subdivision.verticalSwitchEdge_mem_intersection
            col lower upper hrows hswitch 0⟩
    let hz : binaryOpenCoverIntersectionToPiece U V
        (A.subdivision.label col lower) z = Csame.edgeTarget :=
      (A.leftBoundarySameComparisonTarget_eq_switchSource
        hxU hxV hUV hU hV letters Fhom i s t hshared hs ht).symm
    let T := A.leftBoundaryCellToLetterTransitions
      hxU hxV hUV hU hV letters Fhom i s
    T.endChange = transitionFromPotentials
      (binaryOpenCoverVertexPotentialFromIntersection
        hxU hxV hUV z (A.subdivision.label col lower)
        Csame.edgeTarget Csame.leftEnd hz)
      (binaryOpenCoverVertexPotentialFromIntersection
        hxU hxV hUV z (A.subdivision.label col lower)
        Csame.edgeTarget Csame.rightEnd hz) := by
  dsimp only
  rw [PathConcatAlignedSquareSubdivision.leftBoundaryCellToLetterTransitions,
    dite_eq_left hs]
  exact (binaryOpenCoverSamePathConnectorComparison hxU hxV
    (A.leftBoundaryAlignedGridEdge hxU hxV letters Fhom i s)
    (A.leftBoundaryAlignedGridEdge_mem_cellPiece hxU hxV letters Fhom i s)
    (A.leftBoundaryAlignedGridEdge_mem_letterPiece hxU hxV letters Fhom i s)
    hs
    (A.leftBoundaryAlignedGridEdgeCellStart
      hxU hxV hU hV letters Fhom i s)
    (A.leftBoundaryAlignedGridEdgeCellEnd
      hxU hxV hU hV letters Fhom i s)
    (A.leftBoundaryAlignedGridEdgeLetterStart
      hxU hxV hU hV letters Fhom i s)
    (A.leftBoundaryAlignedGridEdgeLetterEnd
      hxU hxV hU hV letters Fhom i s)).pushout_endChange_inv_eq_vertexPotentials
        hxU hxV hUV
        (A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
          (A.segmentGridEdgeIndex i s)) _ _

/-- 上一定理中的下方 cell potential，正是真实竖直 switch comparison 的下格起点 potential。-/
private theorem leftBoundarySameCellEndPotential_eq_switchBottom
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
    (hshared : s.succ = t.castSucc)
    (hs : A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
      (A.segmentGridEdgeIndex i s) = (letters.reverse.get i).1)
    (ht : A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
      (A.segmentGridEdgeIndex i t) ≠ (letters.reverse.get i).1) :
    let col : Fin A.subdivision.steps := ⟨0, A.subdivision.steps_pos⟩
    let lower := A.segmentGridEdgeIndex i s
    let upper := A.segmentGridEdgeIndex i t
    let hrows : lower.succ = upper.castSucc :=
      A.segmentGridEdgeIndex_succ_eq_castSucc i s t hshared
    let hswitch : A.subdivision.label col lower ≠
        A.subdivision.label col upper := by
      intro h
      exact ht (h.symm.trans hs)
    let Csame := binaryOpenCoverSamePathConnectorComparison hxU hxV
      (A.leftBoundaryAlignedGridEdge hxU hxV letters Fhom i s)
      (A.leftBoundaryAlignedGridEdge_mem_cellPiece hxU hxV letters Fhom i s)
      (A.leftBoundaryAlignedGridEdge_mem_letterPiece hxU hxV letters Fhom i s)
      hs
      (A.leftBoundaryAlignedGridEdgeCellStart
        hxU hxV hU hV letters Fhom i s)
      (A.leftBoundaryAlignedGridEdgeCellEnd
        hxU hxV hU hV letters Fhom i s)
      (A.leftBoundaryAlignedGridEdgeLetterStart
        hxU hxV hU hV letters Fhom i s)
      (A.leftBoundaryAlignedGridEdgeLetterEnd
        hxU hxV hU hV letters Fhom i s)
    let Cbottom := A.subdivision.verticalSwitchBottomConnectorComparison
      hxU hxV hUV hU hV col lower upper hrows hswitch
    let z : ↥(U ∩ V) :=
      ⟨squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
          A.subdivision.steps_pos col.castSucc lower.succ, by
        simpa [squareGridVertex, Set.Icc.convexComb_zero] using
          A.subdivision.verticalSwitchEdge_mem_intersection
            col lower upper hrows hswitch 0⟩
    let hz : binaryOpenCoverIntersectionToPiece U V
        (A.subdivision.label col lower) z = Csame.edgeTarget :=
      (A.leftBoundarySameComparisonTarget_eq_switchSource
        hxU hxV hUV hU hV letters Fhom i s t hshared hs ht).symm
    binaryOpenCoverVertexPotentialFromIntersection
        hxU hxV hUV z (A.subdivision.label col lower)
        Csame.edgeTarget Csame.leftEnd hz =
      ((Monoid.PushoutI.of (A.subdivision.label col lower)
        Cbottom.startChange : binaryVanKampenPushout U V hxU hxV)⁻¹) := by
  dsimp only
  rw [A.subdivision.verticalSwitchBottom_startPotential_eq_vertexPotential]
  apply binaryOpenCoverVertexPotentialFromIntersection_cast
    hxU hxV hUV
      (A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
        (A.segmentGridEdgeIndex i s))
  · apply Subtype.ext
    rfl
  · apply Path.ext
    funext u
    apply Subtype.ext
    rw [Path.cast_coe,
      coe_binaryOpenCoverSamePathConnectorComparison_leftEnd]
    have hconnector := A.leftBoundaryCellEnd_eq_verticalSwitchBottomStart
      hxU hxV hUV hU hV letters Fhom i s t hshared
      (by
        intro h
        exact ht (h.symm.trans hs))
    have hu := congrArg (fun p => ((p u :
      binaryOpenCoverPiece U V
        (A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
          (A.segmentGridEdgeIndex i s))) : X)) hconnector
    simpa only [Path.cast_coe] using hu
  · exact A.leftBoundarySameComparisonTarget_eq_switchSource
      hxU hxV hUV hU hV letters Fhom i s t hshared hs ht

/-- 同一 mixed 分支中的下方 letter potential，与上方 dual comparison 在共享顶点的 letter
potential 严格相同。-/
private theorem leftBoundarySameLetterEndPotential_eq_upperDual
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
    (hshared : s.succ = t.castSucc)
    (hs : A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
      (A.segmentGridEdgeIndex i s) = (letters.reverse.get i).1)
    (ht : A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
      (A.segmentGridEdgeIndex i t) ≠ (letters.reverse.get i).1) :
    let col : Fin A.subdivision.steps := ⟨0, A.subdivision.steps_pos⟩
    let lower := A.segmentGridEdgeIndex i s
    let upper := A.segmentGridEdgeIndex i t
    let hrows : lower.succ = upper.castSucc :=
      A.segmentGridEdgeIndex_succ_eq_castSucc i s t hshared
    let hswitch : A.subdivision.label col lower ≠
        A.subdivision.label col upper := by
      intro h
      exact ht (h.symm.trans hs)
    let Csame := binaryOpenCoverSamePathConnectorComparison hxU hxV
      (A.leftBoundaryAlignedGridEdge hxU hxV letters Fhom i s)
      (A.leftBoundaryAlignedGridEdge_mem_cellPiece hxU hxV letters Fhom i s)
      (A.leftBoundaryAlignedGridEdge_mem_letterPiece hxU hxV letters Fhom i s)
      hs
      (A.leftBoundaryAlignedGridEdgeCellStart
        hxU hxV hU hV letters Fhom i s)
      (A.leftBoundaryAlignedGridEdgeCellEnd
        hxU hxV hU hV letters Fhom i s)
      (A.leftBoundaryAlignedGridEdgeLetterStart
        hxU hxV hU hV letters Fhom i s)
      (A.leftBoundaryAlignedGridEdgeLetterEnd
        hxU hxV hU hV letters Fhom i s)
    let qUpper := A.leftBoundaryAlignedGridEdge hxU hxV letters Fhom i t
    let hbUpper := A.leftBoundaryAlignedGridEdge_mem_cellPiece
      hxU hxV letters Fhom i t
    let hcUpper := A.leftBoundaryAlignedGridEdge_mem_letterPiece
      hxU hxV letters Fhom i t
    let CCupper := binaryOpenCoverDualPathConnectorComparison hxU hxV hUV
      qUpper hbUpper hcUpper ht hcUpper
      (A.leftBoundaryAlignedGridEdgeLetterStart
        hxU hxV hU hV letters Fhom i t)
      (A.leftBoundaryAlignedGridEdgeLetterEnd
        hxU hxV hU hV letters Fhom i t)
    let z : ↥(U ∩ V) :=
      ⟨squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
          A.subdivision.steps_pos col.castSucc lower.succ, by
        simpa [squareGridVertex, Set.Icc.convexComb_zero] using
          A.subdivision.verticalSwitchEdge_mem_intersection
            col lower upper hrows hswitch 0⟩
    let hz : binaryOpenCoverIntersectionToPiece U V
        (A.subdivision.label col lower) z = Csame.edgeTarget :=
      (A.leftBoundarySameComparisonTarget_eq_switchSource
        hxU hxV hUV hU hV letters Fhom i s t hshared hs ht).symm
    binaryOpenCoverVertexPotentialFromIntersection
        hxU hxV hUV z (A.subdivision.label col lower)
        Csame.edgeTarget Csame.rightEnd hz =
      ((Monoid.PushoutI.of (letters.reverse.get i).1
        CCupper.startChange : binaryVanKampenPushout U V hxU hxV)⁻¹) := by
  dsimp only
  rw [binaryOpenCoverDualPathConnectorComparison_startPotential_eq]
  apply binaryOpenCoverVertexPotentialFromIntersection_cast_label
    hxU hxV hUV
      (A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
        (A.segmentGridEdgeIndex i s))
      (letters.reverse.get i).1 hs
  · apply Subtype.ext
    exact A.leftBoundary_segmentGridEdgeIndex_shared_vertex i s t hshared
  · rw [binaryOpenCoverSamePathConnectorComparison_edgeTarget]
    exact A.leftBoundary_segmentGridEdgeIndex_shared_vertex i s t hshared
  · intro u
    exact coe_binaryOpenCoverSamePathConnectorComparison_rightEnd
      hxU hxV
      (A.leftBoundaryAlignedGridEdge hxU hxV letters Fhom i s)
      (A.leftBoundaryAlignedGridEdge_mem_cellPiece
        hxU hxV letters Fhom i s)
      (A.leftBoundaryAlignedGridEdge_mem_letterPiece
        hxU hxV letters Fhom i s) hs
      (A.leftBoundaryAlignedGridEdgeCellStart
        hxU hxV hU hV letters Fhom i s)
      (A.leftBoundaryAlignedGridEdgeCellEnd
        hxU hxV hU hV letters Fhom i s)
      (A.leftBoundaryAlignedGridEdgeLetterStart
        hxU hxV hU hV letters Fhom i s)
      (A.leftBoundaryAlignedGridEdgeLetterEnd
        hxU hxV hU hV letters Fhom i s) u |>.trans (by
    have hconnector := A.leftBoundaryAlignedGridEdgeLetterConnector_adjacent
      hxU hxV hU hV letters Fhom i s t hshared
    have hu := congrArg (fun p => ((p u :
      binaryOpenCoverPiece U V (letters.reverse.get i).1) : X)) hconnector
    simpa only [Path.cast_coe] using hu)

/-- 下方 cell 标签等于固定 letter、上方 cell 标签不同时，相邻逐边 transitions 与真实竖直
切换 transition 满足共享顶点 cocycle。-/
private theorem leftBoundaryCellToLetterTransitions_adjacent_of_lower_eq
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
    (hshared : s.succ = t.castSucc)
    (hs : A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
      (A.segmentGridEdgeIndex i s) = (letters.reverse.get i).1)
    (ht : A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
      (A.segmentGridEdgeIndex i t) ≠ (letters.reverse.get i).1) :
    let col : Fin A.subdivision.steps := ⟨0, A.subdivision.steps_pos⟩
    let lower := A.segmentGridEdgeIndex i s
    let upper := A.segmentGridEdgeIndex i t
    let hrows : lower.succ = upper.castSucc :=
      A.segmentGridEdgeIndex_succ_eq_castSucc i s t hshared
    let hswitch : A.subdivision.label col lower ≠
        A.subdivision.label col upper := by
      intro h
      exact ht (h.symm.trans hs)
    let lowerT := A.leftBoundaryCellToLetterTransitions
      hxU hxV hUV hU hV letters Fhom i s
    let upperT := A.leftBoundaryCellToLetterTransitions
      hxU hxV hUV hU hV letters Fhom i t
    let verticalT := A.subdivision.verticalSwitchEdgeTransitions
      hxU hxV hUV hU hV col lower upper hrows hswitch
    lowerT.endChange = upperT.startChange * verticalT.startChange := by
  dsimp only
  let col : Fin A.subdivision.steps := ⟨0, A.subdivision.steps_pos⟩
  let lower := A.segmentGridEdgeIndex i s
  let upper := A.segmentGridEdgeIndex i t
  let hrows : lower.succ = upper.castSucc :=
    A.segmentGridEdgeIndex_succ_eq_castSucc i s t hshared
  have hswitch : A.subdivision.label col lower ≠
      A.subdivision.label col upper := by
    intro h
    exact ht (h.symm.trans hs)
  let qUpper := A.leftBoundaryAlignedGridEdge hxU hxV letters Fhom i t
  let hbUpper := A.leftBoundaryAlignedGridEdge_mem_cellPiece
    hxU hxV letters Fhom i t
  let hcUpper := A.leftBoundaryAlignedGridEdge_mem_letterPiece
    hxU hxV letters Fhom i t
  let CBupper := binaryOpenCoverDualPathConnectorComparison hxU hxV hUV
    qUpper hbUpper hcUpper ht hbUpper
    (A.leftBoundaryAlignedGridEdgeCellStart
      hxU hxV hU hV letters Fhom i t)
    (A.leftBoundaryAlignedGridEdgeCellEnd
      hxU hxV hU hV letters Fhom i t)
  let CCupper := binaryOpenCoverDualPathConnectorComparison hxU hxV hUV
    qUpper hbUpper hcUpper ht hcUpper
    (A.leftBoundaryAlignedGridEdgeLetterStart
      hxU hxV hU hV letters Fhom i t)
    (A.leftBoundaryAlignedGridEdgeLetterEnd
      hxU hxV hU hV letters Fhom i t)
  let Cbottom := A.subdivision.verticalSwitchBottomConnectorComparison
    hxU hxV hUV hU hV col lower upper hrows hswitch
  let Ctop := A.subdivision.verticalSwitchTopConnectorComparison
    hxU hxV hUV hU hV col lower upper hrows hswitch
  let bottomPotential : binaryVanKampenPushout U V hxU hxV :=
    (Monoid.PushoutI.of (A.subdivision.label col lower)
      Cbottom.startChange)⁻¹
  let topPotential : binaryVanKampenPushout U V hxU hxV :=
    (Monoid.PushoutI.of (A.subdivision.label col upper)
      Ctop.startChange)⁻¹
  let targetPotential : binaryVanKampenPushout U V hxU hxV :=
    (Monoid.PushoutI.of (letters.reverse.get i).1
      CCupper.startChange)⁻¹
  apply edgeTransitions_cocycle_of_potentials
    bottomPotential topPotential targetPotential
  · rw [A.leftBoundarySameTransitionEnd_eq_switchVertexPotentials
      hxU hxV hUV hU hV letters Fhom i s t hshared hs ht]
    rw [A.leftBoundarySameCellEndPotential_eq_switchBottom
      hxU hxV hUV hU hV letters Fhom i s t hshared hs ht]
    rw [A.leftBoundarySameLetterEndPotential_eq_upperDual
      hxU hxV hUV hU hV letters Fhom i s t hshared hs ht]
  · rw [A.leftBoundaryCellToLetterTransitions_start_potential_of_ne
      hxU hxV hUV hU hV letters Fhom i t ht]
    unfold topPotential targetPotential
    rw [A.leftBoundaryDualCellStartPotential_eq_verticalSwitchTop
      hxU hxV hUV hU hV letters Fhom i s t hshared ht hswitch]
  · exact A.subdivision.verticalSwitchEdgeTransitions_start_potential
      hxU hxV hUV hU hV col lower upper hrows hswitch

/-- 对称 mixed 分支的端点正规化：上方 same comparison 的起点与竖直切换边上格左端相同。-/
private theorem leftBoundaryUpperSameComparisonSource_eq_switchTopSource
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
    (hshared : s.succ = t.castSucc)
    (hs : A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
      (A.segmentGridEdgeIndex i s) ≠ (letters.reverse.get i).1)
    (ht : A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
      (A.segmentGridEdgeIndex i t) = (letters.reverse.get i).1) :
    let col : Fin A.subdivision.steps := ⟨0, A.subdivision.steps_pos⟩
    let lower := A.segmentGridEdgeIndex i s
    let upper := A.segmentGridEdgeIndex i t
    let hrows : lower.succ = upper.castSucc :=
      A.segmentGridEdgeIndex_succ_eq_castSucc i s t hshared
    let hswitch : A.subdivision.label col lower ≠
        A.subdivision.label col upper := by
      intro h
      exact hs (h.trans ht)
    let Csame := binaryOpenCoverSamePathConnectorComparison hxU hxV
      (A.leftBoundaryAlignedGridEdge hxU hxV letters Fhom i t)
      (A.leftBoundaryAlignedGridEdge_mem_cellPiece hxU hxV letters Fhom i t)
      (A.leftBoundaryAlignedGridEdge_mem_letterPiece hxU hxV letters Fhom i t)
      ht
      (A.leftBoundaryAlignedGridEdgeCellStart
        hxU hxV hU hV letters Fhom i t)
      (A.leftBoundaryAlignedGridEdgeCellEnd
        hxU hxV hU hV letters Fhom i t)
      (A.leftBoundaryAlignedGridEdgeLetterStart
        hxU hxV hU hV letters Fhom i t)
      (A.leftBoundaryAlignedGridEdgeLetterEnd
        hxU hxV hU hV letters Fhom i t)
    let Ctop := A.subdivision.verticalSwitchTopConnectorComparison
      hxU hxV hUV hU hV col lower upper hrows hswitch
    Csame.edgeSource = Ctop.edgeSource := by
  dsimp only
  rw [binaryOpenCoverSamePathConnectorComparison_edgeSource]
  apply Subtype.ext
  unfold BinaryOpenCoverSquareSubdivision.verticalSwitchTopConnectorComparison
  dsimp only [CommonEdgeConnectorComparison.edgeSource]
  rw [coe_binaryOpenCoverIntersectionToPiece]
  exact A.leftBoundary_segmentGridEdgeIndex_shared_vertex i s t hshared |>.symm

/-- “下异上同”分支中，上方逐边 transition 在共享 switch 顶点处由其 cell／letter 起点
potentials 给出。-/
private theorem leftBoundaryUpperSameTransitionStart_eq_switchVertexPotentials
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
    (hshared : s.succ = t.castSucc)
    (hs : A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
      (A.segmentGridEdgeIndex i s) ≠ (letters.reverse.get i).1)
    (ht : A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
      (A.segmentGridEdgeIndex i t) = (letters.reverse.get i).1) :
    let col : Fin A.subdivision.steps := ⟨0, A.subdivision.steps_pos⟩
    let lower := A.segmentGridEdgeIndex i s
    let upper := A.segmentGridEdgeIndex i t
    let hrows : lower.succ = upper.castSucc :=
      A.segmentGridEdgeIndex_succ_eq_castSucc i s t hshared
    let hswitch : A.subdivision.label col lower ≠
        A.subdivision.label col upper := by
      intro h
      exact hs (h.trans ht)
    let Csame := binaryOpenCoverSamePathConnectorComparison hxU hxV
      (A.leftBoundaryAlignedGridEdge hxU hxV letters Fhom i t)
      (A.leftBoundaryAlignedGridEdge_mem_cellPiece hxU hxV letters Fhom i t)
      (A.leftBoundaryAlignedGridEdge_mem_letterPiece hxU hxV letters Fhom i t)
      ht
      (A.leftBoundaryAlignedGridEdgeCellStart
        hxU hxV hU hV letters Fhom i t)
      (A.leftBoundaryAlignedGridEdgeCellEnd
        hxU hxV hU hV letters Fhom i t)
      (A.leftBoundaryAlignedGridEdgeLetterStart
        hxU hxV hU hV letters Fhom i t)
      (A.leftBoundaryAlignedGridEdgeLetterEnd
        hxU hxV hU hV letters Fhom i t)
    let z : ↥(U ∩ V) :=
      ⟨squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
          A.subdivision.steps_pos col.castSucc lower.succ, by
        simpa [squareGridVertex, Set.Icc.convexComb_zero] using
          A.subdivision.verticalSwitchEdge_mem_intersection
            col lower upper hrows hswitch 0⟩
    let hz : binaryOpenCoverIntersectionToPiece U V
        (A.subdivision.label col upper) z = Csame.edgeSource :=
      (A.leftBoundaryUpperSameComparisonSource_eq_switchTopSource
        hxU hxV hUV hU hV letters Fhom i s t hshared hs ht).symm
    let T := A.leftBoundaryCellToLetterTransitions
      hxU hxV hUV hU hV letters Fhom i t
    T.startChange = transitionFromPotentials
      (binaryOpenCoverVertexPotentialFromIntersection
        hxU hxV hUV z (A.subdivision.label col upper)
        Csame.edgeSource Csame.leftStart hz)
      (binaryOpenCoverVertexPotentialFromIntersection
        hxU hxV hUV z (A.subdivision.label col upper)
        Csame.edgeSource Csame.rightStart hz) := by
  dsimp only
  rw [PathConcatAlignedSquareSubdivision.leftBoundaryCellToLetterTransitions,
    dite_eq_left ht]
  exact (binaryOpenCoverSamePathConnectorComparison hxU hxV
    (A.leftBoundaryAlignedGridEdge hxU hxV letters Fhom i t)
    (A.leftBoundaryAlignedGridEdge_mem_cellPiece hxU hxV letters Fhom i t)
    (A.leftBoundaryAlignedGridEdge_mem_letterPiece hxU hxV letters Fhom i t)
    ht
    (A.leftBoundaryAlignedGridEdgeCellStart
      hxU hxV hU hV letters Fhom i t)
    (A.leftBoundaryAlignedGridEdgeCellEnd
      hxU hxV hU hV letters Fhom i t)
    (A.leftBoundaryAlignedGridEdgeLetterStart
      hxU hxV hU hV letters Fhom i t)
    (A.leftBoundaryAlignedGridEdgeLetterEnd
      hxU hxV hU hV letters Fhom i t)).pushout_startChange_inv_eq_vertexPotentials
        hxU hxV hUV
        (A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
          (A.segmentGridEdgeIndex i t)) _ _

/-- 上方 same transition 的 cell 起点 potential 等于真实 switch 的上格 potential。-/
private theorem leftBoundaryUpperSameCellStartPotential_eq_switchTop
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
    (hshared : s.succ = t.castSucc)
    (hs : A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
      (A.segmentGridEdgeIndex i s) ≠ (letters.reverse.get i).1)
    (ht : A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
      (A.segmentGridEdgeIndex i t) = (letters.reverse.get i).1) :
    let col : Fin A.subdivision.steps := ⟨0, A.subdivision.steps_pos⟩
    let lower := A.segmentGridEdgeIndex i s
    let upper := A.segmentGridEdgeIndex i t
    let hrows : lower.succ = upper.castSucc :=
      A.segmentGridEdgeIndex_succ_eq_castSucc i s t hshared
    let hswitch : A.subdivision.label col lower ≠
        A.subdivision.label col upper := by
      intro h
      exact hs (h.trans ht)
    let Csame := binaryOpenCoverSamePathConnectorComparison hxU hxV
      (A.leftBoundaryAlignedGridEdge hxU hxV letters Fhom i t)
      (A.leftBoundaryAlignedGridEdge_mem_cellPiece hxU hxV letters Fhom i t)
      (A.leftBoundaryAlignedGridEdge_mem_letterPiece hxU hxV letters Fhom i t)
      ht
      (A.leftBoundaryAlignedGridEdgeCellStart
        hxU hxV hU hV letters Fhom i t)
      (A.leftBoundaryAlignedGridEdgeCellEnd
        hxU hxV hU hV letters Fhom i t)
      (A.leftBoundaryAlignedGridEdgeLetterStart
        hxU hxV hU hV letters Fhom i t)
      (A.leftBoundaryAlignedGridEdgeLetterEnd
        hxU hxV hU hV letters Fhom i t)
    let Ctop := A.subdivision.verticalSwitchTopConnectorComparison
      hxU hxV hUV hU hV col lower upper hrows hswitch
    let z : ↥(U ∩ V) :=
      ⟨squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
          A.subdivision.steps_pos col.castSucc lower.succ, by
        simpa [squareGridVertex, Set.Icc.convexComb_zero] using
          A.subdivision.verticalSwitchEdge_mem_intersection
            col lower upper hrows hswitch 0⟩
    let hz : binaryOpenCoverIntersectionToPiece U V
        (A.subdivision.label col upper) z = Csame.edgeSource :=
      (A.leftBoundaryUpperSameComparisonSource_eq_switchTopSource
        hxU hxV hUV hU hV letters Fhom i s t hshared hs ht).symm
    binaryOpenCoverVertexPotentialFromIntersection
        hxU hxV hUV z (A.subdivision.label col upper)
        Csame.edgeSource Csame.leftStart hz =
      ((Monoid.PushoutI.of (A.subdivision.label col upper)
        Ctop.startChange : binaryVanKampenPushout U V hxU hxV)⁻¹) := by
  dsimp only
  rw [A.subdivision.verticalSwitchTop_startPotential_eq_vertexPotential]
  apply binaryOpenCoverVertexPotentialFromIntersection_cast
    hxU hxV hUV
      (A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
        (A.segmentGridEdgeIndex i t))
  · apply Subtype.ext
    rfl
  · apply Path.ext
    funext u
    apply Subtype.ext
    rw [Path.cast_coe,
      coe_binaryOpenCoverSamePathConnectorComparison_leftStart]
    have hconnector := A.leftBoundaryCellStart_eq_verticalSwitchTopStart
      hxU hxV hUV hU hV letters Fhom i s t hshared
      (by
        intro h
        exact hs (h.trans ht))
    have hu := congrArg (fun p => ((p u :
      binaryOpenCoverPiece U V
        (A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
          (A.segmentGridEdgeIndex i t))) : X)) hconnector
    simpa only [Path.cast_coe] using hu
  · exact A.leftBoundaryUpperSameComparisonSource_eq_switchTopSource
      hxU hxV hUV hU hV letters Fhom i s t hshared hs ht

/-- 上方 same transition 的 letter 起点 potential，与下方 dual comparison 的 letter 终点 potential
在共享顶点严格相同。-/
private theorem leftBoundaryUpperSameLetterStartPotential_eq_lowerDual
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
    (hshared : s.succ = t.castSucc)
    (hs : A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
      (A.segmentGridEdgeIndex i s) ≠ (letters.reverse.get i).1)
    (ht : A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
      (A.segmentGridEdgeIndex i t) = (letters.reverse.get i).1) :
    let col : Fin A.subdivision.steps := ⟨0, A.subdivision.steps_pos⟩
    let lower := A.segmentGridEdgeIndex i s
    let upper := A.segmentGridEdgeIndex i t
    let hrows : lower.succ = upper.castSucc :=
      A.segmentGridEdgeIndex_succ_eq_castSucc i s t hshared
    let hswitch : A.subdivision.label col lower ≠
        A.subdivision.label col upper := by
      intro h
      exact hs (h.trans ht)
    let Csame := binaryOpenCoverSamePathConnectorComparison hxU hxV
      (A.leftBoundaryAlignedGridEdge hxU hxV letters Fhom i t)
      (A.leftBoundaryAlignedGridEdge_mem_cellPiece hxU hxV letters Fhom i t)
      (A.leftBoundaryAlignedGridEdge_mem_letterPiece hxU hxV letters Fhom i t)
      ht
      (A.leftBoundaryAlignedGridEdgeCellStart
        hxU hxV hU hV letters Fhom i t)
      (A.leftBoundaryAlignedGridEdgeCellEnd
        hxU hxV hU hV letters Fhom i t)
      (A.leftBoundaryAlignedGridEdgeLetterStart
        hxU hxV hU hV letters Fhom i t)
      (A.leftBoundaryAlignedGridEdgeLetterEnd
        hxU hxV hU hV letters Fhom i t)
    let qLower := A.leftBoundaryAlignedGridEdge hxU hxV letters Fhom i s
    let hbLower := A.leftBoundaryAlignedGridEdge_mem_cellPiece
      hxU hxV letters Fhom i s
    let hcLower := A.leftBoundaryAlignedGridEdge_mem_letterPiece
      hxU hxV letters Fhom i s
    let CClower := binaryOpenCoverDualPathConnectorComparison hxU hxV hUV
      qLower hbLower hcLower hs hcLower
      (A.leftBoundaryAlignedGridEdgeLetterStart
        hxU hxV hU hV letters Fhom i s)
      (A.leftBoundaryAlignedGridEdgeLetterEnd
        hxU hxV hU hV letters Fhom i s)
    let z : ↥(U ∩ V) :=
      ⟨squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
          A.subdivision.steps_pos col.castSucc lower.succ, by
        simpa [squareGridVertex, Set.Icc.convexComb_zero] using
          A.subdivision.verticalSwitchEdge_mem_intersection
            col lower upper hrows hswitch 0⟩
    let hz : binaryOpenCoverIntersectionToPiece U V
        (A.subdivision.label col upper) z = Csame.edgeSource :=
      (A.leftBoundaryUpperSameComparisonSource_eq_switchTopSource
        hxU hxV hUV hU hV letters Fhom i s t hshared hs ht).symm
    binaryOpenCoverVertexPotentialFromIntersection
        hxU hxV hUV z (A.subdivision.label col upper)
        Csame.edgeSource Csame.rightStart hz =
      ((Monoid.PushoutI.of (letters.reverse.get i).1
        CClower.endChange : binaryVanKampenPushout U V hxU hxV)⁻¹) := by
  dsimp only
  rw [binaryOpenCoverDualPathConnectorComparison_endPotential_eq]
  apply binaryOpenCoverVertexPotentialFromIntersection_cast_label
    hxU hxV hUV
      (A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
        (A.segmentGridEdgeIndex i t))
      (letters.reverse.get i).1 ht
  · apply Subtype.ext
    rfl
  · rw [binaryOpenCoverSamePathConnectorComparison_edgeSource]
    exact A.leftBoundary_segmentGridEdgeIndex_shared_vertex i s t hshared |>.symm
  · intro u
    exact coe_binaryOpenCoverSamePathConnectorComparison_rightStart
      hxU hxV
      (A.leftBoundaryAlignedGridEdge hxU hxV letters Fhom i t)
      (A.leftBoundaryAlignedGridEdge_mem_cellPiece
        hxU hxV letters Fhom i t)
      (A.leftBoundaryAlignedGridEdge_mem_letterPiece
        hxU hxV letters Fhom i t) ht
      (A.leftBoundaryAlignedGridEdgeCellStart
        hxU hxV hU hV letters Fhom i t)
      (A.leftBoundaryAlignedGridEdgeCellEnd
        hxU hxV hU hV letters Fhom i t)
      (A.leftBoundaryAlignedGridEdgeLetterStart
        hxU hxV hU hV letters Fhom i t)
      (A.leftBoundaryAlignedGridEdgeLetterEnd
        hxU hxV hU hV letters Fhom i t) u |>.trans (by
    have hconnector := A.leftBoundaryAlignedGridEdgeLetterConnector_adjacent
      hxU hxV hU hV letters Fhom i s t hshared
    have hu := congrArg (fun p => ((p u :
      binaryOpenCoverPiece U V (letters.reverse.get i).1) : X)) hconnector
    simpa only [Path.cast_coe] using hu.symm)

/-- 下方 cell 标签不同于固定 letter、上方 cell 标签等于固定 letter 时的共享顶点 cocycle。-/
private theorem leftBoundaryCellToLetterTransitions_adjacent_of_upper_eq
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
    (hshared : s.succ = t.castSucc)
    (hs : A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
      (A.segmentGridEdgeIndex i s) ≠ (letters.reverse.get i).1)
    (ht : A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
      (A.segmentGridEdgeIndex i t) = (letters.reverse.get i).1) :
    let col : Fin A.subdivision.steps := ⟨0, A.subdivision.steps_pos⟩
    let lower := A.segmentGridEdgeIndex i s
    let upper := A.segmentGridEdgeIndex i t
    let hrows : lower.succ = upper.castSucc :=
      A.segmentGridEdgeIndex_succ_eq_castSucc i s t hshared
    let hswitch : A.subdivision.label col lower ≠
        A.subdivision.label col upper := by
      intro h
      exact hs (h.trans ht)
    let lowerT := A.leftBoundaryCellToLetterTransitions
      hxU hxV hUV hU hV letters Fhom i s
    let upperT := A.leftBoundaryCellToLetterTransitions
      hxU hxV hUV hU hV letters Fhom i t
    let verticalT := A.subdivision.verticalSwitchEdgeTransitions
      hxU hxV hUV hU hV col lower upper hrows hswitch
    lowerT.endChange = upperT.startChange * verticalT.startChange := by
  dsimp only
  let col : Fin A.subdivision.steps := ⟨0, A.subdivision.steps_pos⟩
  let lower := A.segmentGridEdgeIndex i s
  let upper := A.segmentGridEdgeIndex i t
  let hrows : lower.succ = upper.castSucc :=
    A.segmentGridEdgeIndex_succ_eq_castSucc i s t hshared
  have hswitch : A.subdivision.label col lower ≠
      A.subdivision.label col upper := by
    intro h
    exact hs (h.trans ht)
  let qLower := A.leftBoundaryAlignedGridEdge hxU hxV letters Fhom i s
  let hbLower := A.leftBoundaryAlignedGridEdge_mem_cellPiece
    hxU hxV letters Fhom i s
  let hcLower := A.leftBoundaryAlignedGridEdge_mem_letterPiece
    hxU hxV letters Fhom i s
  let CBlower := binaryOpenCoverDualPathConnectorComparison hxU hxV hUV
    qLower hbLower hcLower hs hbLower
    (A.leftBoundaryAlignedGridEdgeCellStart
      hxU hxV hU hV letters Fhom i s)
    (A.leftBoundaryAlignedGridEdgeCellEnd
      hxU hxV hU hV letters Fhom i s)
  let CClower := binaryOpenCoverDualPathConnectorComparison hxU hxV hUV
    qLower hbLower hcLower hs hcLower
    (A.leftBoundaryAlignedGridEdgeLetterStart
      hxU hxV hU hV letters Fhom i s)
    (A.leftBoundaryAlignedGridEdgeLetterEnd
      hxU hxV hU hV letters Fhom i s)
  let Cbottom := A.subdivision.verticalSwitchBottomConnectorComparison
    hxU hxV hUV hU hV col lower upper hrows hswitch
  let Ctop := A.subdivision.verticalSwitchTopConnectorComparison
    hxU hxV hUV hU hV col lower upper hrows hswitch
  let bottomPotential : binaryVanKampenPushout U V hxU hxV :=
    (Monoid.PushoutI.of (A.subdivision.label col lower)
      Cbottom.startChange)⁻¹
  let topPotential : binaryVanKampenPushout U V hxU hxV :=
    (Monoid.PushoutI.of (A.subdivision.label col upper)
      Ctop.startChange)⁻¹
  let targetPotential : binaryVanKampenPushout U V hxU hxV :=
    (Monoid.PushoutI.of (letters.reverse.get i).1
      CClower.endChange)⁻¹
  apply edgeTransitions_cocycle_of_potentials
    bottomPotential topPotential targetPotential
  · rw [A.leftBoundaryCellToLetterTransitions_end_potential_of_ne
      hxU hxV hUV hU hV letters Fhom i s hs]
    unfold bottomPotential targetPotential
    rw [A.leftBoundaryDualCellEndPotential_eq_verticalSwitchBottom
      hxU hxV hUV hU hV letters Fhom i s t hshared hs hswitch]
  · rw [A.leftBoundaryUpperSameTransitionStart_eq_switchVertexPotentials
      hxU hxV hUV hU hV letters Fhom i s t hshared hs ht]
    rw [A.leftBoundaryUpperSameCellStartPotential_eq_switchTop
      hxU hxV hUV hU hV letters Fhom i s t hshared hs ht]
    rw [A.leftBoundaryUpperSameLetterStartPotential_eq_lowerDual
      hxU hxV hUV hU hV letters Fhom i s t hshared hs ht]
  · exact A.subdivision.verticalSwitchEdgeTransitions_start_potential
      hxU hxV hUV hU hV col lower upper hrows hswitch

/-- 上下 cell 标签都等于固定 letter 时，三条 transitions 在单一共同覆盖成员中满足共享顶点
cocycle；该分支不需要共享点属于交集。-/
private theorem leftBoundaryCellToLetterTransitions_adjacent_of_both_eq
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
    (hshared : s.succ = t.castSucc)
    (hs : A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
      (A.segmentGridEdgeIndex i s) = (letters.reverse.get i).1)
    (ht : A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
      (A.segmentGridEdgeIndex i t) = (letters.reverse.get i).1) :
    let col : Fin A.subdivision.steps := ⟨0, A.subdivision.steps_pos⟩
    let lower := A.segmentGridEdgeIndex i s
    let upper := A.segmentGridEdgeIndex i t
    let hrows : lower.succ = upper.castSucc :=
      A.segmentGridEdgeIndex_succ_eq_castSucc i s t hshared
    let hlabel : A.subdivision.label col lower =
        A.subdivision.label col upper := hs.trans ht.symm
    let lowerT := A.leftBoundaryCellToLetterTransitions
      hxU hxV hUV hU hV letters Fhom i s
    let upperT := A.leftBoundaryCellToLetterTransitions
      hxU hxV hUV hU hV letters Fhom i t
    let verticalT := A.subdivision.verticalCommonEdgeTransitions
      hxU hxV hU hV col lower upper hrows hlabel
    lowerT.endChange = upperT.startChange * verticalT.startChange := by
  dsimp only
  let col : Fin A.subdivision.steps := ⟨0, A.subdivision.steps_pos⟩
  let lower := A.segmentGridEdgeIndex i s
  let upper := A.segmentGridEdgeIndex i t
  let hrows : lower.succ = upper.castSucc :=
    A.segmentGridEdgeIndex_succ_eq_castSucc i s t hshared
  let hlabel : A.subdivision.label col lower =
      A.subdivision.label col upper := hs.trans ht.symm
  let qs := A.leftBoundaryAlignedGridEdge hxU hxV letters Fhom i s
  let qt := A.leftBoundaryAlignedGridEdge hxU hxV letters Fhom i t
  let hbs := A.leftBoundaryAlignedGridEdge_mem_cellPiece
    hxU hxV letters Fhom i s
  let hbt := A.leftBoundaryAlignedGridEdge_mem_cellPiece
    hxU hxV letters Fhom i t
  let hcs := A.leftBoundaryAlignedGridEdge_mem_letterPiece
    hxU hxV letters Fhom i s
  let hct := A.leftBoundaryAlignedGridEdge_mem_letterPiece
    hxU hxV letters Fhom i t
  let Cs := binaryOpenCoverSamePathConnectorComparison hxU hxV
    qs hbs hcs hs
    (A.leftBoundaryAlignedGridEdgeCellStart
      hxU hxV hU hV letters Fhom i s)
    (A.leftBoundaryAlignedGridEdgeCellEnd
      hxU hxV hU hV letters Fhom i s)
    (A.leftBoundaryAlignedGridEdgeLetterStart
      hxU hxV hU hV letters Fhom i s)
    (A.leftBoundaryAlignedGridEdgeLetterEnd
      hxU hxV hU hV letters Fhom i s)
  let Ct := binaryOpenCoverSamePathConnectorComparison hxU hxV
    qt hbt hct ht
    (A.leftBoundaryAlignedGridEdgeCellStart
      hxU hxV hU hV letters Fhom i t)
    (A.leftBoundaryAlignedGridEdgeCellEnd
      hxU hxV hU hV letters Fhom i t)
    (A.leftBoundaryAlignedGridEdgeLetterStart
      hxU hxV hU hV letters Fhom i t)
    (A.leftBoundaryAlignedGridEdgeLetterEnd
      hxU hxV hU hV letters Fhom i t)
  let Cv := A.subdivision.verticalCommonEdgeConnectorComparison
    hxU hxV hU hV col lower upper hrows hlabel
  let fLower := (Monoid.PushoutI.of
    (φ := binaryOpenCoverIntersectionMaps U V hxU hxV)
    (A.subdivision.label col lower) :
    FundamentalGroup
      (binaryOpenCoverPiece U V (A.subdivision.label col lower))
      (binaryOpenCoverBasepoint hxU hxV (A.subdivision.label col lower)) →*
      binaryVanKampenPushout U V hxU hxV)
  have hCsTarget : (Cs.edgeTarget : X) = (Cv.edgeSource : X) := by
    rw [binaryOpenCoverSamePathConnectorComparison_edgeTarget]
    rfl
  have hCsTarget' : Cs.edgeTarget = Cv.edgeSource := by
    apply Subtype.ext
    exact hCsTarget
  have hCtSource : (Ct.edgeSource : X) = (Cv.edgeSource : X) := by
    rw [binaryOpenCoverSamePathConnectorComparison_edgeSource]
    exact A.leftBoundary_segmentGridEdgeIndex_shared_vertex i s t hshared |>.symm
  let targetConnector := Cs.rightEnd.cast rfl hCsTarget'.symm
  let lowerPotential := binaryOpenCoverConnectorPotential hxU hxV
    (A.subdivision.label col lower) Cv.edgeSource Cv.leftStart targetConnector
  let upperPotential := binaryOpenCoverConnectorPotential hxU hxV
    (A.subdivision.label col lower) Cv.edgeSource Cv.rightStart targetConnector
  let verticalPotential := binaryOpenCoverConnectorPotential hxU hxV
    (A.subdivision.label col lower) Cv.edgeSource Cv.leftStart Cv.rightStart
  have hLower : binaryOpenCoverConnectorPotential hxU hxV
      (A.subdivision.label col lower) Cs.edgeTarget Cs.leftEnd Cs.rightEnd =
      lowerPotential := by
    apply binaryOpenCoverConnectorPotential_cast_label
      hxU hxV (A.subdivision.label col lower)
        (A.subdivision.label col lower) rfl
    · exact hCsTarget
    · intro u
      have hconnector := A.leftBoundaryCellEnd_eq_verticalCommonLeftStart
        hxU hxV hU hV letters Fhom i s t hshared hlabel
      have hu := congrArg (fun p => ((p u :
        binaryOpenCoverPiece U V (A.subdivision.label col lower)) : X)) hconnector
      exact (coe_binaryOpenCoverSamePathConnectorComparison_leftEnd
        hxU hxV qs hbs hcs hs
        (A.leftBoundaryAlignedGridEdgeCellStart
          hxU hxV hU hV letters Fhom i s)
        (A.leftBoundaryAlignedGridEdgeCellEnd
          hxU hxV hU hV letters Fhom i s)
        (A.leftBoundaryAlignedGridEdgeLetterStart
          hxU hxV hU hV letters Fhom i s)
        (A.leftBoundaryAlignedGridEdgeLetterEnd
          hxU hxV hU hV letters Fhom i s) u).trans (by
          simpa only [Path.cast_coe] using hu)
    · intro u
      rw [Path.cast_coe]
  have hUpper : binaryOpenCoverConnectorPotential hxU hxV
      (A.subdivision.label col upper) Ct.edgeSource Ct.leftStart Ct.rightStart =
      upperPotential := by
    apply binaryOpenCoverConnectorPotential_cast_label
      hxU hxV (A.subdivision.label col upper)
        (A.subdivision.label col lower) hlabel.symm
    · exact hCtSource
    · intro u
      exact (coe_binaryOpenCoverSamePathConnectorComparison_leftStart
        hxU hxV qt hbt hct ht
        (A.leftBoundaryAlignedGridEdgeCellStart
          hxU hxV hU hV letters Fhom i t)
        (A.leftBoundaryAlignedGridEdgeCellEnd
          hxU hxV hU hV letters Fhom i t)
        (A.leftBoundaryAlignedGridEdgeLetterStart
          hxU hxV hU hV letters Fhom i t)
        (A.leftBoundaryAlignedGridEdgeLetterEnd
          hxU hxV hU hV letters Fhom i t) u).trans
        (A.coe_leftBoundaryCellStart_eq_verticalCommonRightStart
          hxU hxV hU hV letters Fhom i s t hshared hlabel u).symm
    · intro u
      have hstart := coe_binaryOpenCoverSamePathConnectorComparison_rightStart
        hxU hxV qt hbt hct ht
        (A.leftBoundaryAlignedGridEdgeCellStart
          hxU hxV hU hV letters Fhom i t)
        (A.leftBoundaryAlignedGridEdgeCellEnd
          hxU hxV hU hV letters Fhom i t)
        (A.leftBoundaryAlignedGridEdgeLetterStart
          hxU hxV hU hV letters Fhom i t)
        (A.leftBoundaryAlignedGridEdgeLetterEnd
          hxU hxV hU hV letters Fhom i t) u
      have hconnector := A.leftBoundaryAlignedGridEdgeLetterConnector_adjacent
        hxU hxV hU hV letters Fhom i s t hshared
      have hu := congrArg (fun p => ((p u :
        binaryOpenCoverPiece U V (letters.reverse.get i).1) : X)) hconnector
      have hsEnd := coe_binaryOpenCoverSamePathConnectorComparison_rightEnd
        hxU hxV qs hbs hcs hs
        (A.leftBoundaryAlignedGridEdgeCellStart
          hxU hxV hU hV letters Fhom i s)
        (A.leftBoundaryAlignedGridEdgeCellEnd
          hxU hxV hU hV letters Fhom i s)
        (A.leftBoundaryAlignedGridEdgeLetterStart
          hxU hxV hU hV letters Fhom i s)
        (A.leftBoundaryAlignedGridEdgeLetterEnd
          hxU hxV hU hV letters Fhom i s) u
      have hletters :
          ((A.leftBoundaryAlignedGridEdgeLetterStart
            hxU hxV hU hV letters Fhom i t) u : X) =
          ((A.leftBoundaryAlignedGridEdgeLetterEnd
            hxU hxV hU hV letters Fhom i s) u : X) := by
        simpa only [Path.cast_coe] using hu.symm
      calc
        (Ct.rightStart u : X) =
            ((A.leftBoundaryAlignedGridEdgeLetterStart
              hxU hxV hU hV letters Fhom i t) u : X) := hstart
        _ = ((A.leftBoundaryAlignedGridEdgeLetterEnd
              hxU hxV hU hV letters Fhom i s) u : X) := hletters
        _ = (Cs.rightEnd u : X) := hsEnd.symm
        _ = (targetConnector u : X) := by rw [Path.cast_coe]
  rw [PathConcatAlignedSquareSubdivision.leftBoundaryCellToLetterTransitions,
    dite_eq_left hs,
    PathConcatAlignedSquareSubdivision.leftBoundaryCellToLetterTransitions,
    dite_eq_left ht]
  dsimp only
  unfold BinaryOpenCoverSquareSubdivision.verticalCommonEdgeTransitions
  dsimp only
  rw [Cs.map_endChange_inv, Ct.map_startChange_inv, Cv.map_startChange_inv]
  change binaryOpenCoverConnectorPotential hxU hxV
      (A.subdivision.label col lower) Cs.edgeTarget Cs.leftEnd Cs.rightEnd =
    binaryOpenCoverConnectorPotential hxU hxV
        (A.subdivision.label col upper) Ct.edgeSource Ct.leftStart Ct.rightStart *
      verticalPotential
  rw [hLower, hUpper]
  unfold lowerPotential upperPotential verticalPotential
    binaryOpenCoverConnectorPotential
  exact (map_connectorChange_mul fLower
    Cv.leftStart Cv.rightStart targetConnector).symm

/-- 任意相邻两条左边界细边的 cell-to-letter transitions，与两格之间真实内部横边 transition
满足统一共享顶点 cocycle。四种 Bool 标签情形全部由前述 potential／connector 结果覆盖。-/
theorem leftBoundaryCellToLetterTransitions_adjacent
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
    let hrows : lower.succ = upper.castSucc :=
      A.segmentGridEdgeIndex_succ_eq_castSucc i s t hshared
    let lowerT := A.leftBoundaryCellToLetterTransitions
      hxU hxV hUV hU hV letters Fhom i s
    let upperT := A.leftBoundaryCellToLetterTransitions
      hxU hxV hUV hU hV letters Fhom i t
    let verticalT := A.subdivision.verticalInternalEdgeTransitions
      hxU hxV hUV hU hV col lower upper hrows
    lowerT.endChange = upperT.startChange * verticalT.startChange := by
  dsimp only
  let col : Fin A.subdivision.steps := ⟨0, A.subdivision.steps_pos⟩
  let lower := A.segmentGridEdgeIndex i s
  let upper := A.segmentGridEdgeIndex i t
  let hrows : lower.succ = upper.castSucc :=
    A.segmentGridEdgeIndex_succ_eq_castSucc i s t hshared
  let c := (letters.reverse.get i).1
  by_cases hs : A.subdivision.label col lower = c
  · by_cases ht : A.subdivision.label col upper = c
    · rw [BinaryOpenCoverSquareSubdivision.verticalInternalEdgeTransitions,
        dite_eq_left (hs.trans ht.symm)]
      exact A.leftBoundaryCellToLetterTransitions_adjacent_of_both_eq
        hxU hxV hUV hU hV letters Fhom i s t hshared hs ht
    · have hswitch : A.subdivision.label col lower ≠
          A.subdivision.label col upper := by
        intro h
        exact ht (h.symm.trans hs)
      rw [BinaryOpenCoverSquareSubdivision.verticalInternalEdgeTransitions,
        dite_eq_right hswitch]
      exact A.leftBoundaryCellToLetterTransitions_adjacent_of_lower_eq
        hxU hxV hUV hU hV letters Fhom i s t hshared hs ht
  · by_cases ht : A.subdivision.label col upper = c
    · have hswitch : A.subdivision.label col lower ≠
          A.subdivision.label col upper := by
        intro h
        exact hs (h.trans ht)
      rw [BinaryOpenCoverSquareSubdivision.verticalInternalEdgeTransitions,
        dite_eq_right hswitch]
      exact A.leftBoundaryCellToLetterTransitions_adjacent_of_upper_eq
        hxU hxV hUV hU hV letters Fhom i s t hshared hs ht
    · have hlabel : A.subdivision.label col lower =
          A.subdivision.label col upper := by
        cases hc : c <;>
          cases hsl : A.subdivision.label col lower <;>
          cases htu : A.subdivision.label col upper <;>
          simp_all
      rw [BinaryOpenCoverSquareSubdivision.verticalInternalEdgeTransitions,
        dite_eq_left hlabel]
      exact A.leftBoundaryCellToLetterTransitions_adjacent_of_common_ne
        hxU hxV hUV hU hV letters Fhom i s t hshared hs ht hlabel

end PathConcatAlignedSquareSubdivision

end SandronesLibrary.Topology
