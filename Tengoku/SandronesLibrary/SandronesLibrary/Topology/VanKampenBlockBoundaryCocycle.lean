/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.VanKampenCombinedFrames

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# van Kampen 相邻字母 blocks 的边界 cocycle

本文件识别每个输入 letter block 的首末左边界网格顶点为公共基点，并证明相邻 blocks 的
cell-to-letter transitions 与真实竖直网格 transition 在该共享断点满足 cocycle。它还记录两侧 letter
connectors 送回环境空间后的逐点相等。

本文件不执行 block 或完整左边界的有限 telescope，也不证明 kernel 平凡、规范同态单射或最终
van Kampen 同构。

当前条目：`topology.fundamental-group.van-kampen-block-boundary-cocycle`。
-/

open Set
open scoped unitInterval

noncomputable section

namespace SandronesLibrary.Topology

variable {X : Type*} [TopologicalSpace X]

/-- 一个 block 最后一条左边界边的环境空间终点就是指定基点。

> **Entry**: topology.fundamental-group.van-kampen-block-boundary-cocycle
@isnad1 id=other.4h8v.s9.ee45f284dceb from=translated src=- shape=30cf041c vocab=c603175e
-/
theorem PathConcatAlignedSquareSubdivision.leftBoundaryBlockLastVertex_eq_basepoint
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (Fhom : Path.Homotopy
      (binaryVanKampenLetterConcatLoop hxU hxV letters) (Path.refl x₀))
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V
      letters.reverse.length)
    (i : Fin letters.reverse.length) :
    let L := pathConcatSegmentGridLength letters.reverse.length A.factor i
    let hL := pathConcatSegmentGridLength_pos letters.reverse.length A.factor
      A.factor_pos i
    squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
      A.subdivision.steps_pos 0
        (A.segmentGridEdgeIndex i (finLastOfPos L hL)).succ = x₀ := by
  dsimp only
  let L := pathConcatSegmentGridLength letters.reverse.length A.factor i
  let hL := pathConcatSegmentGridLength_pos letters.reverse.length A.factor
    A.factor_pos i
  have h := A.coe_leftBoundaryBlockLastLetterEnd
    hxU hxV hU hV letters Fhom i (1 : unitInterval)
  simpa [PathConcatAlignedSquareSubdivision.leftBoundaryAlignedGridEdgeLetterEnd,
    Path.cast_coe] using h

/-- The ambient endpoint vertex of a block's first left-boundary edge is the
distinguished basepoint.
@isnad1 id=other.4h8v.s9.112cc1606406 from=translated src=- shape=a9691fa1 vocab=eb20a2ed
-/
theorem PathConcatAlignedSquareSubdivision.leftBoundaryBlockFirstVertex_eq_basepoint
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (Fhom : Path.Homotopy
      (binaryVanKampenLetterConcatLoop hxU hxV letters) (Path.refl x₀))
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V
      letters.reverse.length)
    (j : Fin letters.reverse.length) :
    let hL := pathConcatSegmentGridLength_pos letters.reverse.length A.factor
      A.factor_pos j
    squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
      A.subdivision.steps_pos 0
        (A.segmentGridEdgeIndex j ⟨0, hL⟩).castSucc = x₀ := by
  dsimp only
  have h := A.coe_leftBoundaryBlockFirstLetterStart
    hxU hxV hU hV letters Fhom j (1 : unitInterval)
  simpa [PathConcatAlignedSquareSubdivision.leftBoundaryAlignedGridEdgeLetterStart,
    Path.cast_coe] using h

/-- Across two adjacent input-letter blocks, the two cell-to-letter transitions
and the actual vertical grid transition satisfy the shared-vertex cocycle.
@isnad1 id=other.6h9v.s10.8d6860533dd0 from=translated src=- shape=97ea8cc8 vocab=1f8382a9
-/
theorem PathConcatAlignedSquareSubdivision.leftBoundaryBlockTransitions_cocycle
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
    let si := finLastOfPos Li hi
    let sj : Fin (pathConcatSegmentGridLength letters.reverse.length A.factor j) :=
      ⟨0, hj⟩
    let lower := A.segmentGridEdgeIndex i si
    let upper := A.segmentGridEdgeIndex j sj
    let col : Fin A.subdivision.steps := ⟨0, A.subdivision.steps_pos⟩
    let lowerT := A.leftBoundaryCellToLetterTransitions
      hxU hxV hUV hU hV letters Fhom i si
    let upperT := A.leftBoundaryCellToLetterTransitions
      hxU hxV hUV hU hV letters Fhom j sj
    let vertical := A.subdivision.verticalInternalEdgeTransitions
      hxU hxV hUV hU hV col lower upper
        (A.segmentGridEdgeIndex_block_adjacent i j hshared)
    lowerT.endChange = upperT.startChange * vertical.startChange := by
  dsimp only
  let Li := pathConcatSegmentGridLength letters.reverse.length A.factor i
  let hi := pathConcatSegmentGridLength_pos letters.reverse.length A.factor
    A.factor_pos i
  let hj := pathConcatSegmentGridLength_pos letters.reverse.length A.factor
    A.factor_pos j
  let si := finLastOfPos Li hi
  let sj : Fin (pathConcatSegmentGridLength letters.reverse.length A.factor j) :=
    ⟨0, hj⟩
  let lower := A.segmentGridEdgeIndex i si
  let upper := A.segmentGridEdgeIndex j sj
  let col : Fin A.subdivision.steps := ⟨0, A.subdivision.steps_pos⟩
  let z₀ := binaryOpenCoverIntersectionBasepoint hxU hxV
  have hlowerVertex : squareGridVertex (pathHomotopySquare Fhom)
      A.subdivision.steps A.subdivision.steps_pos 0 lower.succ = x₀ := by
    exact A.leftBoundaryBlockLastVertex_eq_basepoint
      hxU hxV hU hV letters Fhom i
  have hupperVertex : squareGridVertex (pathHomotopySquare Fhom)
      A.subdivision.steps A.subdivision.steps_pos 0 upper.castSucc = x₀ := by
    exact A.leftBoundaryBlockFirstVertex_eq_basepoint
      hxU hxV hU hV letters Fhom j
  have hlowerCell : binaryOpenCoverIntersectionToPiece U V
      (A.subdivision.label col lower) z₀ =
      ⟨squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
          A.subdivision.steps_pos 0 lower.succ,
        by simpa [col, lower, si] using
          A.leftBoundaryAlignedGridEdge_mem_cellPiece
            hxU hxV letters Fhom i si 1⟩ := by
    apply binaryOpenCoverIntersectionToPiece_basepoint_eq_of_coe hxU hxV
    exact hlowerVertex
  have hlowerLetter : binaryOpenCoverIntersectionToPiece U V
      (letters.reverse.get i).1 z₀ =
      ⟨squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
          A.subdivision.steps_pos 0 lower.succ,
        by simpa [lower, si] using
          A.leftBoundaryAlignedGridEdge_mem_letterPiece
            hxU hxV letters Fhom i si 1⟩ := by
    apply binaryOpenCoverIntersectionToPiece_basepoint_eq_of_coe hxU hxV
    exact hlowerVertex
  have hupperCell : binaryOpenCoverIntersectionToPiece U V
      (A.subdivision.label col upper) z₀ =
      ⟨squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
          A.subdivision.steps_pos 0 upper.castSucc,
        by simpa [col, upper, sj] using
          A.leftBoundaryAlignedGridEdge_mem_cellPiece
            hxU hxV letters Fhom j sj 0⟩ := by
    apply binaryOpenCoverIntersectionToPiece_basepoint_eq_of_coe hxU hxV
    exact hupperVertex
  have hupperLetter : binaryOpenCoverIntersectionToPiece U V
      (letters.reverse.get j).1 z₀ =
      ⟨squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
          A.subdivision.steps_pos 0 upper.castSucc,
        by simpa [upper, sj] using
          A.leftBoundaryAlignedGridEdge_mem_letterPiece
            hxU hxV letters Fhom j sj 0⟩ := by
    apply binaryOpenCoverIntersectionToPiece_basepoint_eq_of_coe hxU hxV
    exact hupperVertex
  have hlowerGrid : binaryOpenCoverIntersectionToPiece U V
      (A.subdivision.label col lower) z₀ =
      A.subdivision.gridCellVertexInPiece col lower 0 1 := by
    apply binaryOpenCoverIntersectionToPiece_basepoint_eq_of_coe hxU hxV
    have hone : unitIntervalMeshPoint 1 unitSquareOnePos (1 : Fin 2) = 1 := by
      simpa using unitIntervalMeshPoint_last 1 unitSquareOnePos
    simpa [BinaryOpenCoverSquareSubdivision.gridCellVertexInPiece,
      BinaryOpenCoverSquareSubdivision.gridCellMapInPiece,
      unitSquareGridVertex, unitSquareCellPoint, squareGridVertex, col,
      Set.Icc.convexComb_one, hone] using
        hlowerVertex
  have hupperGrid : binaryOpenCoverIntersectionToPiece U V
      (A.subdivision.label col upper) z₀ =
      A.subdivision.gridCellVertexInPiece col upper 0 0 := by
    apply binaryOpenCoverIntersectionToPiece_basepoint_eq_of_coe hxU hxV
    simpa [BinaryOpenCoverSquareSubdivision.gridCellVertexInPiece,
      BinaryOpenCoverSquareSubdivision.gridCellMapInPiece,
      unitSquareGridVertex, unitSquareCellPoint, squareGridVertex, col,
      Set.Icc.convexComb_zero] using
        hupperVertex
  let lowerT := A.leftBoundaryCellToLetterTransitions
    hxU hxV hUV hU hV letters Fhom i si
  let upperT := A.leftBoundaryCellToLetterTransitions
    hxU hxV hUV hU hV letters Fhom j sj
  let vertical := A.subdivision.verticalInternalEdgeTransitions
    hxU hxV hUV hU hV col lower upper
      (A.segmentGridEdgeIndex_block_adjacent i j hshared)
  have hlower := A.leftBoundaryCellToLetterTransitions_end_eq_intersectionPotentials
    hxU hxV hUV hU hV letters Fhom i si z₀ hlowerCell hlowerLetter
  dsimp only at hlower
  rw [A.leftBoundaryCellEndPotential_eq_gridCellPotential
    hxU hxV hUV hU hV letters Fhom i si z₀ hlowerCell hlowerGrid] at hlower
  have hupper := A.leftBoundaryCellToLetterTransitions_start_eq_intersectionPotentials
    hxU hxV hUV hU hV letters Fhom j sj z₀ hupperCell hupperLetter
  dsimp only at hupper
  rw [A.leftBoundaryCellStartPotential_eq_gridCellPotential
    hxU hxV hUV hU hV letters Fhom j sj z₀ hupperCell hupperGrid] at hupper
  have hvertical :=
    A.subdivision.verticalInternalEdgeTransitions_start_eq_gridCellPotentials
      hxU hxV hUV hU hV col lower upper
        (A.segmentGridEdgeIndex_block_adjacent i j hshared)
        z₀ hlowerGrid hupperGrid
  have hletters :=
    binaryOpenCoverVertexPotentialFromIntersection_basepoint_eq_of_coe
      hxU hxV hUV (letters.reverse.get i).1 (letters.reverse.get j).1
      ⟨squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
          A.subdivision.steps_pos 0 lower.succ,
        by simpa [lower, si] using
          A.leftBoundaryAlignedGridEdge_mem_letterPiece
            hxU hxV letters Fhom i si 1⟩
      ⟨squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
          A.subdivision.steps_pos 0 upper.castSucc,
        by simpa [upper, sj] using
          A.leftBoundaryAlignedGridEdge_mem_letterPiece
            hxU hxV letters Fhom j sj 0⟩
      (A.leftBoundaryAlignedGridEdgeLetterEnd
        hxU hxV hU hV letters Fhom i si)
      (A.leftBoundaryAlignedGridEdgeLetterStart
        hxU hxV hU hV letters Fhom j sj)
      (A.coe_leftBoundaryBlockLastLetterEnd
        hxU hxV hU hV letters Fhom i)
      (A.coe_leftBoundaryBlockFirstLetterStart
        hxU hxV hU hV letters Fhom j)
      hlowerLetter hupperLetter
  apply edgeTransitions_cocycle_of_potentials
    (A.subdivision.gridCellVertexPotentialFromIntersection
      hxU hxV hUV hU hV z₀ col lower 0 1 hlowerGrid)
    (A.subdivision.gridCellVertexPotentialFromIntersection
      hxU hxV hUV hU hV z₀ col upper 0 0 hupperGrid)
    (binaryOpenCoverVertexPotentialFromIntersection hxU hxV hUV z₀
      (letters.reverse.get i).1
      ⟨squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
          A.subdivision.steps_pos 0 lower.succ,
        by simpa [lower, si] using
          A.leftBoundaryAlignedGridEdge_mem_letterPiece
            hxU hxV letters Fhom i si 1⟩
      (A.leftBoundaryAlignedGridEdgeLetterEnd
        hxU hxV hU hV letters Fhom i si) hlowerLetter)
    lowerT upperT vertical
  · exact hlower
  · rw [hletters]
    exact hupper
  · exact hvertical

/-- 相邻 blocks 在共享断点使用的两条 letter connector 即使标签不同，送回环境空间后仍逐点
相同；两者都是公共基点常值道路。
@isnad1 id=other.5h10v.s11.385ee9466e29 from=translated src=- shape=0c74d139 vocab=fafaefb6
-/
theorem PathConcatAlignedSquareSubdivision.coe_leftBoundaryBlockLetterConnectors_adjacent
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (Fhom : Path.Homotopy
      (binaryVanKampenLetterConcatLoop hxU hxV letters) (Path.refl x₀))
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V
      letters.reverse.length)
    (i j : Fin letters.reverse.length) (_hshared : i.succ = j.castSucc)
    (u : unitInterval) :
    let Li := pathConcatSegmentGridLength letters.reverse.length A.factor i
    let hi := pathConcatSegmentGridLength_pos letters.reverse.length A.factor
      A.factor_pos i
    let hj := pathConcatSegmentGridLength_pos letters.reverse.length A.factor
      A.factor_pos j
    ((A.leftBoundaryAlignedGridEdgeLetterEnd
        hxU hxV hU hV letters Fhom i (finLastOfPos Li hi)) u : X) =
      ((A.leftBoundaryAlignedGridEdgeLetterStart
        hxU hxV hU hV letters Fhom j ⟨0, hj⟩) u : X) := by
  dsimp only
  rw [A.coe_leftBoundaryBlockLastLetterEnd hxU hxV hU hV letters Fhom i u,
    A.coe_leftBoundaryBlockFirstLetterStart hxU hxV hU hV letters Fhom j u]

end SandronesLibrary.Topology
