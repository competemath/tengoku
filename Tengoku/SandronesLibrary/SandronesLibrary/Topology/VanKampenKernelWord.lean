/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.VanKampenResidualGauge

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# van Kampen kernel 字母词

本文件用余规范消去证明全局首末 frame 相等，进而从整体 rebased 字母词为一恢复原字母词为一。
它处理规范同态 kernel 的核心非空词情形，并给出最终单射证明所需的常 connector 桥。
-/

open Set
open scoped unitInterval

noncomputable section

namespace SandronesLibrary.Topology

variable {X : Type*} [TopologicalSpace X]

/-- 对非空字母词，第二层 block chain 的终点是最后一个 block 最后一条细边的 combined frame。

> **Entry**: topology.fundamental-group.van-kampen-kernel-word-/
theorem PathConcatAlignedSquareSubdivision.leftBoundaryLetterBlockChain_end
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (Fhom : Path.Homotopy
      (binaryVanKampenLetterConcatLoop hxU hxV letters) (Path.refl x₀))
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V
      letters.reverse.length)
    (hn : 0 < letters.reverse.length) :
    let firstBlock : Fin letters.reverse.length := ⟨0, hn⟩
    let firstLengthPos := pathConcatSegmentGridLength_pos
      letters.reverse.length A.factor A.factor_pos firstBlock
    let lastBlock : Fin letters.reverse.length :=
      ⟨letters.reverse.length - 1, Nat.sub_lt hn Nat.zero_lt_one⟩
    let lastLength := pathConcatSegmentGridLength
      letters.reverse.length A.factor lastBlock
    let lastLengthPos := pathConcatSegmentGridLength_pos
      letters.reverse.length A.factor A.factor_pos lastBlock
    let start := A.leftBoundaryCombinedStartFrame
      hxU hxV hUV hU hV letters Fhom firstBlock ⟨0, firstLengthPos⟩
    edgeChainEnd start
        (A.leftBoundaryLetterBlockChain
          hxU hxV hUV hU hV letters Fhom) =
      A.leftBoundaryCombinedEndFrame
        hxU hxV hUV hU hV letters Fhom lastBlock
          (finLastOfPos lastLength lastLengthPos) := by
  dsimp only
  unfold PathConcatAlignedSquareSubdivision.leftBoundaryLetterBlockChain
  exact edgeChainEnd_ofFn_of_pos _ hn _ _ _

/-- 非空左边界词的全局起点 frame 与终点 frame 相等。证明把公共的 letter-side 基点 potential 与
沿同伦方形其余三边传播的 cell 余规范分开比较。

> **Entry**: topology.fundamental-group.van-kampen-kernel-word-/
theorem PathConcatAlignedSquareSubdivision.leftBoundaryGlobalCombinedFrames_eq
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (Fhom : Path.Homotopy
      (binaryVanKampenLetterConcatLoop hxU hxV letters) (Path.refl x₀))
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V
      letters.reverse.length)
    (hn : 0 < letters.reverse.length) :
    let firstBlock : Fin letters.reverse.length := ⟨0, hn⟩
    let firstLengthPos := pathConcatSegmentGridLength_pos
      letters.reverse.length A.factor A.factor_pos firstBlock
    let firstEdge : Fin (pathConcatSegmentGridLength
      letters.reverse.length A.factor firstBlock) := ⟨0, firstLengthPos⟩
    let lastBlock : Fin letters.reverse.length :=
      ⟨letters.reverse.length - 1, Nat.sub_lt hn Nat.zero_lt_one⟩
    let lastLength := pathConcatSegmentGridLength
      letters.reverse.length A.factor lastBlock
    let lastLengthPos := pathConcatSegmentGridLength_pos
      letters.reverse.length A.factor A.factor_pos lastBlock
    let lastEdge := finLastOfPos lastLength lastLengthPos
    A.leftBoundaryCombinedStartFrame
        hxU hxV hUV hU hV letters Fhom firstBlock firstEdge =
      A.leftBoundaryCombinedEndFrame
        hxU hxV hUV hU hV letters Fhom lastBlock lastEdge := by
  dsimp only
  let firstBlock : Fin letters.reverse.length := ⟨0, hn⟩
  let firstLengthPos := pathConcatSegmentGridLength_pos
    letters.reverse.length A.factor A.factor_pos firstBlock
  let firstEdge : Fin (pathConcatSegmentGridLength
      letters.reverse.length A.factor firstBlock) := ⟨0, firstLengthPos⟩
  let lastBlock : Fin letters.reverse.length :=
    ⟨letters.reverse.length - 1, Nat.sub_lt hn Nat.zero_lt_one⟩
  let lastLength := pathConcatSegmentGridLength
    letters.reverse.length A.factor lastBlock
  let lastLengthPos := pathConcatSegmentGridLength_pos
    letters.reverse.length A.factor A.factor_pos lastBlock
  let lastEdge := finLastOfPos lastLength lastLengthPos
  let first : Fin A.subdivision.steps := ⟨0, A.subdivision.steps_pos⟩
  let last : Fin A.subdivision.steps :=
    ⟨A.subdivision.steps - 1,
      Nat.sub_lt A.subdivision.steps_pos Nat.zero_lt_one⟩
  let z₀ := binaryOpenCoverIntersectionBasepoint hxU hxV
  have hfirstRow : A.segmentGridEdgeIndex firstBlock firstEdge = first := by
    exact A.segmentGridEdgeIndex_first hn
  have hlastRow : A.segmentGridEdgeIndex lastBlock lastEdge = last := by
    exact A.segmentGridEdgeIndex_last hn
  have hfirstFrame := congrArg (fun row : Fin A.subdivision.steps =>
      (A.subdivision.rightAnchoredGridRowFramesAt
        hxU hxV hUV hU hV row.val row.isLt first).bottomLeft) hfirstRow
  have hlastFrame := congrArg (fun row : Fin A.subdivision.steps =>
      (A.subdivision.rightAnchoredGridRowFramesAt
        hxU hxV hUV hU hV row.val row.isLt first).topLeft) hlastRow
  have hfirstVertex := A.leftBoundaryBlockFirstVertex_eq_basepoint
    hxU hxV hU hV letters Fhom firstBlock
  have hlastVertex := A.leftBoundaryBlockLastVertex_eq_basepoint
    hxU hxV hU hV letters Fhom lastBlock
  have hfirstCell : binaryOpenCoverIntersectionToPiece U V
      (A.subdivision.label first (A.segmentGridEdgeIndex firstBlock firstEdge)) z₀ =
      ⟨squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
          A.subdivision.steps_pos 0
            (A.segmentGridEdgeIndex firstBlock firstEdge).castSucc,
        by simpa [first, firstBlock, firstEdge] using
          A.leftBoundaryAlignedGridEdge_mem_cellPiece
            hxU hxV letters Fhom firstBlock firstEdge 0⟩ := by
    apply binaryOpenCoverIntersectionToPiece_basepoint_eq_of_coe hxU hxV
    exact hfirstVertex
  have hlastCell : binaryOpenCoverIntersectionToPiece U V
      (A.subdivision.label first (A.segmentGridEdgeIndex lastBlock lastEdge)) z₀ =
      ⟨squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
          A.subdivision.steps_pos 0
            (A.segmentGridEdgeIndex lastBlock lastEdge).succ,
        by simpa [first, lastBlock, lastEdge] using
          A.leftBoundaryAlignedGridEdge_mem_cellPiece
            hxU hxV letters Fhom lastBlock lastEdge 1⟩ := by
    apply binaryOpenCoverIntersectionToPiece_basepoint_eq_of_coe hxU hxV
    exact hlastVertex
  have hfirstLetter : binaryOpenCoverIntersectionToPiece U V
      (letters.reverse.get firstBlock).1 z₀ =
      ⟨squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
          A.subdivision.steps_pos 0
            (A.segmentGridEdgeIndex firstBlock firstEdge).castSucc,
        by simpa [firstBlock, firstEdge] using
          A.leftBoundaryAlignedGridEdge_mem_letterPiece
            hxU hxV letters Fhom firstBlock firstEdge 0⟩ := by
    apply binaryOpenCoverIntersectionToPiece_basepoint_eq_of_coe hxU hxV
    exact hfirstVertex
  have hlastLetter : binaryOpenCoverIntersectionToPiece U V
      (letters.reverse.get lastBlock).1 z₀ =
      ⟨squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
          A.subdivision.steps_pos 0
            (A.segmentGridEdgeIndex lastBlock lastEdge).succ,
        by simpa [lastBlock, lastEdge] using
          A.leftBoundaryAlignedGridEdge_mem_letterPiece
            hxU hxV letters Fhom lastBlock lastEdge 1⟩ := by
    apply binaryOpenCoverIntersectionToPiece_basepoint_eq_of_coe hxU hxV
    exact hlastVertex
  let hbottom := A.subdivision.gridCellVertexInPiece_bottom_eq_basepoint
    Fhom hxU hxV first 0
  let htop := A.subdivision.gridCellVertexInPiece_top_eq_basepoint
    Fhom hxU hxV first 0
  have hfirstGrid : binaryOpenCoverIntersectionToPiece U V
      (A.subdivision.label first (A.segmentGridEdgeIndex firstBlock firstEdge)) z₀ =
      A.subdivision.gridCellVertexInPiece first
        (A.segmentGridEdgeIndex firstBlock firstEdge) 0 0 := by
    rw [hfirstRow]
    exact A.subdivision.intersectionBasepoint_eq_gridCellVertexInPiece_of_eq_basepoint
      hxU hxV first first 0 0 hbottom
  have hlastGrid : binaryOpenCoverIntersectionToPiece U V
      (A.subdivision.label first (A.segmentGridEdgeIndex lastBlock lastEdge)) z₀ =
      A.subdivision.gridCellVertexInPiece first
        (A.segmentGridEdgeIndex lastBlock lastEdge) 0 1 := by
    rw [hlastRow]
    exact A.subdivision.intersectionBasepoint_eq_gridCellVertexInPiece_of_eq_basepoint
      hxU hxV first last 0 1 htop
  have hfirstTransition :=
    A.leftBoundaryCellToLetterTransitions_start_eq_intersectionPotentials
      hxU hxV hUV hU hV letters Fhom firstBlock firstEdge z₀
        hfirstCell hfirstLetter
  dsimp only at hfirstTransition
  rw [A.leftBoundaryCellStartPotential_eq_gridCellPotential
    hxU hxV hUV hU hV letters Fhom firstBlock firstEdge z₀
      hfirstCell hfirstGrid] at hfirstTransition
  have hlastTransition :=
    A.leftBoundaryCellToLetterTransitions_end_eq_intersectionPotentials
      hxU hxV hUV hU hV letters Fhom lastBlock lastEdge z₀
        hlastCell hlastLetter
  dsimp only at hlastTransition
  rw [A.leftBoundaryCellEndPotential_eq_gridCellPotential
    hxU hxV hUV hU hV letters Fhom lastBlock lastEdge z₀
      hlastCell hlastGrid] at hlastTransition
  have htarget :=
    binaryOpenCoverVertexPotentialFromIntersection_basepoint_eq_of_coe
      hxU hxV hUV
      (letters.reverse.get firstBlock).1 (letters.reverse.get lastBlock).1
      ⟨squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
          A.subdivision.steps_pos 0
            (A.segmentGridEdgeIndex firstBlock firstEdge).castSucc,
        by simpa [firstBlock, firstEdge] using
          A.leftBoundaryAlignedGridEdge_mem_letterPiece
            hxU hxV letters Fhom firstBlock firstEdge 0⟩
      ⟨squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
          A.subdivision.steps_pos 0
            (A.segmentGridEdgeIndex lastBlock lastEdge).succ,
        by simpa [lastBlock, lastEdge] using
          A.leftBoundaryAlignedGridEdge_mem_letterPiece
            hxU hxV letters Fhom lastBlock lastEdge 1⟩
      (A.leftBoundaryAlignedGridEdgeLetterStart
        hxU hxV hU hV letters Fhom firstBlock firstEdge)
      (A.leftBoundaryAlignedGridEdgeLetterEnd
        hxU hxV hU hV letters Fhom lastBlock lastEdge)
      (A.coe_leftBoundaryBlockFirstLetterStart
        hxU hxV hU hV letters Fhom firstBlock)
      (A.coe_leftBoundaryBlockLastLetterEnd
        hxU hxV hU hV letters Fhom lastBlock)
      hfirstLetter hlastLetter
  have hnormalized := A.subdivision.leftResidualGauge_bottom_eq_top
    Fhom hxU hxV hUV hU hV
  unfold PathConcatAlignedSquareSubdivision.leftBoundaryCombinedStartFrame
    PathConcatAlignedSquareSubdivision.leftBoundaryCombinedEndFrame
  dsimp only
  rw [hfirstTransition, hlastTransition]
  apply combinedFrame_eq_of_target_and_normalized
  · exact htarget
  · simp only [hfirstRow, hlastRow]
    rw [hfirstFrame, hlastFrame]
    unfold BinaryOpenCoverSquareSubdivision.gridCellBasepointPotential at hnormalized
    simpa [first, last, z₀] using hnormalized

/-- 若非空 Pushout 字母词对应的环境拼接环路零伦，则该字母词已经是 Pushout 的单位元。

> **Entry**: topology.fundamental-group.van-kampen-kernel-word-/
theorem PathConcatAlignedSquareSubdivision.letterWord_eq_one_of_homotopy_of_nonempty
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (Fhom : Path.Homotopy
      (binaryVanKampenLetterConcatLoop hxU hxV letters) (Path.refl x₀))
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V
      letters.reverse.length)
    (hn : 0 < letters.reverse.length) :
    binaryVanKampenLetterWord U V hxU hxV letters = 1 := by
  let firstBlock : Fin letters.reverse.length := ⟨0, hn⟩
  let firstLengthPos := pathConcatSegmentGridLength_pos
    letters.reverse.length A.factor A.factor_pos firstBlock
  let start := A.leftBoundaryCombinedStartFrame
    hxU hxV hUV hU hV letters Fhom firstBlock ⟨0, firstLengthPos⟩
  let chain := A.leftBoundaryLetterBlockChain
    hxU hxV hUV hU hV letters Fhom
  have hrebased := A.rebasedLetterWord_eq_one
    hxU hxV hUV hU hV letters Fhom hn
  dsimp only at hrebased
  have hend := A.leftBoundaryLetterBlockChain_end
    hxU hxV hUV hU hV letters Fhom hn
  dsimp only at hend
  have hframes := A.leftBoundaryGlobalCombinedFrames_eq
    hxU hxV hUV hU hV letters Fhom hn
  dsimp only at hframes
  change rebaseEdge start (edgeChainEnd start chain)
      (binaryVanKampenLetterWord U V hxU hxV letters) = 1 at hrebased
  rw [hend, ← hframes] at hrebased
  have hconjugated := congrArg (fun g =>
      start * g * start⁻¹) hrebased
  dsimp only [start, firstBlock, firstLengthPos] at hconjugated
  simpa [rebaseEdge, mul_assoc] using hconjugated

/-- 两端使用常 connector 不改变环路的基本群类；这是最终规范同态计算使用的桥。

> **Entry**: topology.fundamental-group.van-kampen-kernel-word-/
@[simp] theorem fundamentalGroup_fromPath_correctedLoop_refl
    {Y : Type*} [TopologicalSpace Y] {y : Y} (p : Path y y) :
    FundamentalGroup.fromPath
        ⟦Path.correctedLoop (Path.refl y) p (Path.refl y)⟧ =
      FundamentalGroup.fromPath ⟦p⟧ := by
  unfold Path.correctedLoop FundamentalGroup.fromPath FundamentalGroup.fromArrow
  simp

end SandronesLibrary.Topology
