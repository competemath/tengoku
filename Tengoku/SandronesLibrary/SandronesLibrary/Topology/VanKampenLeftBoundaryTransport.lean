/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.VanKampenLeftBoundaryEdge

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# van Kampen 左边界 cell-to-letter 逐边 transport

本文件为对齐零同伦方格左边界的每条真实细边构造从 cell 标签局部表示到输入 letter 标签局部表示
的 endpoint transitions。它统一同标签的 same-path comparison 与异标签的 dual-path comparison，
用 vertex potentials 刻画两端变化，并证明 cell factor 是 letter block factor 的非交换 rebase。

本文件不把相邻细边或相邻 blocks 的 transitions 相乘，不执行有限 telescope，也不证明 kernel
平凡、规范同态单射或最终 van Kampen 同构。

当前条目：`topology.fundamental-group.van-kampen-left-boundary-transport`。
-/

open Set
open scoped unitInterval

noncomputable section

namespace SandronesLibrary.Topology

variable {X : Type*} [TopologicalSpace X]

/-- 每条真实左边界细边从 cell 标签表示切换到固定 letter 标签表示所需的端点 transitions。

> **Entry**: topology.fundamental-group.van-kampen-left-boundary-transport-/
noncomputable def PathConcatAlignedSquareSubdivision.leftBoundaryCellToLetterTransitions
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (Fhom : Path.Homotopy
      (binaryVanKampenLetterConcatLoop hxU hxV letters) (Path.refl x₀))
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V
      letters.reverse.length)
    (i : Fin letters.reverse.length)
    (s : Fin (pathConcatSegmentGridLength letters.reverse.length A.factor i)) :
    EdgeTransitions (binaryVanKampenPushout U V hxU hxV) := by
  let q := A.leftBoundaryAlignedGridEdge hxU hxV letters Fhom i s
  let b := A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
    (A.segmentGridEdgeIndex i s)
  let c := (letters.reverse.get i).1
  let hb := A.leftBoundaryAlignedGridEdge_mem_cellPiece hxU hxV letters Fhom i s
  let hc := A.leftBoundaryAlignedGridEdge_mem_letterPiece hxU hxV letters Fhom i s
  let bStart := A.leftBoundaryAlignedGridEdgeCellStart
    hxU hxV hU hV letters Fhom i s
  let bEnd := A.leftBoundaryAlignedGridEdgeCellEnd
    hxU hxV hU hV letters Fhom i s
  let cStart := A.leftBoundaryAlignedGridEdgeLetterStart
    hxU hxV hU hV letters Fhom i s
  let cEnd := A.leftBoundaryAlignedGridEdgeLetterEnd
    hxU hxV hU hV letters Fhom i s
  if heq : b = c then
    let C := binaryOpenCoverSamePathConnectorComparison hxU hxV q hb hc heq
      bStart bEnd cStart cEnd
    exact
      { startChange := (Monoid.PushoutI.of b C.startChange)⁻¹
        endChange := (Monoid.PushoutI.of b C.endChange)⁻¹ }
  else
    let CB := binaryOpenCoverDualPathConnectorComparison hxU hxV hUV
      q hb hc heq hb bStart bEnd
    let CC := binaryOpenCoverDualPathConnectorComparison hxU hxV hUV
      q hb hc heq hc cStart cEnd
    exact
      { startChange := (Monoid.PushoutI.of c CC.startChange)⁻¹ *
          Monoid.PushoutI.of b CB.startChange
        endChange := (Monoid.PushoutI.of c CC.endChange)⁻¹ *
          Monoid.PushoutI.of b CB.endChange }

/-- cell 与 letter 标签不同时，逐边起点 transition 是两侧统一 vertex potentials 之比。-/
theorem PathConcatAlignedSquareSubdivision.leftBoundaryCellToLetterTransitions_start_potential_of_ne
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (Fhom : Path.Homotopy
      (binaryVanKampenLetterConcatLoop hxU hxV letters) (Path.refl x₀))
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V
      letters.reverse.length)
    (i : Fin letters.reverse.length)
    (s : Fin (pathConcatSegmentGridLength letters.reverse.length A.factor i))
    (hne : A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
      (A.segmentGridEdgeIndex i s) ≠ (letters.reverse.get i).1) :
    let q := A.leftBoundaryAlignedGridEdge hxU hxV letters Fhom i s
    let b := A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
      (A.segmentGridEdgeIndex i s)
    let c := (letters.reverse.get i).1
    let hb := A.leftBoundaryAlignedGridEdge_mem_cellPiece
      hxU hxV letters Fhom i s
    let hc := A.leftBoundaryAlignedGridEdge_mem_letterPiece
      hxU hxV letters Fhom i s
    let CB := binaryOpenCoverDualPathConnectorComparison hxU hxV hUV
      q hb hc hne hb
      (A.leftBoundaryAlignedGridEdgeCellStart
        hxU hxV hU hV letters Fhom i s)
      (A.leftBoundaryAlignedGridEdgeCellEnd
        hxU hxV hU hV letters Fhom i s)
    let CC := binaryOpenCoverDualPathConnectorComparison hxU hxV hUV
      q hb hc hne hc
      (A.leftBoundaryAlignedGridEdgeLetterStart
        hxU hxV hU hV letters Fhom i s)
      (A.leftBoundaryAlignedGridEdgeLetterEnd
        hxU hxV hU hV letters Fhom i s)
    let T := A.leftBoundaryCellToLetterTransitions
      hxU hxV hUV hU hV letters Fhom i s
    T.startChange = transitionFromPotentials
      ((Monoid.PushoutI.of b CB.startChange :
        binaryVanKampenPushout U V hxU hxV)⁻¹)
      ((Monoid.PushoutI.of c CC.startChange :
        binaryVanKampenPushout U V hxU hxV)⁻¹) := by
  dsimp only
  rw [PathConcatAlignedSquareSubdivision.leftBoundaryCellToLetterTransitions,
    dite_eq_right hne]
  simp [transitionFromPotentials]

/-- cell 与 letter 标签不同时，逐边终点 transition 是对应终点 potentials 之比。-/
theorem PathConcatAlignedSquareSubdivision.leftBoundaryCellToLetterTransitions_end_potential_of_ne
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (Fhom : Path.Homotopy
      (binaryVanKampenLetterConcatLoop hxU hxV letters) (Path.refl x₀))
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V
      letters.reverse.length)
    (i : Fin letters.reverse.length)
    (s : Fin (pathConcatSegmentGridLength letters.reverse.length A.factor i))
    (hne : A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
      (A.segmentGridEdgeIndex i s) ≠ (letters.reverse.get i).1) :
    let q := A.leftBoundaryAlignedGridEdge hxU hxV letters Fhom i s
    let b := A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
      (A.segmentGridEdgeIndex i s)
    let c := (letters.reverse.get i).1
    let hb := A.leftBoundaryAlignedGridEdge_mem_cellPiece
      hxU hxV letters Fhom i s
    let hc := A.leftBoundaryAlignedGridEdge_mem_letterPiece
      hxU hxV letters Fhom i s
    let CB := binaryOpenCoverDualPathConnectorComparison hxU hxV hUV
      q hb hc hne hb
      (A.leftBoundaryAlignedGridEdgeCellStart
        hxU hxV hU hV letters Fhom i s)
      (A.leftBoundaryAlignedGridEdgeCellEnd
        hxU hxV hU hV letters Fhom i s)
    let CC := binaryOpenCoverDualPathConnectorComparison hxU hxV hUV
      q hb hc hne hc
      (A.leftBoundaryAlignedGridEdgeLetterStart
        hxU hxV hU hV letters Fhom i s)
      (A.leftBoundaryAlignedGridEdgeLetterEnd
        hxU hxV hU hV letters Fhom i s)
    let T := A.leftBoundaryCellToLetterTransitions
      hxU hxV hUV hU hV letters Fhom i s
    T.endChange = transitionFromPotentials
      ((Monoid.PushoutI.of b CB.endChange :
        binaryVanKampenPushout U V hxU hxV)⁻¹)
      ((Monoid.PushoutI.of c CC.endChange :
        binaryVanKampenPushout U V hxU hxV)⁻¹) := by
  dsimp only
  rw [PathConcatAlignedSquareSubdivision.leftBoundaryCellToLetterTransitions,
    dite_eq_right hne]
  simp [transitionFromPotentials]

namespace PathConcatAlignedSquareSubdivision

/-- 若一条左边界细边的终点已知属于交集，则其 cell-to-letter 终点 transition 可无条件统一写成
该交集顶点处 cell connector potential 与 letter connector potential 的比值。-/
theorem leftBoundaryCellToLetterTransitions_end_eq_intersectionPotentials
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (Fhom : Path.Homotopy
      (binaryVanKampenLetterConcatLoop hxU hxV letters) (Path.refl x₀))
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V
      letters.reverse.length)
    (i : Fin letters.reverse.length)
    (s : Fin (pathConcatSegmentGridLength letters.reverse.length A.factor i))
    (z : ↥(U ∩ V))
    (hcell : binaryOpenCoverIntersectionToPiece U V
        (A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
          (A.segmentGridEdgeIndex i s)) z =
      ⟨squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
          A.subdivision.steps_pos 0 (A.segmentGridEdgeIndex i s).succ,
        by simpa using
          A.leftBoundaryAlignedGridEdge_mem_cellPiece hxU hxV letters Fhom i s 1⟩)
    (hletter : binaryOpenCoverIntersectionToPiece U V
        (letters.reverse.get i).1 z =
      ⟨squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
          A.subdivision.steps_pos 0 (A.segmentGridEdgeIndex i s).succ,
        by simpa using
          A.leftBoundaryAlignedGridEdge_mem_letterPiece hxU hxV letters Fhom i s 1⟩) :
    let b := A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
      (A.segmentGridEdgeIndex i s)
    let c := (letters.reverse.get i).1
    let wb : binaryOpenCoverPiece U V b :=
      ⟨squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
          A.subdivision.steps_pos 0 (A.segmentGridEdgeIndex i s).succ,
        by simpa using
          A.leftBoundaryAlignedGridEdge_mem_cellPiece hxU hxV letters Fhom i s 1⟩
    let wc : binaryOpenCoverPiece U V c :=
      ⟨squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
          A.subdivision.steps_pos 0 (A.segmentGridEdgeIndex i s).succ,
        by
          change squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
            A.subdivision.steps_pos 0 (A.segmentGridEdgeIndex i s).succ ∈
              binaryOpenCoverPiece U V (letters.reverse.get i).1
          simpa using A.leftBoundaryAlignedGridEdge_mem_letterPiece
            hxU hxV letters Fhom i s 1⟩
    let T := A.leftBoundaryCellToLetterTransitions
      hxU hxV hUV hU hV letters Fhom i s
    T.endChange = transitionFromPotentials
      (binaryOpenCoverVertexPotentialFromIntersection hxU hxV hUV z b wb
        (A.leftBoundaryAlignedGridEdgeCellEnd
          hxU hxV hU hV letters Fhom i s) hcell)
      (binaryOpenCoverVertexPotentialFromIntersection hxU hxV hUV z c wc
        (A.leftBoundaryAlignedGridEdgeLetterEnd
          hxU hxV hU hV letters Fhom i s) hletter) := by
  dsimp only
  let b := A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
    (A.segmentGridEdgeIndex i s)
  let c := (letters.reverse.get i).1
  have hzval : (z : X) =
      squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
        A.subdivision.steps_pos 0 (A.segmentGridEdgeIndex i s).succ := by
    have hz := congrArg
      (fun w : binaryOpenCoverPiece U V
        (A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
          (A.segmentGridEdgeIndex i s)) => (w : X)) hcell
    simpa only [coe_binaryOpenCoverIntersectionToPiece] using hz
  by_cases heq : b = c
  · rw [PathConcatAlignedSquareSubdivision.leftBoundaryCellToLetterTransitions,
      dite_eq_left heq]
    let C := binaryOpenCoverSamePathConnectorComparison hxU hxV
      (A.leftBoundaryAlignedGridEdge hxU hxV letters Fhom i s)
      (A.leftBoundaryAlignedGridEdge_mem_cellPiece hxU hxV letters Fhom i s)
      (A.leftBoundaryAlignedGridEdge_mem_letterPiece hxU hxV letters Fhom i s)
      heq
      (A.leftBoundaryAlignedGridEdgeCellStart
        hxU hxV hU hV letters Fhom i s)
      (A.leftBoundaryAlignedGridEdgeCellEnd
        hxU hxV hU hV letters Fhom i s)
      (A.leftBoundaryAlignedGridEdgeLetterStart
        hxU hxV hU hV letters Fhom i s)
      (A.leftBoundaryAlignedGridEdgeLetterEnd
        hxU hxV hU hV letters Fhom i s)
    have hCtarget : C.edgeTarget =
        (⟨squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
            A.subdivision.steps_pos 0 (A.segmentGridEdgeIndex i s).succ,
          by
            change squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
              A.subdivision.steps_pos 0 (A.segmentGridEdgeIndex i s).succ ∈
                binaryOpenCoverPiece U V
                  (A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
                    (A.segmentGridEdgeIndex i s))
            simpa using (A.leftBoundaryAlignedGridEdge_mem_cellPiece
              hxU hxV letters Fhom i s 1)⟩ : binaryOpenCoverPiece U V b) := by
      exact binaryOpenCoverSamePathConnectorComparison_edgeTarget
        hxU hxV _ _ _ heq _ _ _ _
    have hzC : binaryOpenCoverIntersectionToPiece U V b z = C.edgeTarget := by
      rw [hCtarget]
      exact hcell
    change ((Monoid.PushoutI.of b C.endChange :
      binaryVanKampenPushout U V hxU hxV)⁻¹) = _
    rw [C.pushout_endChange_inv_eq_vertexPotentials hxU hxV hUV b z hzC]
    apply congrArg₂ transitionFromPotentials
    · apply binaryOpenCoverVertexPotentialFromIntersection_cast_label
        hxU hxV hUV b b rfl z z rfl C.edgeTarget
        ⟨squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
            A.subdivision.steps_pos 0 (A.segmentGridEdgeIndex i s).succ,
          by
            change squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
              A.subdivision.steps_pos 0 (A.segmentGridEdgeIndex i s).succ ∈
                binaryOpenCoverPiece U V
                  (A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
                    (A.segmentGridEdgeIndex i s))
            simpa using A.leftBoundaryAlignedGridEdge_mem_cellPiece
              hxU hxV letters Fhom i s 1⟩
      · exact congrArg
          (fun w : binaryOpenCoverPiece U V b => (w : X)) hCtarget
      · intro u
        exact coe_binaryOpenCoverSamePathConnectorComparison_leftEnd
          hxU hxV _ _ _ heq _ _ _ _ u
    · apply binaryOpenCoverVertexPotentialFromIntersection_cast_label
        hxU hxV hUV b c heq z z rfl C.edgeTarget
        ⟨squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
            A.subdivision.steps_pos 0 (A.segmentGridEdgeIndex i s).succ,
          by
            change squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
              A.subdivision.steps_pos 0 (A.segmentGridEdgeIndex i s).succ ∈
                binaryOpenCoverPiece U V (letters.reverse.get i).1
            simpa using A.leftBoundaryAlignedGridEdge_mem_letterPiece
              hxU hxV letters Fhom i s 1⟩
      · exact congrArg
          (fun w : binaryOpenCoverPiece U V b => (w : X)) hCtarget
      · intro u
        exact coe_binaryOpenCoverSamePathConnectorComparison_rightEnd
          hxU hxV _ _ _ heq _ _ _ _ u
  · rw [A.leftBoundaryCellToLetterTransitions_end_potential_of_ne
      hxU hxV hUV hU hV letters Fhom i s heq]
    rw [binaryOpenCoverDualPathConnectorComparison_endPotential_eq,
      binaryOpenCoverDualPathConnectorComparison_endPotential_eq]
    congr 1 <;>
      apply binaryOpenCoverVertexPotentialFromIntersection_cast
        hxU hxV hUV <;>
      first
      | apply Subtype.ext
        exact hzval.symm
      | rfl

/-- 上一定理的起点版本。-/
theorem leftBoundaryCellToLetterTransitions_start_eq_intersectionPotentials
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (Fhom : Path.Homotopy
      (binaryVanKampenLetterConcatLoop hxU hxV letters) (Path.refl x₀))
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V
      letters.reverse.length)
    (i : Fin letters.reverse.length)
    (s : Fin (pathConcatSegmentGridLength letters.reverse.length A.factor i))
    (z : ↥(U ∩ V))
    (hcell : binaryOpenCoverIntersectionToPiece U V
        (A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
          (A.segmentGridEdgeIndex i s)) z =
      ⟨squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
          A.subdivision.steps_pos 0 (A.segmentGridEdgeIndex i s).castSucc,
        by simpa using
          A.leftBoundaryAlignedGridEdge_mem_cellPiece hxU hxV letters Fhom i s 0⟩)
    (hletter : binaryOpenCoverIntersectionToPiece U V
        (letters.reverse.get i).1 z =
      ⟨squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
          A.subdivision.steps_pos 0 (A.segmentGridEdgeIndex i s).castSucc,
        by simpa using
          A.leftBoundaryAlignedGridEdge_mem_letterPiece hxU hxV letters Fhom i s 0⟩) :
    let b := A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
      (A.segmentGridEdgeIndex i s)
    let c := (letters.reverse.get i).1
    let wb : binaryOpenCoverPiece U V b :=
      ⟨squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
          A.subdivision.steps_pos 0 (A.segmentGridEdgeIndex i s).castSucc,
        by simpa using
          A.leftBoundaryAlignedGridEdge_mem_cellPiece hxU hxV letters Fhom i s 0⟩
    let wc : binaryOpenCoverPiece U V c :=
      ⟨squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
          A.subdivision.steps_pos 0 (A.segmentGridEdgeIndex i s).castSucc,
        by
          change squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
            A.subdivision.steps_pos 0 (A.segmentGridEdgeIndex i s).castSucc ∈
              binaryOpenCoverPiece U V (letters.reverse.get i).1
          simpa using A.leftBoundaryAlignedGridEdge_mem_letterPiece
            hxU hxV letters Fhom i s 0⟩
    let T := A.leftBoundaryCellToLetterTransitions
      hxU hxV hUV hU hV letters Fhom i s
    T.startChange = transitionFromPotentials
      (binaryOpenCoverVertexPotentialFromIntersection hxU hxV hUV z b wb
        (A.leftBoundaryAlignedGridEdgeCellStart
          hxU hxV hU hV letters Fhom i s) hcell)
      (binaryOpenCoverVertexPotentialFromIntersection hxU hxV hUV z c wc
        (A.leftBoundaryAlignedGridEdgeLetterStart
          hxU hxV hU hV letters Fhom i s) hletter) := by
  dsimp only
  let b := A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
    (A.segmentGridEdgeIndex i s)
  let c := (letters.reverse.get i).1
  have hzval : (z : X) =
      squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
        A.subdivision.steps_pos 0 (A.segmentGridEdgeIndex i s).castSucc := by
    have hz := congrArg
      (fun w : binaryOpenCoverPiece U V
        (A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
          (A.segmentGridEdgeIndex i s)) => (w : X)) hcell
    simpa only [coe_binaryOpenCoverIntersectionToPiece] using hz
  by_cases heq : b = c
  · rw [PathConcatAlignedSquareSubdivision.leftBoundaryCellToLetterTransitions,
      dite_eq_left heq]
    let C := binaryOpenCoverSamePathConnectorComparison hxU hxV
      (A.leftBoundaryAlignedGridEdge hxU hxV letters Fhom i s)
      (A.leftBoundaryAlignedGridEdge_mem_cellPiece hxU hxV letters Fhom i s)
      (A.leftBoundaryAlignedGridEdge_mem_letterPiece hxU hxV letters Fhom i s)
      heq
      (A.leftBoundaryAlignedGridEdgeCellStart
        hxU hxV hU hV letters Fhom i s)
      (A.leftBoundaryAlignedGridEdgeCellEnd
        hxU hxV hU hV letters Fhom i s)
      (A.leftBoundaryAlignedGridEdgeLetterStart
        hxU hxV hU hV letters Fhom i s)
      (A.leftBoundaryAlignedGridEdgeLetterEnd
        hxU hxV hU hV letters Fhom i s)
    have hCsource : C.edgeSource =
        (⟨squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
            A.subdivision.steps_pos 0 (A.segmentGridEdgeIndex i s).castSucc,
          by
            change squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
              A.subdivision.steps_pos 0 (A.segmentGridEdgeIndex i s).castSucc ∈
                binaryOpenCoverPiece U V
                  (A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
                    (A.segmentGridEdgeIndex i s))
            simpa using (A.leftBoundaryAlignedGridEdge_mem_cellPiece
              hxU hxV letters Fhom i s 0)⟩ : binaryOpenCoverPiece U V b) := by
      exact binaryOpenCoverSamePathConnectorComparison_edgeSource
        hxU hxV _ _ _ heq _ _ _ _
    have hzC : binaryOpenCoverIntersectionToPiece U V b z = C.edgeSource := by
      rw [hCsource]
      exact hcell
    change ((Monoid.PushoutI.of b C.startChange :
      binaryVanKampenPushout U V hxU hxV)⁻¹) = _
    rw [C.pushout_startChange_inv_eq_vertexPotentials hxU hxV hUV b z hzC]
    apply congrArg₂ transitionFromPotentials
    · apply binaryOpenCoverVertexPotentialFromIntersection_cast_label
        hxU hxV hUV b b rfl z z rfl C.edgeSource
        ⟨squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
            A.subdivision.steps_pos 0 (A.segmentGridEdgeIndex i s).castSucc,
          by
            change squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
              A.subdivision.steps_pos 0 (A.segmentGridEdgeIndex i s).castSucc ∈
                binaryOpenCoverPiece U V
                  (A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
                    (A.segmentGridEdgeIndex i s))
            simpa using A.leftBoundaryAlignedGridEdge_mem_cellPiece
              hxU hxV letters Fhom i s 0⟩
      · exact congrArg
          (fun w : binaryOpenCoverPiece U V b => (w : X)) hCsource
      · intro u
        exact coe_binaryOpenCoverSamePathConnectorComparison_leftStart
          hxU hxV _ _ _ heq _ _ _ _ u
    · apply binaryOpenCoverVertexPotentialFromIntersection_cast_label
        hxU hxV hUV b c heq z z rfl C.edgeSource
        ⟨squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
            A.subdivision.steps_pos 0 (A.segmentGridEdgeIndex i s).castSucc,
          by
            change squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
              A.subdivision.steps_pos 0 (A.segmentGridEdgeIndex i s).castSucc ∈
                binaryOpenCoverPiece U V (letters.reverse.get i).1
            simpa using A.leftBoundaryAlignedGridEdge_mem_letterPiece
              hxU hxV letters Fhom i s 0⟩
      · exact congrArg
          (fun w : binaryOpenCoverPiece U V b => (w : X)) hCsource
      · intro u
        exact coe_binaryOpenCoverSamePathConnectorComparison_rightStart
          hxU hxV _ _ _ heq _ _ _ _ u
  · rw [A.leftBoundaryCellToLetterTransitions_start_potential_of_ne
      hxU hxV hUV hU hV letters Fhom i s heq]
    rw [binaryOpenCoverDualPathConnectorComparison_startPotential_eq,
      binaryOpenCoverDualPathConnectorComparison_startPotential_eq]
    congr 1 <;>
      apply binaryOpenCoverVertexPotentialFromIntersection_cast
        hxU hxV hUV <;>
      first
      | apply Subtype.ext
        exact hzval.symm
      | rfl

end PathConcatAlignedSquareSubdivision

/-- 左边界细边实际 cell 终点 connector 的交集 potential，就是该格左上角的标准 grid-cell
potential；该桥不要求 cell 与 letter 标签不同。-/
theorem PathConcatAlignedSquareSubdivision.leftBoundaryCellEndPotential_eq_gridCellPotential
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (Fhom : Path.Homotopy
      (binaryVanKampenLetterConcatLoop hxU hxV letters) (Path.refl x₀))
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V
      letters.reverse.length)
    (i : Fin letters.reverse.length)
    (s : Fin (pathConcatSegmentGridLength letters.reverse.length A.factor i))
    (z : ↥(U ∩ V))
    (hzLocal : binaryOpenCoverIntersectionToPiece U V
        (A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
          (A.segmentGridEdgeIndex i s)) z =
      ⟨squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
          A.subdivision.steps_pos 0 (A.segmentGridEdgeIndex i s).succ,
        by simpa using
          A.leftBoundaryAlignedGridEdge_mem_cellPiece hxU hxV letters Fhom i s 1⟩)
    (hzGrid : binaryOpenCoverIntersectionToPiece U V
        (A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
          (A.segmentGridEdgeIndex i s)) z =
      A.subdivision.gridCellVertexInPiece ⟨0, A.subdivision.steps_pos⟩
        (A.segmentGridEdgeIndex i s) 0 1) :
    binaryOpenCoverVertexPotentialFromIntersection hxU hxV hUV z
        (A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
          (A.segmentGridEdgeIndex i s))
        ⟨squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
            A.subdivision.steps_pos 0 (A.segmentGridEdgeIndex i s).succ,
          by simpa using
            A.leftBoundaryAlignedGridEdge_mem_cellPiece hxU hxV letters Fhom i s 1⟩
        (A.leftBoundaryAlignedGridEdgeCellEnd
          hxU hxV hU hV letters Fhom i s) hzLocal =
      A.subdivision.gridCellVertexPotentialFromIntersection
        hxU hxV hUV hU hV z ⟨0, A.subdivision.steps_pos⟩
          (A.segmentGridEdgeIndex i s) 0 1 hzGrid := by
  rw [A.subdivision.gridCellVertexPotentialFromIntersection_eq_vertexPotential]
  apply binaryOpenCoverVertexPotentialFromIntersection_cast
    hxU hxV hUV
      (A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
        (A.segmentGridEdgeIndex i s))
  · rfl
  · apply Path.ext
    funext u
    apply Subtype.ext
    rw [Path.cast_coe]
    unfold PathConcatAlignedSquareSubdivision.leftBoundaryAlignedGridEdgeCellEnd
    rw [Path.cast_coe]
  · exact A.leftBoundaryAlignedGridEdge_cellTarget_eq
      hxU hxV letters Fhom i s

/-- 起点对称版本：实际 cell 起点 connector 的交集 potential 等于该格左下角标准 grid-cell
potential。-/
theorem PathConcatAlignedSquareSubdivision.leftBoundaryCellStartPotential_eq_gridCellPotential
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (Fhom : Path.Homotopy
      (binaryVanKampenLetterConcatLoop hxU hxV letters) (Path.refl x₀))
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V
      letters.reverse.length)
    (i : Fin letters.reverse.length)
    (s : Fin (pathConcatSegmentGridLength letters.reverse.length A.factor i))
    (z : ↥(U ∩ V))
    (hzLocal : binaryOpenCoverIntersectionToPiece U V
        (A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
          (A.segmentGridEdgeIndex i s)) z =
      ⟨squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
          A.subdivision.steps_pos 0 (A.segmentGridEdgeIndex i s).castSucc,
        by simpa using
          A.leftBoundaryAlignedGridEdge_mem_cellPiece hxU hxV letters Fhom i s 0⟩)
    (hzGrid : binaryOpenCoverIntersectionToPiece U V
        (A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
          (A.segmentGridEdgeIndex i s)) z =
      A.subdivision.gridCellVertexInPiece ⟨0, A.subdivision.steps_pos⟩
        (A.segmentGridEdgeIndex i s) 0 0) :
    binaryOpenCoverVertexPotentialFromIntersection hxU hxV hUV z
        (A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
          (A.segmentGridEdgeIndex i s))
        ⟨squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
            A.subdivision.steps_pos 0 (A.segmentGridEdgeIndex i s).castSucc,
          by simpa using
            A.leftBoundaryAlignedGridEdge_mem_cellPiece hxU hxV letters Fhom i s 0⟩
        (A.leftBoundaryAlignedGridEdgeCellStart
          hxU hxV hU hV letters Fhom i s) hzLocal =
      A.subdivision.gridCellVertexPotentialFromIntersection
        hxU hxV hUV hU hV z ⟨0, A.subdivision.steps_pos⟩
          (A.segmentGridEdgeIndex i s) 0 0 hzGrid := by
  rw [A.subdivision.gridCellVertexPotentialFromIntersection_eq_vertexPotential]
  apply binaryOpenCoverVertexPotentialFromIntersection_cast
    hxU hxV hUV
      (A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
        (A.segmentGridEdgeIndex i s))
  · rfl
  · apply Path.ext
    funext u
    apply Subtype.ext
    rw [Path.cast_coe]
    unfold PathConcatAlignedSquareSubdivision.leftBoundaryAlignedGridEdgeCellStart
    rw [Path.cast_coe]
  · exact A.leftBoundaryAlignedGridEdge_cellSource_eq
      hxU hxV letters Fhom i s

/-- 同标签比较对象的左侧送入 Pushout 后，就是显式左 connectors 的 corrected-loop。-/
private theorem binaryOpenCoverSamePathComparison_left_pushout_eq
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    {z w : X} {b c : Bool} (q : Path z w)
    (hb : ∀ t, q t ∈ binaryOpenCoverPiece U V b)
    (hc : ∀ t, q t ∈ binaryOpenCoverPiece U V c) (heq : b = c)
    (bStart : Path (binaryOpenCoverBasepoint hxU hxV b)
      (⟨z, by simpa using hb 0⟩ : binaryOpenCoverPiece U V b))
    (bEnd : Path (binaryOpenCoverBasepoint hxU hxV b)
      (⟨w, by simpa using hb 1⟩ : binaryOpenCoverPiece U V b))
    (cStart : Path (binaryOpenCoverBasepoint hxU hxV c)
      (⟨z, by simpa using hc 0⟩ : binaryOpenCoverPiece U V c))
    (cEnd : Path (binaryOpenCoverBasepoint hxU hxV c)
      (⟨w, by simpa using hc 1⟩ : binaryOpenCoverPiece U V c)) :
    let C := binaryOpenCoverSamePathConnectorComparison hxU hxV q hb hc heq
      bStart bEnd cStart cEnd
    (Monoid.PushoutI.of b C.leftElement : binaryVanKampenPushout U V hxU hxV) =
      Monoid.PushoutI.of b
        ((FundamentalGroup.fromPath ⟦Path.correctedLoop
          (x₀ := binaryOpenCoverBasepoint hxU hxV b) bStart
          (binaryOpenCoverPathInPiece q hb) bEnd⟧) :
          FundamentalGroup (binaryOpenCoverPiece U V b)
            (binaryOpenCoverBasepoint hxU hxV b)) := by
  cases b <;> cases c
  · simp [binaryOpenCoverSamePathConnectorComparison,
      CommonEdgeConnectorComparison.leftElement]
  · contradiction
  · contradiction
  · simp [binaryOpenCoverSamePathConnectorComparison,
      CommonEdgeConnectorComparison.leftElement]

/-- 同标签比较对象的右侧送入 Pushout 后，就是原标签 `c` 的显式右 connectors corrected-loop。-/
private theorem binaryOpenCoverSamePathComparison_right_pushout_eq
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    {z w : X} {b c : Bool} (q : Path z w)
    (hb : ∀ t, q t ∈ binaryOpenCoverPiece U V b)
    (hc : ∀ t, q t ∈ binaryOpenCoverPiece U V c) (heq : b = c)
    (bStart : Path (binaryOpenCoverBasepoint hxU hxV b)
      (⟨z, by simpa using hb 0⟩ : binaryOpenCoverPiece U V b))
    (bEnd : Path (binaryOpenCoverBasepoint hxU hxV b)
      (⟨w, by simpa using hb 1⟩ : binaryOpenCoverPiece U V b))
    (cStart : Path (binaryOpenCoverBasepoint hxU hxV c)
      (⟨z, by simpa using hc 0⟩ : binaryOpenCoverPiece U V c))
    (cEnd : Path (binaryOpenCoverBasepoint hxU hxV c)
      (⟨w, by simpa using hc 1⟩ : binaryOpenCoverPiece U V c)) :
    let C := binaryOpenCoverSamePathConnectorComparison hxU hxV q hb hc heq
      bStart bEnd cStart cEnd
    (Monoid.PushoutI.of b C.rightElement : binaryVanKampenPushout U V hxU hxV) =
      Monoid.PushoutI.of c
        ((FundamentalGroup.fromPath ⟦Path.correctedLoop
          (x₀ := binaryOpenCoverBasepoint hxU hxV c) cStart
          (binaryOpenCoverPathInPiece q hc) cEnd⟧) :
          FundamentalGroup (binaryOpenCoverPiece U V c)
            (binaryOpenCoverBasepoint hxU hxV c)) := by
  cases b <;> cases c
  · simp [binaryOpenCoverSamePathConnectorComparison,
      CommonEdgeConnectorComparison.rightElement]
  · contradiction
  · contradiction
  · simp [binaryOpenCoverSamePathConnectorComparison,
      CommonEdgeConnectorComparison.rightElement]

/-- 统一逐边关系：cell-label 的真实局部元素等于 letter-label 真实局部元素按上述 transitions
换连接后的结果。-/
theorem PathConcatAlignedSquareSubdivision.leftBoundaryCellToLetter_relation
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (Fhom : Path.Homotopy
      (binaryVanKampenLetterConcatLoop hxU hxV letters) (Path.refl x₀))
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V
      letters.reverse.length)
    (i : Fin letters.reverse.length)
    (s : Fin (pathConcatSegmentGridLength letters.reverse.length A.factor i)) :
    let b := A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
      (A.segmentGridEdgeIndex i s)
    let c := (letters.reverse.get i).1
    let T := A.leftBoundaryCellToLetterTransitions hxU hxV hUV hU hV
      letters Fhom i s
    (Monoid.PushoutI.of b
        (A.leftBoundaryAlignedGridEdgeCellElement hxU hxV hU hV
          letters Fhom i s) : binaryVanKampenPushout U V hxU hxV) =
      rebaseEdge T.startChange T.endChange
        (Monoid.PushoutI.of c
          (A.leftBoundaryAlignedGridEdgeLetterElement hxU hxV hU hV
            letters Fhom i s)) := by
  dsimp only
  let q := A.leftBoundaryAlignedGridEdge hxU hxV letters Fhom i s
  let b := A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
    (A.segmentGridEdgeIndex i s)
  let c := (letters.reverse.get i).1
  let hb := A.leftBoundaryAlignedGridEdge_mem_cellPiece hxU hxV letters Fhom i s
  let hc := A.leftBoundaryAlignedGridEdge_mem_letterPiece hxU hxV letters Fhom i s
  let bStart := A.leftBoundaryAlignedGridEdgeCellStart
    hxU hxV hU hV letters Fhom i s
  let bEnd := A.leftBoundaryAlignedGridEdgeCellEnd
    hxU hxV hU hV letters Fhom i s
  let cStart := A.leftBoundaryAlignedGridEdgeLetterStart
    hxU hxV hU hV letters Fhom i s
  let cEnd := A.leftBoundaryAlignedGridEdgeLetterEnd
    hxU hxV hU hV letters Fhom i s
  by_cases heq : b = c
  · rw [PathConcatAlignedSquareSubdivision.leftBoundaryCellToLetterTransitions,
      dite_eq_left heq]
    let C := binaryOpenCoverSamePathConnectorComparison hxU hxV q hb hc heq
      bStart bEnd cStart cEnd
    have h := binaryOpenCoverSamePath_localElements_pushout_rebase
      hxU hxV q hb hc heq bStart bEnd cStart cEnd
    have hL := binaryOpenCoverSamePathComparison_left_pushout_eq
      hxU hxV q hb hc heq bStart bEnd cStart cEnd
    have hR := binaryOpenCoverSamePathComparison_right_pushout_eq
      hxU hxV q hb hc heq bStart bEnd cStart cEnd
    dsimp only at h hL hR
    have hCell : (Monoid.PushoutI.of b
        (A.leftBoundaryAlignedGridEdgeCellElement hxU hxV hU hV
          letters Fhom i s) : binaryVanKampenPushout U V hxU hxV) =
        Monoid.PushoutI.of b
          ((FundamentalGroup.fromPath ⟦Path.correctedLoop
            (x₀ := binaryOpenCoverBasepoint hxU hxV b) bStart
            (binaryOpenCoverPathInPiece q hb) bEnd⟧) :
            FundamentalGroup (binaryOpenCoverPiece U V b)
              (binaryOpenCoverBasepoint hxU hxV b)) := by rfl
    have hLetter : (Monoid.PushoutI.of c
        (A.leftBoundaryAlignedGridEdgeLetterElement hxU hxV hU hV
          letters Fhom i s) : binaryVanKampenPushout U V hxU hxV) =
        Monoid.PushoutI.of c
          ((FundamentalGroup.fromPath ⟦Path.correctedLoop
            (x₀ := binaryOpenCoverBasepoint hxU hxV c) cStart
            (binaryOpenCoverPathInPiece q hc) cEnd⟧) :
            FundamentalGroup (binaryOpenCoverPiece U V c)
              (binaryOpenCoverBasepoint hxU hxV c)) := by rfl
    rw [hCell, ← hL, h, hR, hLetter]
  · rw [PathConcatAlignedSquareSubdivision.leftBoundaryCellToLetterTransitions,
      dite_eq_right heq]
    let CB := binaryOpenCoverDualPathConnectorComparison hxU hxV hUV
      q hb hc heq hb bStart bEnd
    let CC := binaryOpenCoverDualPathConnectorComparison hxU hxV hUV
      q hb hc heq hc cStart cEnd
    have h := binaryOpenCoverDualPath_localElements_pushout_rebase
      hxU hxV hUV q hb hc heq bStart bEnd cStart cEnd
    have hL : (Monoid.PushoutI.of b CB.rightElement :
        binaryVanKampenPushout U V hxU hxV) =
        Monoid.PushoutI.of b
          (A.leftBoundaryAlignedGridEdgeCellElement hxU hxV hU hV
            letters Fhom i s) := by rfl
    have hR : (Monoid.PushoutI.of c CC.rightElement :
        binaryVanKampenPushout U V hxU hxV) =
        Monoid.PushoutI.of c
          (A.leftBoundaryAlignedGridEdgeLetterElement hxU hxV hU hV
            letters Fhom i s) := by rfl
    dsimp only at h
    rw [← hL, h, hR]

/-- 上述统一关系改写到两套现有有限词真正使用的生成元。-/
theorem PathConcatAlignedSquareSubdivision.leftBoundaryCellEdgeToBlockFactor_relation
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (Fhom : Path.Homotopy
      (binaryVanKampenLetterConcatLoop hxU hxV letters) (Path.refl x₀))
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V
      letters.reverse.length)
    (i : Fin letters.reverse.length)
    (s : Fin (pathConcatSegmentGridLength letters.reverse.length A.factor i)) :
    let row := A.segmentGridEdgeIndex i s
    let b := A.subdivision.label ⟨0, A.subdivision.steps_pos⟩ row
    let c := (letters.reverse.get i).1
    let T := A.leftBoundaryCellToLetterTransitions hxU hxV hUV hU hV
      letters Fhom i s
    (Monoid.PushoutI.of b
        (A.subdivision.gridCellBasedVerticalEdgeInPiece hxU hxV hU hV
          ⟨0, A.subdivision.steps_pos⟩ row 0) :
      binaryVanKampenPushout U V hxU hxV) =
      rebaseEdge T.startChange T.endChange
        (Monoid.PushoutI.of c
          (FundamentalGroup.fromPath ⟦Path.correctedLoop
            (binaryVanKampenLetterBlockGridConnector hxU hxV hU hV letters
              A.factor A.factor_pos i s.castSucc)
            (binaryVanKampenLetterBlockGridEdgeInPiece hxU hxV letters
              A.factor A.factor_pos i s)
            (binaryVanKampenLetterBlockGridConnector hxU hxV hU hV letters
              A.factor A.factor_pos i s.succ)⟧)) := by
  dsimp only
  rw [← A.leftBoundaryAlignedGridEdgeCellElement_eq
      hxU hxV hU hV letters Fhom i s,
    ← A.leftBoundaryAlignedGridEdgeLetterElement_eq
      hxU hxV hU hV letters Fhom i s]
  exact A.leftBoundaryCellToLetter_relation
    hxU hxV hUV hU hV letters Fhom i s

end SandronesLibrary.Topology
