/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.VanKampenPathGaugeComparison

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# van Kampen aligned 左边界细边

本文件把对齐零同伦方格的每条真实左边界细边同时提升到 cell 标签和输入字母标签对应的覆盖成员，
构造两侧 connectors 与局部基本群元素，并识别为既有 grid/block factors。它不建立统一 transition、
rebase、telescope、kernel、单射或最终 van Kampen 同构。

当前条目：

* `topology.fundamental-group.van-kampen-left-boundary-edge`。
-/

open Set
open scoped unitInterval

noncomputable section

namespace SandronesLibrary.Topology

variable {X : Type*} [TopologicalSpace X]

/-- 对齐同伦方形中一个输入 block 的第 `s` 条真实第零列竖边，作为环境道路。

> **Entry**: topology.fundamental-group.van-kampen-left-boundary-edge-/
def PathConcatAlignedSquareSubdivision.leftBoundaryAlignedGridEdge
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (Fhom : Path.Homotopy
      (binaryVanKampenLetterConcatLoop hxU hxV letters)
      (Path.refl x₀))
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V
      letters.reverse.length)
    (i : Fin letters.reverse.length)
    (s : Fin (pathConcatSegmentGridLength letters.reverse.length A.factor i)) :
    Path
      (squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
        A.subdivision.steps_pos 0 (A.segmentGridEdgeIndex i s).castSucc)
      (squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
        A.subdivision.steps_pos 0 (A.segmentGridEdgeIndex i s).succ) :=
  squareGridVerticalEdge (pathHomotopySquare Fhom) A.subdivision.steps
    A.subdivision.steps_pos 0 (A.segmentGridEdgeIndex i s)

/-- 该真实左边界细边属于其所在第零列小格的标签成员。-/
theorem PathConcatAlignedSquareSubdivision.leftBoundaryAlignedGridEdge_mem_cellPiece
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (Fhom : Path.Homotopy
      (binaryVanKampenLetterConcatLoop hxU hxV letters) (Path.refl x₀))
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V
      letters.reverse.length)
    (i : Fin letters.reverse.length)
    (s : Fin (pathConcatSegmentGridLength letters.reverse.length A.factor i))
    (t : unitInterval) :
    A.leftBoundaryAlignedGridEdge hxU hxV letters Fhom i s t ∈
      binaryOpenCoverPiece U V
        (A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
          (A.segmentGridEdgeIndex i s)) := by
  unfold PathConcatAlignedSquareSubdivision.leftBoundaryAlignedGridEdge
    squareGridVerticalEdge
  change pathHomotopySquare Fhom
      (unitIntervalMeshPoint A.subdivision.steps A.subdivision.steps_pos 0,
        Set.Icc.convexComb
          (unitIntervalMeshPoint A.subdivision.steps A.subdivision.steps_pos
            (A.segmentGridEdgeIndex i s).castSucc)
          (unitIntervalMeshPoint A.subdivision.steps A.subdivision.steps_pos
            (A.segmentGridEdgeIndex i s).succ) t) ∈ _
  have hzero :
      (⟨0, A.subdivision.steps_pos⟩ : Fin A.subdivision.steps).castSucc =
        (0 : Fin (A.subdivision.steps + 1)) := by rfl
  simpa only [unitSquareCellPoint, Set.Icc.convexComb_zero, hzero] using
    A.subdivision.cell_mem ⟨0, A.subdivision.steps_pos⟩
      (A.segmentGridEdgeIndex i s) 0 t

/-- 同一真实左边界细边也属于输入字母指定的标签成员。-/
theorem PathConcatAlignedSquareSubdivision.leftBoundaryAlignedGridEdge_mem_letterPiece
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (Fhom : Path.Homotopy
      (binaryVanKampenLetterConcatLoop hxU hxV letters) (Path.refl x₀))
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V
      letters.reverse.length)
    (i : Fin letters.reverse.length)
    (s : Fin (pathConcatSegmentGridLength letters.reverse.length A.factor i))
    (t : unitInterval) :
    A.leftBoundaryAlignedGridEdge hxU hxV letters Fhom i s t ∈
      binaryOpenCoverPiece U V (letters.reverse.get i).1 :=
  A.leftBoundarySegmentGridEdge_mem_letterPiece hxU hxV letters Fhom i s t

/-- 第零列真实细边的起点提升，等于对应小格的左下角提升。-/
theorem PathConcatAlignedSquareSubdivision.leftBoundaryAlignedGridEdge_cellSource_eq
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (Fhom : Path.Homotopy
      (binaryVanKampenLetterConcatLoop hxU hxV letters) (Path.refl x₀))
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V
      letters.reverse.length)
    (i : Fin letters.reverse.length)
    (s : Fin (pathConcatSegmentGridLength letters.reverse.length A.factor i)) :
    (⟨squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
          A.subdivision.steps_pos 0 (A.segmentGridEdgeIndex i s).castSucc,
        by simpa using
          A.leftBoundaryAlignedGridEdge_mem_cellPiece hxU hxV letters Fhom i s 0⟩ :
      binaryOpenCoverPiece U V
        (A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
          (A.segmentGridEdgeIndex i s))) =
      A.subdivision.gridCellVertexInPiece
        ⟨0, A.subdivision.steps_pos⟩ (A.segmentGridEdgeIndex i s) 0 0 := by
  apply Subtype.ext
  simp [BinaryOpenCoverSquareSubdivision.gridCellVertexInPiece,
    BinaryOpenCoverSquareSubdivision.gridCellMapInPiece,
    unitSquareGridVertex, squareGridVertex,
    unitSquareCellPoint]

/-- 第零列真实细边的终点提升，等于对应小格的左上角提升。-/
theorem PathConcatAlignedSquareSubdivision.leftBoundaryAlignedGridEdge_cellTarget_eq
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (Fhom : Path.Homotopy
      (binaryVanKampenLetterConcatLoop hxU hxV letters) (Path.refl x₀))
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V
      letters.reverse.length)
    (i : Fin letters.reverse.length)
    (s : Fin (pathConcatSegmentGridLength letters.reverse.length A.factor i)) :
    (⟨squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
          A.subdivision.steps_pos 0 (A.segmentGridEdgeIndex i s).succ,
        by simpa using
          A.leftBoundaryAlignedGridEdge_mem_cellPiece hxU hxV letters Fhom i s 1⟩ :
      binaryOpenCoverPiece U V
        (A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
          (A.segmentGridEdgeIndex i s))) =
      A.subdivision.gridCellVertexInPiece
        ⟨0, A.subdivision.steps_pos⟩ (A.segmentGridEdgeIndex i s) 0 1 := by
  apply Subtype.ext
  have hone : unitIntervalMeshPoint 1 unitSquareOnePos (1 : Fin 2) = 1 := by
    simpa using unitIntervalMeshPoint_last 1 unitSquareOnePos
  simp [BinaryOpenCoverSquareSubdivision.gridCellVertexInPiece,
    BinaryOpenCoverSquareSubdivision.gridCellMapInPiece,
    unitSquareGridVertex, squareGridVertex, unitSquareCellPoint, hone]

/-- 真实细边起点在输入字母成员中的提升，等于 block 的规范细网格起点。-/
private theorem PathConcatAlignedSquareSubdivision.leftBoundaryAlignedGridEdge_letterSource_eq
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (Fhom : Path.Homotopy
      (binaryVanKampenLetterConcatLoop hxU hxV letters) (Path.refl x₀))
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V
      letters.reverse.length)
    (i : Fin letters.reverse.length)
    (s : Fin (pathConcatSegmentGridLength letters.reverse.length A.factor i)) :
    (⟨squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
          A.subdivision.steps_pos 0 (A.segmentGridEdgeIndex i s).castSucc,
        by simpa using
          A.leftBoundaryAlignedGridEdge_mem_letterPiece hxU hxV letters Fhom i s 0⟩ :
      binaryOpenCoverPiece U V (letters.reverse.get i).1) =
      binaryVanKampenLetterBlockGridVertex hxU hxV letters A.factor
        A.factor_pos i s.castSucc := by
  apply Subtype.ext
  change squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
      A.subdivision.steps_pos 0 (A.segmentGridEdgeIndex i s).castSucc =
    ((binaryVanKampenLetterBlockGridVertex hxU hxV letters A.factor
      A.factor_pos i s.castSucc :
      binaryOpenCoverPiece U V (letters.reverse.get i).1) : X)
  rw [squareGridVertex, unitIntervalMeshPoint_zero,
    pathHomotopySquare_zero_left,
    A.unitIntervalMeshPoint_segmentGridEdgeIndex_castSucc]
  unfold binaryVanKampenLetterBlockGridVertex
    binaryVanKampenLetterDyadicSegmentInPiece
  rw [pathConcatSegmentMeshPoint_eq_convexComb]
  rfl

/-- 真实细边终点在输入字母成员中的提升，等于 block 的规范细网格终点。-/
private theorem PathConcatAlignedSquareSubdivision.leftBoundaryAlignedGridEdge_letterTarget_eq
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (Fhom : Path.Homotopy
      (binaryVanKampenLetterConcatLoop hxU hxV letters) (Path.refl x₀))
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V
      letters.reverse.length)
    (i : Fin letters.reverse.length)
    (s : Fin (pathConcatSegmentGridLength letters.reverse.length A.factor i)) :
    (⟨squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
          A.subdivision.steps_pos 0 (A.segmentGridEdgeIndex i s).succ,
        by simpa using
          A.leftBoundaryAlignedGridEdge_mem_letterPiece hxU hxV letters Fhom i s 1⟩ :
      binaryOpenCoverPiece U V (letters.reverse.get i).1) =
      binaryVanKampenLetterBlockGridVertex hxU hxV letters A.factor
        A.factor_pos i s.succ := by
  apply Subtype.ext
  change squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
      A.subdivision.steps_pos 0 (A.segmentGridEdgeIndex i s).succ =
    ((binaryVanKampenLetterBlockGridVertex hxU hxV letters A.factor
      A.factor_pos i s.succ :
      binaryOpenCoverPiece U V (letters.reverse.get i).1) : X)
  rw [squareGridVertex, unitIntervalMeshPoint_zero,
    pathHomotopySquare_zero_left,
    A.unitIntervalMeshPoint_segmentGridEdgeIndex_succ]
  unfold binaryVanKampenLetterBlockGridVertex
    binaryVanKampenLetterDyadicSegmentInPiece
  rw [pathConcatSegmentMeshPoint_eq_convexComb]
  rfl

/-- cell 标签侧从公共基点到统一真实细边起点的 connector。-/
def PathConcatAlignedSquareSubdivision.leftBoundaryAlignedGridEdgeCellStart
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (Fhom : Path.Homotopy
      (binaryVanKampenLetterConcatLoop hxU hxV letters) (Path.refl x₀))
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V
      letters.reverse.length)
    (i : Fin letters.reverse.length)
    (s : Fin (pathConcatSegmentGridLength letters.reverse.length A.factor i)) :
    Path
      (binaryOpenCoverBasepoint hxU hxV
        (A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
          (A.segmentGridEdgeIndex i s)))
      (⟨squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
          A.subdivision.steps_pos 0 (A.segmentGridEdgeIndex i s).castSucc,
        by simpa using
          A.leftBoundaryAlignedGridEdge_mem_cellPiece hxU hxV letters Fhom i s 0⟩ :
        binaryOpenCoverPiece U V
          (A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
            (A.segmentGridEdgeIndex i s))) :=
  (A.subdivision.gridCellVertexConnectorInPiece hxU hxV hU hV
    ⟨0, A.subdivision.steps_pos⟩ (A.segmentGridEdgeIndex i s) 0 0).cast rfl
      (A.leftBoundaryAlignedGridEdge_cellSource_eq hxU hxV letters Fhom i s)

/-- cell 标签侧从公共基点到统一真实细边终点的 connector。-/
def PathConcatAlignedSquareSubdivision.leftBoundaryAlignedGridEdgeCellEnd
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (Fhom : Path.Homotopy
      (binaryVanKampenLetterConcatLoop hxU hxV letters) (Path.refl x₀))
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V
      letters.reverse.length)
    (i : Fin letters.reverse.length)
    (s : Fin (pathConcatSegmentGridLength letters.reverse.length A.factor i)) :
    Path
      (binaryOpenCoverBasepoint hxU hxV
        (A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
          (A.segmentGridEdgeIndex i s)))
      (⟨squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
          A.subdivision.steps_pos 0 (A.segmentGridEdgeIndex i s).succ,
        by simpa using
          A.leftBoundaryAlignedGridEdge_mem_cellPiece hxU hxV letters Fhom i s 1⟩ :
        binaryOpenCoverPiece U V
          (A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
            (A.segmentGridEdgeIndex i s))) :=
  (A.subdivision.gridCellVertexConnectorInPiece hxU hxV hU hV
    ⟨0, A.subdivision.steps_pos⟩ (A.segmentGridEdgeIndex i s) 0 1).cast rfl
      (A.leftBoundaryAlignedGridEdge_cellTarget_eq hxU hxV letters Fhom i s)

/-- letter 标签侧从公共基点到统一真实细边起点的 connector。-/
def PathConcatAlignedSquareSubdivision.leftBoundaryAlignedGridEdgeLetterStart
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (Fhom : Path.Homotopy
      (binaryVanKampenLetterConcatLoop hxU hxV letters) (Path.refl x₀))
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V
      letters.reverse.length)
    (i : Fin letters.reverse.length)
    (s : Fin (pathConcatSegmentGridLength letters.reverse.length A.factor i)) :
    Path (binaryOpenCoverBasepoint hxU hxV (letters.reverse.get i).1)
      (⟨squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
          A.subdivision.steps_pos 0 (A.segmentGridEdgeIndex i s).castSucc,
        by simpa using
          A.leftBoundaryAlignedGridEdge_mem_letterPiece hxU hxV letters Fhom i s 0⟩ :
        binaryOpenCoverPiece U V (letters.reverse.get i).1) :=
  (binaryVanKampenLetterBlockGridConnector hxU hxV hU hV letters A.factor
    A.factor_pos i s.castSucc).cast rfl
      (A.leftBoundaryAlignedGridEdge_letterSource_eq hxU hxV letters Fhom i s)

/-- letter 标签侧从公共基点到统一真实细边终点的 connector。-/
def PathConcatAlignedSquareSubdivision.leftBoundaryAlignedGridEdgeLetterEnd
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (Fhom : Path.Homotopy
      (binaryVanKampenLetterConcatLoop hxU hxV letters) (Path.refl x₀))
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V
      letters.reverse.length)
    (i : Fin letters.reverse.length)
    (s : Fin (pathConcatSegmentGridLength letters.reverse.length A.factor i)) :
    Path (binaryOpenCoverBasepoint hxU hxV (letters.reverse.get i).1)
      (⟨squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
          A.subdivision.steps_pos 0 (A.segmentGridEdgeIndex i s).succ,
        by simpa using
          A.leftBoundaryAlignedGridEdge_mem_letterPiece hxU hxV letters Fhom i s 1⟩ :
        binaryOpenCoverPiece U V (letters.reverse.get i).1) :=
  (binaryVanKampenLetterBlockGridConnector hxU hxV hU hV letters A.factor
    A.factor_pos i s.succ).cast rfl
      (A.leftBoundaryAlignedGridEdge_letterTarget_eq hxU hxV letters Fhom i s)

/-- 同一 block 中相邻真实细边在固定 letter 成员中使用同一条共享顶点 connector；端点 proof
transport 不产生额外 gauge。-/
theorem PathConcatAlignedSquareSubdivision.leftBoundaryAlignedGridEdgeLetterConnector_adjacent
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (Fhom : Path.Homotopy
      (binaryVanKampenLetterConcatLoop hxU hxV letters) (Path.refl x₀))
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V
      letters.reverse.length)
    (i : Fin letters.reverse.length)
    (s t : Fin (pathConcatSegmentGridLength letters.reverse.length A.factor i))
    (hshared : s.succ = t.castSucc) :
    let ws : binaryOpenCoverPiece U V (letters.reverse.get i).1 :=
      ⟨squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
          A.subdivision.steps_pos 0 (A.segmentGridEdgeIndex i s).succ,
        by simpa using
          A.leftBoundaryAlignedGridEdge_mem_letterPiece hxU hxV letters Fhom i s 1⟩
    let wt : binaryOpenCoverPiece U V (letters.reverse.get i).1 :=
      ⟨squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
          A.subdivision.steps_pos 0 (A.segmentGridEdgeIndex i t).castSucc,
        by simpa using
          A.leftBoundaryAlignedGridEdge_mem_letterPiece hxU hxV letters Fhom i t 0⟩
    let hw : ws = wt := by
      apply Subtype.ext
      exact A.leftBoundary_segmentGridEdgeIndex_shared_vertex i s t hshared
    (A.leftBoundaryAlignedGridEdgeLetterEnd
        hxU hxV hU hV letters Fhom i s).cast rfl hw.symm =
      A.leftBoundaryAlignedGridEdgeLetterStart
        hxU hxV hU hV letters Fhom i t := by
  dsimp only
  apply Path.ext
  funext u
  apply Subtype.ext
  rw [Path.cast_coe]
  unfold PathConcatAlignedSquareSubdivision.leftBoundaryAlignedGridEdgeLetterEnd
    PathConcatAlignedSquareSubdivision.leftBoundaryAlignedGridEdgeLetterStart
  rw [Path.cast_coe, Path.cast_coe]
  exact congrArg (fun r =>
    ((binaryVanKampenLetterBlockGridConnector hxU hxV hU hV letters A.factor
      A.factor_pos i r u : binaryOpenCoverPiece U V (letters.reverse.get i).1) : X))
    hshared

/-- 下方细边的 cell 终点 connector 与真实竖直切换边下格 comparison 使用的左端 connector 相同。-/
theorem PathConcatAlignedSquareSubdivision.leftBoundaryCellEnd_eq_verticalSwitchBottomStart
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
    (hswitch : A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
      (A.segmentGridEdgeIndex i s) ≠
      A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
        (A.segmentGridEdgeIndex i t)) :
    let col : Fin A.subdivision.steps := ⟨0, A.subdivision.steps_pos⟩
    let lower := A.segmentGridEdgeIndex i s
    let upper := A.segmentGridEdgeIndex i t
    let hrows : lower.succ = upper.castSucc :=
      A.segmentGridEdgeIndex_succ_eq_castSucc i s t hshared
    let C := A.subdivision.verticalSwitchBottomConnectorComparison
      hxU hxV hUV hU hV col lower upper hrows hswitch
    let ws : binaryOpenCoverPiece U V (A.subdivision.label col lower) :=
      ⟨squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
          A.subdivision.steps_pos 0 lower.succ,
        by simpa using
          A.leftBoundaryAlignedGridEdge_mem_cellPiece hxU hxV letters Fhom i s 1⟩
    let hw : ws = C.edgeSource := by
      apply Subtype.ext
      change squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
          A.subdivision.steps_pos 0 lower.succ =
        ((binaryOpenCoverIntersectionToPiece U V (A.subdivision.label col lower)
          ⟨squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
              A.subdivision.steps_pos col.castSucc lower.succ, by
            simpa [squareGridVertex, Set.Icc.convexComb_zero] using
              A.subdivision.verticalSwitchEdge_mem_intersection
                col lower upper hrows hswitch 0⟩ :
          binaryOpenCoverPiece U V (A.subdivision.label col lower)) : X)
      rw [coe_binaryOpenCoverIntersectionToPiece]
      rfl
    (A.leftBoundaryAlignedGridEdgeCellEnd
        hxU hxV hU hV letters Fhom i s).cast rfl hw.symm = C.rightStart := by
  dsimp only
  apply Path.ext
  funext u
  apply Subtype.ext
  rw [Path.cast_coe]
  unfold PathConcatAlignedSquareSubdivision.leftBoundaryAlignedGridEdgeCellEnd
    BinaryOpenCoverSquareSubdivision.verticalSwitchBottomConnectorComparison
  dsimp only [CommonEdgeConnectorComparison.rightStart]
  rw [Path.cast_coe, Path.cast_coe]
  exact A.subdivision.coe_gridCellVertexConnectorInPieceOfLabel_eq
    hxU hxV hU hV ⟨0, A.subdivision.steps_pos⟩
    (A.segmentGridEdgeIndex i s) 0 1
    (A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
      (A.segmentGridEdgeIndex i s))
    (A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
      (A.segmentGridEdgeIndex i s)) rfl _ u

/-- 上方细边的 cell 起点 connector 与同一真实竖直切换边上格 comparison 的左端 connector 相同。-/
theorem PathConcatAlignedSquareSubdivision.leftBoundaryCellStart_eq_verticalSwitchTopStart
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
    (hswitch : A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
      (A.segmentGridEdgeIndex i s) ≠
      A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
        (A.segmentGridEdgeIndex i t)) :
    let col : Fin A.subdivision.steps := ⟨0, A.subdivision.steps_pos⟩
    let lower := A.segmentGridEdgeIndex i s
    let upper := A.segmentGridEdgeIndex i t
    let hrows : lower.succ = upper.castSucc :=
      A.segmentGridEdgeIndex_succ_eq_castSucc i s t hshared
    let C := A.subdivision.verticalSwitchTopConnectorComparison
      hxU hxV hUV hU hV col lower upper hrows hswitch
    let wt : binaryOpenCoverPiece U V (A.subdivision.label col upper) :=
      ⟨squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
          A.subdivision.steps_pos 0 upper.castSucc,
        by simpa using
          A.leftBoundaryAlignedGridEdge_mem_cellPiece hxU hxV letters Fhom i t 0⟩
    let hw : wt = C.edgeSource := by
      apply Subtype.ext
      change squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
          A.subdivision.steps_pos 0 upper.castSucc =
        ((binaryOpenCoverIntersectionToPiece U V (A.subdivision.label col upper)
          ⟨squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
              A.subdivision.steps_pos col.castSucc lower.succ, by
            simpa [squareGridVertex, Set.Icc.convexComb_zero] using
              A.subdivision.verticalSwitchEdge_mem_intersection
                col lower upper hrows hswitch 0⟩ :
          binaryOpenCoverPiece U V (A.subdivision.label col upper)) : X)
      rw [coe_binaryOpenCoverIntersectionToPiece]
      exact A.leftBoundary_segmentGridEdgeIndex_shared_vertex i s t hshared |>.symm
    (A.leftBoundaryAlignedGridEdgeCellStart
        hxU hxV hU hV letters Fhom i t).cast rfl hw.symm = C.rightStart := by
  dsimp only
  apply Path.ext
  funext u
  apply Subtype.ext
  rw [Path.cast_coe]
  unfold PathConcatAlignedSquareSubdivision.leftBoundaryAlignedGridEdgeCellStart
    BinaryOpenCoverSquareSubdivision.verticalSwitchTopConnectorComparison
  dsimp only [CommonEdgeConnectorComparison.rightStart]
  rw [Path.cast_coe, Path.cast_coe]
  exact A.subdivision.coe_gridCellVertexConnectorInPieceOfLabel_eq
    hxU hxV hU hV ⟨0, A.subdivision.steps_pos⟩
    (A.segmentGridEdgeIndex i t) 0 0
    (A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
      (A.segmentGridEdgeIndex i t))
    (A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
      (A.segmentGridEdgeIndex i t)) rfl _ u

/-- 两行同标签时，下方细边 cell 终点 connector 与竖直 common comparison 的下格 connector 相同。-/
theorem PathConcatAlignedSquareSubdivision.leftBoundaryCellEnd_eq_verticalCommonLeftStart
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (Fhom : Path.Homotopy
      (binaryVanKampenLetterConcatLoop hxU hxV letters) (Path.refl x₀))
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V
      letters.reverse.length)
    (i : Fin letters.reverse.length)
    (s t : Fin (pathConcatSegmentGridLength letters.reverse.length A.factor i))
    (hshared : s.succ = t.castSucc)
    (hlabel : A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
      (A.segmentGridEdgeIndex i s) =
      A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
        (A.segmentGridEdgeIndex i t)) :
    let col : Fin A.subdivision.steps := ⟨0, A.subdivision.steps_pos⟩
    let lower := A.segmentGridEdgeIndex i s
    let upper := A.segmentGridEdgeIndex i t
    let hrows : lower.succ = upper.castSucc :=
      A.segmentGridEdgeIndex_succ_eq_castSucc i s t hshared
    let C := A.subdivision.verticalCommonEdgeConnectorComparison
      hxU hxV hU hV col lower upper hrows hlabel
    let ws : binaryOpenCoverPiece U V (A.subdivision.label col lower) :=
      ⟨squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
          A.subdivision.steps_pos 0 lower.succ,
        by simpa using
          A.leftBoundaryAlignedGridEdge_mem_cellPiece hxU hxV letters Fhom i s 1⟩
    let hw : ws = C.edgeSource := by apply Subtype.ext; rfl
    (A.leftBoundaryAlignedGridEdgeCellEnd
        hxU hxV hU hV letters Fhom i s).cast rfl hw.symm = C.leftStart := by
  dsimp only
  apply Path.ext
  funext u
  apply Subtype.ext
  rw [Path.cast_coe]
  unfold PathConcatAlignedSquareSubdivision.leftBoundaryAlignedGridEdgeCellEnd
    BinaryOpenCoverSquareSubdivision.verticalCommonEdgeConnectorComparison
  dsimp only [CommonEdgeConnectorComparison.leftStart]
  rw [Path.cast_coe, Path.cast_coe]
  exact A.subdivision.coe_gridCellVertexConnectorInPieceOfLabel_eq
    hxU hxV hU hV ⟨0, A.subdivision.steps_pos⟩
    (A.segmentGridEdgeIndex i s) 0 1
    (A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
      (A.segmentGridEdgeIndex i s))
    (A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
      (A.segmentGridEdgeIndex i s)) rfl _ u

/-- 两行同标签时，竖直 common comparison 的上格 connector 与上方细边 cell 起点 connector
送回环境空间后逐点相同。底层函数形式避免显式搬运两个 Bool 标签的基点类型。-/
theorem PathConcatAlignedSquareSubdivision.coe_leftBoundaryCellStart_eq_verticalCommonRightStart
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (Fhom : Path.Homotopy
      (binaryVanKampenLetterConcatLoop hxU hxV letters) (Path.refl x₀))
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V
      letters.reverse.length)
    (i : Fin letters.reverse.length)
    (s t : Fin (pathConcatSegmentGridLength letters.reverse.length A.factor i))
    (hshared : s.succ = t.castSucc)
    (hlabel : A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
      (A.segmentGridEdgeIndex i s) =
      A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
        (A.segmentGridEdgeIndex i t))
    (u : unitInterval) :
    let col : Fin A.subdivision.steps := ⟨0, A.subdivision.steps_pos⟩
    let lower := A.segmentGridEdgeIndex i s
    let upper := A.segmentGridEdgeIndex i t
    let hrows : lower.succ = upper.castSucc :=
      A.segmentGridEdgeIndex_succ_eq_castSucc i s t hshared
    let C := A.subdivision.verticalCommonEdgeConnectorComparison
      hxU hxV hU hV col lower upper hrows hlabel
    ((C.rightStart u : binaryOpenCoverPiece U V
      (A.subdivision.label col lower)) : X) =
      ((A.leftBoundaryAlignedGridEdgeCellStart
        hxU hxV hU hV letters Fhom i t u :
          binaryOpenCoverPiece U V (A.subdivision.label col upper)) : X) := by
  dsimp only
  unfold BinaryOpenCoverSquareSubdivision.verticalCommonEdgeConnectorComparison
    PathConcatAlignedSquareSubdivision.leftBoundaryAlignedGridEdgeCellStart
  dsimp only [CommonEdgeConnectorComparison.rightStart]
  rw [Path.cast_coe, Path.cast_coe]
  exact A.subdivision.coe_gridCellVertexConnectorInPieceOfLabel_eq
    hxU hxV hU hV ⟨0, A.subdivision.steps_pos⟩
    (A.segmentGridEdgeIndex i t) 0 0
    (A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
      (A.segmentGridEdgeIndex i s))
    (A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
      (A.segmentGridEdgeIndex i t)) hlabel.symm _ u

/-- 任一左边界细边在 cell 与 letter 标签不同时，其 dual comparison 的 cell 终点 potential 正是
该格左上角的实际 `gridCellVertexPotentialFromIntersection`。-/
theorem PathConcatAlignedSquareSubdivision.leftBoundaryDualCellEndPotential_eq_gridCellPotential
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
    let col : Fin A.subdivision.steps := ⟨0, A.subdivision.steps_pos⟩
    let row := A.segmentGridEdgeIndex i s
    let q := A.leftBoundaryAlignedGridEdge hxU hxV letters Fhom i s
    let hb := A.leftBoundaryAlignedGridEdge_mem_cellPiece
      hxU hxV letters Fhom i s
    let hc := A.leftBoundaryAlignedGridEdge_mem_letterPiece
      hxU hxV letters Fhom i s
    let C := binaryOpenCoverDualPathConnectorComparison hxU hxV hUV
      q hb hc hne hb
      (A.leftBoundaryAlignedGridEdgeCellStart
        hxU hxV hU hV letters Fhom i s)
      (A.leftBoundaryAlignedGridEdgeCellEnd
        hxU hxV hU hV letters Fhom i s)
    let z : ↥(U ∩ V) :=
      ⟨squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
          A.subdivision.steps_pos 0 row.succ,
        mem_intersection_of_mem_binaryOpenCoverPieces_of_ne
          (by simpa using hb 1) (by simpa using hc 1) hne⟩
    let hz : binaryOpenCoverIntersectionToPiece U V
        (A.subdivision.label col row) z =
      A.subdivision.gridCellVertexInPiece col row 0 1 := by
      calc
        binaryOpenCoverIntersectionToPiece U V
            (A.subdivision.label col row) z =
            (⟨squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
                A.subdivision.steps_pos 0 row.succ,
              by simpa using hb 1⟩ :
              binaryOpenCoverPiece U V (A.subdivision.label col row)) := by
                apply Subtype.ext
                rw [coe_binaryOpenCoverIntersectionToPiece]
        _ = A.subdivision.gridCellVertexInPiece col row 0 1 :=
          A.leftBoundaryAlignedGridEdge_cellTarget_eq
            hxU hxV letters Fhom i s
    ((Monoid.PushoutI.of (A.subdivision.label col row) C.endChange :
        binaryVanKampenPushout U V hxU hxV)⁻¹) =
      A.subdivision.gridCellVertexPotentialFromIntersection
        hxU hxV hUV hU hV z col row 0 1 hz := by
  dsimp only
  rw [binaryOpenCoverDualPathConnectorComparison_endPotential_eq,
    A.subdivision.gridCellVertexPotentialFromIntersection_eq_vertexPotential]
  apply binaryOpenCoverVertexPotentialFromIntersection_cast
    hxU hxV hUV
      (A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
        (A.segmentGridEdgeIndex i s))
  · apply Subtype.ext
    rfl
  · apply Path.ext
    funext u
    apply Subtype.ext
    rw [Path.cast_coe]
    unfold PathConcatAlignedSquareSubdivision.leftBoundaryAlignedGridEdgeCellEnd
    rw [Path.cast_coe]
  · exact A.leftBoundaryAlignedGridEdge_cellTarget_eq
      hxU hxV letters Fhom i s

/-- 上方逐边 dual comparison 的 cell 起点 potential，可统一改用相邻细边共享的交集顶点作为参考。-/
theorem PathConcatAlignedSquareSubdivision.leftBoundaryDualCellStartPotential_at_sharedVertex
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
    (ht : A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
      (A.segmentGridEdgeIndex i t) ≠ (letters.reverse.get i).1) :
    let col : Fin A.subdivision.steps := ⟨0, A.subdivision.steps_pos⟩
    let lower := A.segmentGridEdgeIndex i s
    let upper := A.segmentGridEdgeIndex i t
    let q := A.leftBoundaryAlignedGridEdge hxU hxV letters Fhom i t
    let hb := A.leftBoundaryAlignedGridEdge_mem_cellPiece
      hxU hxV letters Fhom i t
    let hc := A.leftBoundaryAlignedGridEdge_mem_letterPiece
      hxU hxV letters Fhom i t
    let Cdual := binaryOpenCoverDualPathConnectorComparison hxU hxV hUV
      q hb hc ht hb
      (A.leftBoundaryAlignedGridEdgeCellStart
        hxU hxV hU hV letters Fhom i t)
      (A.leftBoundaryAlignedGridEdgeCellEnd
        hxU hxV hU hV letters Fhom i t)
    let z : ↥(U ∩ V) :=
      ⟨squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
          A.subdivision.steps_pos 0 lower.succ,
        mem_intersection_of_mem_binaryOpenCoverPieces_of_ne
          (by
            rw [A.segmentGridEdgeIndex_succ_eq_castSucc i s t hshared]
            simpa using hb 0)
          (by
            rw [A.segmentGridEdgeIndex_succ_eq_castSucc i s t hshared]
            simpa using hc 0)
          ht⟩
    let hz : binaryOpenCoverIntersectionToPiece U V
        (A.subdivision.label col upper) z =
      A.subdivision.gridCellVertexInPiece col upper 0 0 := by
      calc
        binaryOpenCoverIntersectionToPiece U V
            (A.subdivision.label col upper) z =
            (⟨squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
                A.subdivision.steps_pos 0 upper.castSucc,
              by simpa using hb 0⟩ :
              binaryOpenCoverPiece U V (A.subdivision.label col upper)) := by
                apply Subtype.ext
                rw [coe_binaryOpenCoverIntersectionToPiece]
                exact A.leftBoundary_segmentGridEdgeIndex_shared_vertex
                  i s t hshared
        _ = A.subdivision.gridCellVertexInPiece col upper 0 0 :=
          A.leftBoundaryAlignedGridEdge_cellSource_eq
            hxU hxV letters Fhom i t
    ((Monoid.PushoutI.of (A.subdivision.label col upper) Cdual.startChange :
        binaryVanKampenPushout U V hxU hxV)⁻¹) =
      A.subdivision.gridCellVertexPotentialFromIntersection
        hxU hxV hUV hU hV z col upper 0 0 hz := by
  dsimp only
  rw [binaryOpenCoverDualPathConnectorComparison_startPotential_eq,
    A.subdivision.gridCellVertexPotentialFromIntersection_eq_vertexPotential]
  apply binaryOpenCoverVertexPotentialFromIntersection_cast
    hxU hxV hUV
      (A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
        (A.segmentGridEdgeIndex i t))
  · apply Subtype.ext
    exact A.leftBoundary_segmentGridEdgeIndex_shared_vertex i s t hshared |>.symm
  · apply Path.ext
    funext u
    apply Subtype.ext
    rw [Path.cast_coe]
    unfold PathConcatAlignedSquareSubdivision.leftBoundaryAlignedGridEdgeCellStart
    rw [Path.cast_coe]
  · exact A.leftBoundaryAlignedGridEdge_cellSource_eq
      hxU hxV letters Fhom i t

/-- 下方细边的双标签 comparison cell potential，与真实竖直切换 transition 的下格 potential
严格相同。-/
theorem PathConcatAlignedSquareSubdivision.leftBoundaryDualCellEndPotential_eq_verticalSwitchBottom
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
    (hswitch : A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
      (A.segmentGridEdgeIndex i s) ≠
      A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
        (A.segmentGridEdgeIndex i t)) :
    let col : Fin A.subdivision.steps := ⟨0, A.subdivision.steps_pos⟩
    let lower := A.segmentGridEdgeIndex i s
    let upper := A.segmentGridEdgeIndex i t
    let hrows : lower.succ = upper.castSucc :=
      A.segmentGridEdgeIndex_succ_eq_castSucc i s t hshared
    let q := A.leftBoundaryAlignedGridEdge hxU hxV letters Fhom i s
    let hb := A.leftBoundaryAlignedGridEdge_mem_cellPiece
      hxU hxV letters Fhom i s
    let hc := A.leftBoundaryAlignedGridEdge_mem_letterPiece
      hxU hxV letters Fhom i s
    let Cdual := binaryOpenCoverDualPathConnectorComparison hxU hxV hUV
      q hb hc hs hb
      (A.leftBoundaryAlignedGridEdgeCellStart
        hxU hxV hU hV letters Fhom i s)
      (A.leftBoundaryAlignedGridEdgeCellEnd
        hxU hxV hU hV letters Fhom i s)
    let Cvertical := A.subdivision.verticalSwitchBottomConnectorComparison
      hxU hxV hUV hU hV col lower upper hrows hswitch
    ((Monoid.PushoutI.of (A.subdivision.label col lower) Cdual.endChange :
        binaryVanKampenPushout U V hxU hxV)⁻¹) =
      ((Monoid.PushoutI.of (A.subdivision.label col lower)
        Cvertical.startChange : binaryVanKampenPushout U V hxU hxV)⁻¹) := by
  dsimp only
  rw [binaryOpenCoverDualPathConnectorComparison_endPotential_eq,
    A.subdivision.verticalSwitchBottom_startPotential_eq_vertexPotential]
  apply binaryOpenCoverVertexPotentialFromIntersection_cast
    hxU hxV hUV
      (A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
        (A.segmentGridEdgeIndex i s))
  · apply Subtype.ext
    rfl
  · exact A.leftBoundaryCellEnd_eq_verticalSwitchBottomStart
      hxU hxV hUV hU hV letters Fhom i s t hshared hswitch
  · apply Subtype.ext
    change squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
        A.subdivision.steps_pos 0 (A.segmentGridEdgeIndex i s).succ =
      ((binaryOpenCoverIntersectionToPiece U V
        (A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
          (A.segmentGridEdgeIndex i s))
        ⟨squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
            A.subdivision.steps_pos
            (⟨0, A.subdivision.steps_pos⟩ : Fin A.subdivision.steps).castSucc
            (A.segmentGridEdgeIndex i s).succ, by
          simpa [squareGridVertex, Set.Icc.convexComb_zero] using
            A.subdivision.verticalSwitchEdge_mem_intersection
              ⟨0, A.subdivision.steps_pos⟩
              (A.segmentGridEdgeIndex i s) (A.segmentGridEdgeIndex i t)
              (A.segmentGridEdgeIndex_succ_eq_castSucc i s t hshared)
              hswitch 0⟩ : binaryOpenCoverPiece U V
          (A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
            (A.segmentGridEdgeIndex i s))) : X)
    rw [coe_binaryOpenCoverIntersectionToPiece]
    rfl

/-- 上方细边的双标签 comparison cell potential，与同一真实竖直切换 transition 的上格 potential
严格相同。-/
theorem PathConcatAlignedSquareSubdivision.leftBoundaryDualCellStartPotential_eq_verticalSwitchTop
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
    (ht : A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
      (A.segmentGridEdgeIndex i t) ≠ (letters.reverse.get i).1)
    (hswitch : A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
      (A.segmentGridEdgeIndex i s) ≠
      A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
        (A.segmentGridEdgeIndex i t)) :
    let col : Fin A.subdivision.steps := ⟨0, A.subdivision.steps_pos⟩
    let lower := A.segmentGridEdgeIndex i s
    let upper := A.segmentGridEdgeIndex i t
    let hrows : lower.succ = upper.castSucc :=
      A.segmentGridEdgeIndex_succ_eq_castSucc i s t hshared
    let q := A.leftBoundaryAlignedGridEdge hxU hxV letters Fhom i t
    let hb := A.leftBoundaryAlignedGridEdge_mem_cellPiece
      hxU hxV letters Fhom i t
    let hc := A.leftBoundaryAlignedGridEdge_mem_letterPiece
      hxU hxV letters Fhom i t
    let Cdual := binaryOpenCoverDualPathConnectorComparison hxU hxV hUV
      q hb hc ht hb
      (A.leftBoundaryAlignedGridEdgeCellStart
        hxU hxV hU hV letters Fhom i t)
      (A.leftBoundaryAlignedGridEdgeCellEnd
        hxU hxV hU hV letters Fhom i t)
    let Cvertical := A.subdivision.verticalSwitchTopConnectorComparison
      hxU hxV hUV hU hV col lower upper hrows hswitch
    ((Monoid.PushoutI.of (A.subdivision.label col upper) Cdual.startChange :
        binaryVanKampenPushout U V hxU hxV)⁻¹) =
      ((Monoid.PushoutI.of (A.subdivision.label col upper)
        Cvertical.startChange : binaryVanKampenPushout U V hxU hxV)⁻¹) := by
  dsimp only
  rw [binaryOpenCoverDualPathConnectorComparison_startPotential_eq,
    A.subdivision.verticalSwitchTop_startPotential_eq_vertexPotential]
  apply binaryOpenCoverVertexPotentialFromIntersection_cast
    hxU hxV hUV
      (A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
        (A.segmentGridEdgeIndex i t))
  · apply Subtype.ext
    exact A.leftBoundary_segmentGridEdgeIndex_shared_vertex i s t hshared |>.symm
  · exact A.leftBoundaryCellStart_eq_verticalSwitchTopStart
      hxU hxV hUV hU hV letters Fhom i s t hshared hswitch
  · apply Subtype.ext
    change squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
        A.subdivision.steps_pos 0 (A.segmentGridEdgeIndex i t).castSucc =
      ((binaryOpenCoverIntersectionToPiece U V
        (A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
          (A.segmentGridEdgeIndex i t))
        ⟨squareGridVertex (pathHomotopySquare Fhom) A.subdivision.steps
            A.subdivision.steps_pos
            (⟨0, A.subdivision.steps_pos⟩ : Fin A.subdivision.steps).castSucc
            (A.segmentGridEdgeIndex i s).succ, by
          simpa [squareGridVertex, Set.Icc.convexComb_zero] using
            A.subdivision.verticalSwitchEdge_mem_intersection
              ⟨0, A.subdivision.steps_pos⟩
              (A.segmentGridEdgeIndex i s) (A.segmentGridEdgeIndex i t)
              (A.segmentGridEdgeIndex_succ_eq_castSucc i s t hshared)
              hswitch 0⟩ : binaryOpenCoverPiece U V
          (A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
            (A.segmentGridEdgeIndex i t))) : X)
    rw [coe_binaryOpenCoverIntersectionToPiece]
    exact A.leftBoundary_segmentGridEdgeIndex_shared_vertex i s t hshared |>.symm

/-- 若相邻两条细边的 cell 标签都不同于固定 letter 标签，则两次双标签 comparison 在共享顶点
给出的 letter-side potential 严格一致。-/
theorem PathConcatAlignedSquareSubdivision.leftBoundaryDualLetterPotential_adjacent
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
      (A.segmentGridEdgeIndex i t) ≠ (letters.reverse.get i).1) :
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
    let Cs := binaryOpenCoverDualPathConnectorComparison hxU hxV hUV
      qs hbs hcs hs hcs
      (A.leftBoundaryAlignedGridEdgeLetterStart
        hxU hxV hU hV letters Fhom i s)
      (A.leftBoundaryAlignedGridEdgeLetterEnd
        hxU hxV hU hV letters Fhom i s)
    let Ct := binaryOpenCoverDualPathConnectorComparison hxU hxV hUV
      qt hbt hct ht hct
      (A.leftBoundaryAlignedGridEdgeLetterStart
        hxU hxV hU hV letters Fhom i t)
      (A.leftBoundaryAlignedGridEdgeLetterEnd
        hxU hxV hU hV letters Fhom i t)
    ((Monoid.PushoutI.of (letters.reverse.get i).1 Cs.endChange :
        binaryVanKampenPushout U V hxU hxV)⁻¹) =
      ((Monoid.PushoutI.of (letters.reverse.get i).1 Ct.startChange :
        binaryVanKampenPushout U V hxU hxV)⁻¹) := by
  dsimp only
  apply binaryOpenCoverDualPathConnectorComparison_sharedPotential
    hxU hxV hUV
    (A.leftBoundary_segmentGridEdgeIndex_shared_vertex i s t hshared)
  dsimp only
  exact A.leftBoundaryAlignedGridEdgeLetterConnector_adjacent
    hxU hxV hU hV letters Fhom i s t hshared

/-- 真实左边界细边在其小格标签成员中，使用原小格角 connectors 得到的局部元素。-/
def PathConcatAlignedSquareSubdivision.leftBoundaryAlignedGridEdgeCellElement
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (Fhom : Path.Homotopy
      (binaryVanKampenLetterConcatLoop hxU hxV letters) (Path.refl x₀))
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V
      letters.reverse.length)
    (i : Fin letters.reverse.length)
    (s : Fin (pathConcatSegmentGridLength letters.reverse.length A.factor i)) :
    FundamentalGroup
      (binaryOpenCoverPiece U V
        (A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
          (A.segmentGridEdgeIndex i s)))
      (binaryOpenCoverBasepoint hxU hxV
        (A.subdivision.label ⟨0, A.subdivision.steps_pos⟩
          (A.segmentGridEdgeIndex i s))) :=
  let q := A.leftBoundaryAlignedGridEdge hxU hxV letters Fhom i s
  let hq := A.leftBoundaryAlignedGridEdge_mem_cellPiece hxU hxV letters Fhom i s
  FundamentalGroup.fromPath ⟦Path.correctedLoop
    (A.leftBoundaryAlignedGridEdgeCellStart
      hxU hxV hU hV letters Fhom i s)
    (binaryOpenCoverPathInPiece q hq)
    (A.leftBoundaryAlignedGridEdgeCellEnd
      hxU hxV hU hV letters Fhom i s)⟧

/-- 真实左边界细边在固定输入字母成员中，使用 block connectors 得到的局部元素。-/
def PathConcatAlignedSquareSubdivision.leftBoundaryAlignedGridEdgeLetterElement
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (Fhom : Path.Homotopy
      (binaryVanKampenLetterConcatLoop hxU hxV letters) (Path.refl x₀))
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V
      letters.reverse.length)
    (i : Fin letters.reverse.length)
    (s : Fin (pathConcatSegmentGridLength letters.reverse.length A.factor i)) :
    FundamentalGroup (binaryOpenCoverPiece U V (letters.reverse.get i).1)
      (binaryOpenCoverBasepoint hxU hxV (letters.reverse.get i).1) :=
  let q := A.leftBoundaryAlignedGridEdge hxU hxV letters Fhom i s
  let hq := A.leftBoundaryAlignedGridEdge_mem_letterPiece hxU hxV letters Fhom i s
  FundamentalGroup.fromPath ⟦Path.correctedLoop
    (A.leftBoundaryAlignedGridEdgeLetterStart
      hxU hxV hU hV letters Fhom i s)
    (binaryOpenCoverPathInPiece q hq)
    (A.leftBoundaryAlignedGridEdgeLetterEnd
      hxU hxV hU hV letters Fhom i s)⟧

/-- 小格局部坐标中的左竖边，经端点 transport 后严格等于统一真实左边界细边的成员提升。-/
private theorem PathConcatAlignedSquareSubdivision.leftBoundaryAlignedGridEdgeInCellPiece_eq
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (Fhom : Path.Homotopy
      (binaryVanKampenLetterConcatLoop hxU hxV letters) (Path.refl x₀))
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V
      letters.reverse.length)
    (i : Fin letters.reverse.length)
    (s : Fin (pathConcatSegmentGridLength letters.reverse.length A.factor i)) :
    let row := A.segmentGridEdgeIndex i s
    let col : Fin A.subdivision.steps := ⟨0, A.subdivision.steps_pos⟩
    let q := A.leftBoundaryAlignedGridEdge hxU hxV letters Fhom i s
    let hq := A.leftBoundaryAlignedGridEdge_mem_cellPiece hxU hxV letters Fhom i s
    binaryOpenCoverPathInPiece q hq =
      (((squareGridVerticalEdge (ContinuousMap.id (unitInterval × unitInterval))
        1 unitSquareOnePos 0 0).map
          (A.subdivision.gridCellMapInPiece col row).continuous).cast
        (A.leftBoundaryAlignedGridEdge_cellSource_eq hxU hxV letters Fhom i s)
        (A.leftBoundaryAlignedGridEdge_cellTarget_eq hxU hxV letters Fhom i s)) := by
  dsimp only
  apply Path.ext
  funext t
  apply Subtype.ext
  rw [Path.cast_coe]
  rw [coe_binaryOpenCoverPathInPiece]
  have hone : unitIntervalMeshPoint 1 unitSquareOnePos (1 : Fin 2) = 1 := by
    simpa using unitIntervalMeshPoint_last 1 unitSquareOnePos
  change (A.leftBoundaryAlignedGridEdge hxU hxV letters Fhom i s) t =
    pathHomotopySquare Fhom
      (unitSquareCellPoint A.subdivision.steps A.subdivision.steps_pos
        ⟨0, A.subdivision.steps_pos⟩ (A.segmentGridEdgeIndex i s)
        (squareGridVerticalEdge (ContinuousMap.id (unitInterval × unitInterval))
          1 unitSquareOnePos 0 0 t).1
        (squareGridVerticalEdge (ContinuousMap.id (unitInterval × unitInterval))
          1 unitSquareOnePos 0 0 t).2)
  simp [PathConcatAlignedSquareSubdivision.leftBoundaryAlignedGridEdge,
    squareGridVerticalEdge, unitSquareCellPoint, hone]

/-- 因而 cell-label 版本正是原单格四边词中的真实左竖边生成元。-/
theorem PathConcatAlignedSquareSubdivision.leftBoundaryAlignedGridEdgeCellElement_eq
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (Fhom : Path.Homotopy
      (binaryVanKampenLetterConcatLoop hxU hxV letters) (Path.refl x₀))
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V
      letters.reverse.length)
    (i : Fin letters.reverse.length)
    (s : Fin (pathConcatSegmentGridLength letters.reverse.length A.factor i)) :
    A.leftBoundaryAlignedGridEdgeCellElement hxU hxV hU hV letters Fhom i s =
      A.subdivision.gridCellBasedVerticalEdgeInPiece hxU hxV hU hV
        ⟨0, A.subdivision.steps_pos⟩ (A.segmentGridEdgeIndex i s) 0 := by
  let l := A.subdivision.gridCellVertexConnectorInPiece hxU hxV hU hV
    ⟨0, A.subdivision.steps_pos⟩ (A.segmentGridEdgeIndex i s) 0 0
  let e := (squareGridVerticalEdge (ContinuousMap.id (unitInterval × unitInterval))
    1 unitSquareOnePos 0 0).map
      (A.subdivision.gridCellMapInPiece ⟨0, A.subdivision.steps_pos⟩
        (A.segmentGridEdgeIndex i s)).continuous
  let r := A.subdivision.gridCellVertexConnectorInPiece hxU hxV hU hV
    ⟨0, A.subdivision.steps_pos⟩ (A.segmentGridEdgeIndex i s) 0 1
  let hs := A.leftBoundaryAlignedGridEdge_cellSource_eq hxU hxV letters Fhom i s
  let ht := A.leftBoundaryAlignedGridEdge_cellTarget_eq hxU hxV letters Fhom i s
  have hp : Path.correctedLoop (l.cast rfl hs) (e.cast hs ht) (r.cast rfl ht) =
      Path.correctedLoop l e r := correctedLoop_cast l e r hs ht
  unfold PathConcatAlignedSquareSubdivision.leftBoundaryAlignedGridEdgeCellElement
    BinaryOpenCoverSquareSubdivision.gridCellBasedVerticalEdgeInPiece
  dsimp only
  rw [A.leftBoundaryAlignedGridEdgeInCellPiece_eq hxU hxV letters Fhom i s]
  exact congrArg Path.Homotopic.Quotient.mk hp

/-- dyadic segment transport 送回底层函数后，就是原 concat 道路在相应断点仿射区间上的限制。-/
private theorem Path.concatDyadicSegment_apply
    {Y : Type*} [TopologicalSpace Y] {n : ℕ}
    (p : Fin (n + 1) → Y)
    (F : (i : Fin n) → Path (p i.castSucc) (p i.succ))
    (i : Fin n) (t : unitInterval) :
    Path.concatDyadicSegment p F i t =
      Path.concat p F
        (Set.Icc.convexComb (pathConcatBreakpoint n i.castSucc)
          (pathConcatBreakpoint n i.succ) t) := by
  unfold Path.concatDyadicSegment
  rw [Path.cast_coe]
  rfl

/-- block 的局部字母成员细边经端点 transport 后，严格等于统一真实左边界细边的字母成员提升。-/
private theorem PathConcatAlignedSquareSubdivision.leftBoundaryAlignedGridEdgeInLetterPiece_eq
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (Fhom : Path.Homotopy
      (binaryVanKampenLetterConcatLoop hxU hxV letters) (Path.refl x₀))
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V
      letters.reverse.length)
    (i : Fin letters.reverse.length)
    (s : Fin (pathConcatSegmentGridLength letters.reverse.length A.factor i)) :
    let q := A.leftBoundaryAlignedGridEdge hxU hxV letters Fhom i s
    let hq := A.leftBoundaryAlignedGridEdge_mem_letterPiece hxU hxV letters Fhom i s
    binaryOpenCoverPathInPiece q hq =
      (binaryVanKampenLetterBlockGridEdgeInPiece hxU hxV letters A.factor
        A.factor_pos i s).cast
        (A.leftBoundaryAlignedGridEdge_letterSource_eq hxU hxV letters Fhom i s)
        (A.leftBoundaryAlignedGridEdge_letterTarget_eq hxU hxV letters Fhom i s) := by
  dsimp only
  apply Path.ext
  funext t
  apply Subtype.ext
  rw [Path.cast_coe, coe_binaryOpenCoverPathInPiece]
  unfold PathConcatAlignedSquareSubdivision.leftBoundaryAlignedGridEdge
  rw [A.leftBoundarySegmentGridEdge_apply Fhom i s t]
  change binaryVanKampenLetterConcatLoop hxU hxV letters
      (Set.Icc.convexComb
        (pathConcatSegmentMeshPoint letters.reverse.length A.factor A.factor_pos
          i s.castSucc)
        (pathConcatSegmentMeshPoint letters.reverse.length A.factor A.factor_pos
          i s.succ) t) =
    (Path.concatDyadicSegment (fun _ : Fin (letters.reverse.length + 1) => x₀)
      (fun j : Fin letters.reverse.length =>
        (letters.reverse.get j).ambientLoop hxU hxV) i).subpath
      (unitIntervalMeshPoint
        (pathConcatSegmentGridLength letters.reverse.length A.factor i)
        (pathConcatSegmentGridLength_pos letters.reverse.length A.factor
          A.factor_pos i) s.castSucc)
      (unitIntervalMeshPoint
        (pathConcatSegmentGridLength letters.reverse.length A.factor i)
        (pathConcatSegmentGridLength_pos letters.reverse.length A.factor
          A.factor_pos i) s.succ) t
  unfold Path.subpath
  change binaryVanKampenLetterConcatLoop hxU hxV letters
      (Set.Icc.convexComb
        (pathConcatSegmentMeshPoint letters.reverse.length A.factor A.factor_pos
          i s.castSucc)
        (pathConcatSegmentMeshPoint letters.reverse.length A.factor A.factor_pos
          i s.succ) t) =
    Path.concatDyadicSegment
      (fun _ : Fin (letters.reverse.length + 1) => x₀)
      (fun j : Fin letters.reverse.length =>
        (letters.reverse.get j).ambientLoop hxU hxV) i
      (Set.Icc.convexComb
        (unitIntervalMeshPoint
          (pathConcatSegmentGridLength letters.reverse.length A.factor i)
          (pathConcatSegmentGridLength_pos letters.reverse.length A.factor
            A.factor_pos i) s.castSucc)
        (unitIntervalMeshPoint
          (pathConcatSegmentGridLength letters.reverse.length A.factor i)
          (pathConcatSegmentGridLength_pos letters.reverse.length A.factor
            A.factor_pos i) s.succ) t)
  rw [Path.concatDyadicSegment_apply]
  unfold binaryVanKampenLetterConcatLoop
  rw [pathConcatSegmentFineInterval_eq_convexComb]

/-- 因而 letter-label 版本正是 block word 中的真实细边 corrected-loop 因子。-/
theorem PathConcatAlignedSquareSubdivision.leftBoundaryAlignedGridEdgeLetterElement_eq
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (Fhom : Path.Homotopy
      (binaryVanKampenLetterConcatLoop hxU hxV letters) (Path.refl x₀))
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V
      letters.reverse.length)
    (i : Fin letters.reverse.length)
    (s : Fin (pathConcatSegmentGridLength letters.reverse.length A.factor i)) :
    A.leftBoundaryAlignedGridEdgeLetterElement hxU hxV hU hV letters Fhom i s =
      FundamentalGroup.fromPath ⟦Path.correctedLoop
        (binaryVanKampenLetterBlockGridConnector hxU hxV hU hV letters A.factor
          A.factor_pos i s.castSucc)
        (binaryVanKampenLetterBlockGridEdgeInPiece hxU hxV letters A.factor
          A.factor_pos i s)
        (binaryVanKampenLetterBlockGridConnector hxU hxV hU hV letters A.factor
          A.factor_pos i s.succ)⟧ := by
  let l := binaryVanKampenLetterBlockGridConnector hxU hxV hU hV letters
    A.factor A.factor_pos i s.castSucc
  let e := binaryVanKampenLetterBlockGridEdgeInPiece hxU hxV letters
    A.factor A.factor_pos i s
  let r := binaryVanKampenLetterBlockGridConnector hxU hxV hU hV letters
    A.factor A.factor_pos i s.succ
  let hs := A.leftBoundaryAlignedGridEdge_letterSource_eq hxU hxV letters Fhom i s
  let ht := A.leftBoundaryAlignedGridEdge_letterTarget_eq hxU hxV letters Fhom i s
  have hp : Path.correctedLoop (l.cast rfl hs) (e.cast hs ht) (r.cast rfl ht) =
      Path.correctedLoop l e r := correctedLoop_cast l e r hs ht
  unfold PathConcatAlignedSquareSubdivision.leftBoundaryAlignedGridEdgeLetterElement
  dsimp only
  rw [A.leftBoundaryAlignedGridEdgeInLetterPiece_eq hxU hxV letters Fhom i s]
  exact congrArg Path.Homotopic.Quotient.mk hp

end SandronesLibrary.Topology
