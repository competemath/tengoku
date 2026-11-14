/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.VanKampenBlockBoundaryCocycle

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# van Kampen 单字母 block 的细边 telescope

本文件将一个输入 letter block 内每条真实左边界 cell factor 改写为 letter-side factor 在组合首末
frames 下的 rebase，并利用相邻 combined frames 的严格相容性执行有限 edge-chain telescope。结论把
整 block 的真实 framed cell-edge 反序乘积压缩为原输入 Pushout 字母的一次整体 rebase。

本文件不把不同 letter blocks 相乘，不识别完整左边界词，也不证明 residual gauge、kernel 平凡、
规范同态单射或最终 van Kampen 同构。

当前条目：`topology.fundamental-group.van-kampen-letter-block-telescope`。
-/

open Set
open scoped unitInterval

noncomputable section

namespace SandronesLibrary.Topology

variable {X : Type*} [TopologicalSpace X]

namespace PathConcatAlignedSquareSubdivision

/-- 一个输入 block 的第 `s` 条 letter-side 细边因子送入 Pushout 后的元素。

> **Entry**: topology.fundamental-group.van-kampen-letter-block-telescope-/
private def leftBoundaryBlockFactor
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (Fhom : Path.Homotopy
      (binaryVanKampenLetterConcatLoop hxU hxV letters) (Path.refl x₀))
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V
      letters.reverse.length)
    (i : Fin letters.reverse.length)
    (s : Fin (pathConcatSegmentGridLength letters.reverse.length A.factor i)) :
    binaryVanKampenPushout U V hxU hxV :=
  Monoid.PushoutI.of (letters.reverse.get i).1
    (FundamentalGroup.fromPath ⟦Path.correctedLoop
      (binaryVanKampenLetterBlockGridConnector hxU hxV hU hV letters
        A.factor A.factor_pos i s.castSucc)
      (binaryVanKampenLetterBlockGridEdgeInPiece hxU hxV letters
        A.factor A.factor_pos i s)
      (binaryVanKampenLetterBlockGridConnector hxU hxV hU hV letters
        A.factor A.factor_pos i s.succ)⟧)

/-- 第 `s` 条 block 因子使用的组合起点 frame。-/
noncomputable def leftBoundaryCombinedStartFrame
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
    binaryVanKampenPushout U V hxU hxV :=
  let row := A.segmentGridEdgeIndex i s
  let T := A.leftBoundaryCellToLetterTransitions
    hxU hxV hUV hU hV letters Fhom i s
  let F := A.subdivision.rightAnchoredGridRowFramesAt
    hxU hxV hUV hU hV row.val row.isLt ⟨0, A.subdivision.steps_pos⟩
  T.startChange * F.bottomLeft

/-- 第 `s` 条 block 因子使用的组合终点 frame。-/
noncomputable def leftBoundaryCombinedEndFrame
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
    binaryVanKampenPushout U V hxU hxV :=
  let row := A.segmentGridEdgeIndex i s
  let T := A.leftBoundaryCellToLetterTransitions
    hxU hxV hUV hU hV letters Fhom i s
  let F := A.subdivision.rightAnchoredGridRowFramesAt
    hxU hxV hUV hU hV row.val row.isLt ⟨0, A.subdivision.steps_pos⟩
  T.endChange * F.topLeft

/-- 一个输入 block 的有限 edge chain；每项保存组合终点 frame 与对应 letter-side 因子。-/
noncomputable def leftBoundaryBlockEdgeChain
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (Fhom : Path.Homotopy
      (binaryVanKampenLetterConcatLoop hxU hxV letters) (Path.refl x₀))
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V
      letters.reverse.length)
    (i : Fin letters.reverse.length) :
    List ((binaryVanKampenPushout U V hxU hxV) ×
      binaryVanKampenPushout U V hxU hxV) :=
  List.ofFn fun s =>
    (A.leftBoundaryCombinedEndFrame hxU hxV hUV hU hV letters Fhom i s,
      A.leftBoundaryBlockFactor hxU hxV hU hV letters Fhom i s)

/-- 第 `s` 个左边界 cell 的真实竖边，在二维右锚定 frame 下换连接后的 Pushout 元素。-/
private noncomputable def rightAnchoredFramedLeftBoundaryCellEdge
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
    binaryVanKampenPushout U V hxU hxV :=
  let row := A.segmentGridEdgeIndex i s
  let col : Fin A.subdivision.steps := ⟨0, A.subdivision.steps_pos⟩
  let F := A.subdivision.rightAnchoredGridRowFramesAt
    hxU hxV hUV hU hV row.val row.isLt col
  rebaseEdge F.bottomLeft F.topLeft
    (Monoid.PushoutI.of (A.subdivision.label col row)
      (A.subdivision.gridCellBasedVerticalEdgeInPiece hxU hxV hU hV col row 0))

/-- Each named actual left-boundary fine edge is precisely the left edge stored
by the right-anchored full-row state at its global grid row.
@isnad1 id=other.5h9v.s10.a348bc3f41df from=translated src=- shape=e9053f3f vocab=bd1ec230
-/
theorem rightAnchoredFramedLeftBoundaryCellEdge_eq_rowLeftEdge
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
    let frames := A.subdivision.rightAnchoredGridRowFramesAt
      hxU hxV hUV hU hV row.val row.isLt
    let compat := A.subdivision.rightAnchoredGridRowFramesAt_compatible
      hxU hxV hUV hU hV row.val row.isLt
    A.rightAnchoredFramedLeftBoundaryCellEdge
        hxU hxV hUV hU hV letters Fhom i s =
      (A.subdivision.framedHorizontalFullRowState
        hxU hxV hUV hU hV row frames compat).leftEdge := by
  dsimp only
  unfold PathConcatAlignedSquareSubdivision.rightAnchoredFramedLeftBoundaryCellEdge
  exact (A.subdivision.rightAnchoredGridFullRow_leftEdge_eq_leftmost
    hxU hxV hUV hU hV
    (A.segmentGridEdgeIndex i s).val
    (A.segmentGridEdgeIndex i s).isLt).symm

/-- 一个输入 block 覆盖的真实右锚定左边界 cell 边链。第一坐标只记录与命名 block chain
相同的组合终点 frame；反序边词读取第二坐标。-/
noncomputable def leftBoundaryFramedCellEdgeChain
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (Fhom : Path.Homotopy
      (binaryVanKampenLetterConcatLoop hxU hxV letters) (Path.refl x₀))
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V
      letters.reverse.length)
    (i : Fin letters.reverse.length) :
    List ((binaryVanKampenPushout U V hxU hxV) ×
      binaryVanKampenPushout U V hxU hxV) :=
  List.ofFn fun s =>
    (A.leftBoundaryCombinedEndFrame hxU hxV hUV hU hV letters Fhom i s,
      A.rightAnchoredFramedLeftBoundaryCellEdge
        hxU hxV hUV hU hV letters Fhom i s)

@[simp] private theorem leftBoundaryBlockEdgeChain_length
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (Fhom : Path.Homotopy
      (binaryVanKampenLetterConcatLoop hxU hxV letters) (Path.refl x₀))
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V
      letters.reverse.length)
    (i : Fin letters.reverse.length) :
    (A.leftBoundaryBlockEdgeChain hxU hxV hUV hU hV letters Fhom i).length =
      pathConcatSegmentGridLength letters.reverse.length A.factor i := by
  simp [PathConcatAlignedSquareSubdivision.leftBoundaryBlockEdgeChain]

/-- 相邻 block 因子的组合终点／起点 frames 严格相同。
@isnad1 id=eq.6h10v.s9.9293302ef7cf from=translated src=- shape=6e853388 vocab=327ba245
-/
theorem leftBoundaryCombinedFrames_adjacent
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
    A.leftBoundaryCombinedEndFrame hxU hxV hUV hU hV letters Fhom i s =
      A.leftBoundaryCombinedStartFrame hxU hxV hUV hU hV letters Fhom i t := by
  exact A.combinedLeftBoundaryFrames_adjacent
    hxU hxV hUV hU hV letters Fhom i s t hshared

/-- The combined transition-times-grid frames at the end and start of adjacent
input-letter blocks agree strictly.
@isnad1 id=other.6h9v.s9.425cd4ebe0d2 from=translated src=- shape=fcb2a4b8 vocab=1177860c
-/
theorem leftBoundaryCombinedBlockFrames_adjacent
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
    A.leftBoundaryCombinedEndFrame hxU hxV hUV hU hV letters Fhom i
        (finLastOfPos Li hi) =
      A.leftBoundaryCombinedStartFrame hxU hxV hUV hU hV letters Fhom j
        ⟨0, hj⟩ := by
  dsimp only
  unfold PathConcatAlignedSquareSubdivision.leftBoundaryCombinedEndFrame
    PathConcatAlignedSquareSubdivision.leftBoundaryCombinedStartFrame
  dsimp only
  rw [A.leftBoundaryBlockTransitions_cocycle
      hxU hxV hUV hU hV letters Fhom i j hshared,
    A.rightAnchoredBlockFrames_adjacent
      hxU hxV hUV hU hV letters Fhom i j hshared,
    mul_assoc]

/-- 每条右锚定 framed 左边界 cell 边，等于相同 letter 因子在“逐边 transition × 二维 frame”
组合端点下的单次 rebase。-/
private theorem rightAnchoredFramedLeftEdge_eq_rebaseBlockFactor
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
    let col : Fin A.subdivision.steps := ⟨0, A.subdivision.steps_pos⟩
    let F := A.subdivision.rightAnchoredGridRowFramesAt
      hxU hxV hUV hU hV row.val row.isLt col
    let T := A.leftBoundaryCellToLetterTransitions hxU hxV hUV hU hV
      letters Fhom i s
    let b := A.subdivision.label col row
    let c := (letters.reverse.get i).1
    rebaseEdge F.bottomLeft F.topLeft
        (Monoid.PushoutI.of b
          (A.subdivision.gridCellBasedVerticalEdgeInPiece hxU hxV hU hV
            col row 0)) =
      rebaseEdge (T.startChange * F.bottomLeft) (T.endChange * F.topLeft)
        (Monoid.PushoutI.of c
          (FundamentalGroup.fromPath ⟦Path.correctedLoop
            (binaryVanKampenLetterBlockGridConnector hxU hxV hU hV letters
              A.factor A.factor_pos i s.castSucc)
            (binaryVanKampenLetterBlockGridEdgeInPiece hxU hxV letters
              A.factor A.factor_pos i s)
            (binaryVanKampenLetterBlockGridConnector hxU hxV hU hV letters
              A.factor A.factor_pos i s.succ)⟧)) := by
  dsimp only
  rw [A.leftBoundaryCellEdgeToBlockFactor_relation
    hxU hxV hUV hU hV letters Fhom i s]
  exact rebaseEdge_rebaseEdge _ _ _ _ _

/-- 右锚定真实 cell 边的逐项关系，以 block-chain 的公开 factor/frame 名称重述。-/
private theorem rightAnchoredFramedLeftEdge_eq_rebaseNamedBlockFactor
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
    let col : Fin A.subdivision.steps := ⟨0, A.subdivision.steps_pos⟩
    let F := A.subdivision.rightAnchoredGridRowFramesAt
      hxU hxV hUV hU hV row.val row.isLt col
    rebaseEdge F.bottomLeft F.topLeft
        (Monoid.PushoutI.of (A.subdivision.label col row)
          (A.subdivision.gridCellBasedVerticalEdgeInPiece hxU hxV hU hV
            col row 0) : binaryVanKampenPushout U V hxU hxV) =
      rebaseEdge
        (A.leftBoundaryCombinedStartFrame
          hxU hxV hUV hU hV letters Fhom i s)
        (A.leftBoundaryCombinedEndFrame
          hxU hxV hUV hU hV letters Fhom i s)
        (A.leftBoundaryBlockFactor hxU hxV hU hV letters Fhom i s) := by
  exact A.rightAnchoredFramedLeftEdge_eq_rebaseBlockFactor
    hxU hxV hUV hU hV letters Fhom i s

/-- 一个输入 block 内全部真实右锚定左边界边的反序乘积，等于命名 block factor chain 从
首 frame 开始逐边换连接后的乘积。中间 frame 的消去完全复用通用 `List.ofFn` 链引理。-/
private theorem rebasedLeftBoundaryBlockEdgeChain_eq_framedCellEdges
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (Fhom : Path.Homotopy
      (binaryVanKampenLetterConcatLoop hxU hxV letters) (Path.refl x₀))
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V
      letters.reverse.length)
    (i : Fin letters.reverse.length) :
    rebasedEdgeChainProduct
        (A.leftBoundaryCombinedStartFrame hxU hxV hUV hU hV letters Fhom i
          ⟨0, pathConcatSegmentGridLength_pos letters.reverse.length A.factor
            A.factor_pos i⟩)
        (A.leftBoundaryBlockEdgeChain hxU hxV hUV hU hV letters Fhom i) =
      reverseEdgeChainProduct
        (A.leftBoundaryFramedCellEdgeChain hxU hxV hUV hU hV letters Fhom i) := by
  change
    rebasedEdgeChainProduct
        (A.leftBoundaryCombinedStartFrame hxU hxV hUV hU hV letters Fhom i
          ⟨0, pathConcatSegmentGridLength_pos letters.reverse.length A.factor
            A.factor_pos i⟩)
        (List.ofFn fun s =>
          (A.leftBoundaryCombinedEndFrame hxU hxV hUV hU hV letters Fhom i s,
            A.leftBoundaryBlockFactor hxU hxV hU hV letters Fhom i s)) =
      reverseEdgeChainProduct
        (List.ofFn fun s =>
          (A.leftBoundaryCombinedEndFrame hxU hxV hUV hU hV letters Fhom i s,
            A.rightAnchoredFramedLeftBoundaryCellEdge
              hxU hxV hUV hU hV letters Fhom i s))
  rw [rebasedEdgeChainProduct_ofFn_eq_reverseEdgeChainProduct_of_pos
    (pathConcatSegmentGridLength letters.reverse.length A.factor i)
    (pathConcatSegmentGridLength_pos letters.reverse.length A.factor A.factor_pos i)
    (fun s => A.leftBoundaryCombinedStartFrame
      hxU hxV hUV hU hV letters Fhom i s)
    (fun s => A.leftBoundaryCombinedEndFrame
      hxU hxV hUV hU hV letters Fhom i s)
    (fun s => A.leftBoundaryBlockFactor hxU hxV hU hV letters Fhom i s)
    (fun s t hshared => A.leftBoundaryCombinedFrames_adjacent
      hxU hxV hUV hU hV letters Fhom i s t hshared)]
  apply congrArg reverseEdgeChainProduct
  apply congrArg List.ofFn
  funext s
  apply Prod.ext
  · rfl
  · exact (A.rightAnchoredFramedLeftEdge_eq_rebaseNamedBlockFactor
      hxU hxV hUV hU hV letters Fhom i s).symm

/-- 命名 block factor chain 的反序乘积，正是该输入字母完整细网格词经对应 Pushout 注入后的像。-/
private theorem reverseLeftBoundaryBlockEdgeChain_eq_of_gridWord
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (Fhom : Path.Homotopy
      (binaryVanKampenLetterConcatLoop hxU hxV letters) (Path.refl x₀))
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V
      letters.reverse.length)
    (i : Fin letters.reverse.length) :
    reverseEdgeChainProduct
        (A.leftBoundaryBlockEdgeChain hxU hxV hUV hU hV letters Fhom i) =
      Monoid.PushoutI.of (letters.reverse.get i).1
        (binaryVanKampenLetterBlockGridWord hxU hxV hU hV letters
          A.factor A.factor_pos i) := by
  rw [reverseEdgeChainProduct_eq_reverse_map_snd_prod]
  simp only [PathConcatAlignedSquareSubdivision.leftBoundaryBlockEdgeChain,
    List.map_ofFn]
  change
    (List.ofFn fun s =>
      (Monoid.PushoutI.of (letters.reverse.get i).1
        (FundamentalGroup.fromPath ⟦Path.correctedLoop
          (binaryVanKampenLetterBlockGridConnector hxU hxV hU hV letters
            A.factor A.factor_pos i s.castSucc)
          (binaryVanKampenLetterBlockGridEdgeInPiece hxU hxV letters
            A.factor A.factor_pos i s)
          (binaryVanKampenLetterBlockGridConnector hxU hxV hU hV letters
            A.factor A.factor_pos i s.succ)⟧) :
        binaryVanKampenPushout U V hxU hxV)).reverse.prod = _
  rw [← reverseDfoldl_eq_reverse_ofFn_prod]
  rw [← Path.map_reverseDfoldl]
  rfl

/-- 完整细网格 block word 已由既有接口识别为原输入字母，因此命名 factor chain 的反序乘积
就是该字母经对应 Pushout 注入后的像。-/
private theorem reverseLeftBoundaryBlockEdgeChain_eq_of_letter
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (Fhom : Path.Homotopy
      (binaryVanKampenLetterConcatLoop hxU hxV letters) (Path.refl x₀))
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V
      letters.reverse.length)
    (i : Fin letters.reverse.length) :
    reverseEdgeChainProduct
        (A.leftBoundaryBlockEdgeChain hxU hxV hUV hU hV letters Fhom i) =
      Monoid.PushoutI.of (letters.reverse.get i).1 (letters.reverse.get i).2 := by
  rw [A.reverseLeftBoundaryBlockEdgeChain_eq_of_gridWord
    hxU hxV hUV hU hV letters Fhom i]
  rw [binaryVanKampenLetterBlockGridWord_eq_letter]

/-- 命名 block chain 的 `edgeChainEnd` 是最后一条细边的组合终点 frame。-/
private theorem leftBoundaryBlockEdgeChain_end
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hUV : IsPathConnected (U ∩ V))
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
    let start := A.leftBoundaryCombinedStartFrame
      hxU hxV hUV hU hV letters Fhom i ⟨0, hL⟩
    edgeChainEnd start
        (A.leftBoundaryBlockEdgeChain hxU hxV hUV hU hV letters Fhom i) =
      A.leftBoundaryCombinedEndFrame hxU hxV hUV hU hV letters Fhom i
        (finLastOfPos L hL) := by
  dsimp only
  unfold PathConcatAlignedSquareSubdivision.leftBoundaryBlockEdgeChain
  exact edgeChainEnd_ofFn_of_pos _ _ _ _ _

/-- 复用通用 telescope 后，一个 block 内全部真实右锚定左边界 cell 边只剩首末组合 frame
之间的一次整体 rebase。-/
private theorem leftBoundaryFramedCellEdges_eq_rebaseBlockWord
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (Fhom : Path.Homotopy
      (binaryVanKampenLetterConcatLoop hxU hxV letters) (Path.refl x₀))
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V
      letters.reverse.length)
    (i : Fin letters.reverse.length) :
    let start := A.leftBoundaryCombinedStartFrame
      hxU hxV hUV hU hV letters Fhom i
        ⟨0, pathConcatSegmentGridLength_pos letters.reverse.length A.factor
          A.factor_pos i⟩
    let chain := A.leftBoundaryBlockEdgeChain
      hxU hxV hUV hU hV letters Fhom i
    reverseEdgeChainProduct
        (A.leftBoundaryFramedCellEdgeChain
          hxU hxV hUV hU hV letters Fhom i) =
      rebaseEdge start (edgeChainEnd start chain)
        (reverseEdgeChainProduct chain) := by
  dsimp only
  rw [← A.rebasedLeftBoundaryBlockEdgeChain_eq_framedCellEdges
    hxU hxV hUV hU hV letters Fhom i]
  exact rebasedEdgeChainProduct_eq_rebaseEdge _ _

/-- 一个 block 内真实右锚定左边界 cell 边的总乘积，是原输入 Pushout 字母在该 block 首末
组合 frame 之间的一次整体 rebase。
@isnad1 id=other.5h8v.s12.86e63ede1e25 from=translated src=- shape=f319f5cb vocab=bdffea7f
-/
theorem leftBoundaryFramedCellEdges_eq_rebaseLetter
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (Fhom : Path.Homotopy
      (binaryVanKampenLetterConcatLoop hxU hxV letters) (Path.refl x₀))
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V
      letters.reverse.length)
    (i : Fin letters.reverse.length) :
    let start := A.leftBoundaryCombinedStartFrame
      hxU hxV hUV hU hV letters Fhom i
        ⟨0, pathConcatSegmentGridLength_pos letters.reverse.length A.factor
          A.factor_pos i⟩
    let chain := A.leftBoundaryBlockEdgeChain
      hxU hxV hUV hU hV letters Fhom i
    reverseEdgeChainProduct
        (A.leftBoundaryFramedCellEdgeChain
          hxU hxV hUV hU hV letters Fhom i) =
      rebaseEdge start (edgeChainEnd start chain)
        (Monoid.PushoutI.of (letters.reverse.get i).1 (letters.reverse.get i).2) := by
  dsimp only
  rw [A.leftBoundaryFramedCellEdges_eq_rebaseBlockWord
    hxU hxV hUV hU hV letters Fhom i]
  rw [A.reverseLeftBoundaryBlockEdgeChain_eq_of_letter
    hxU hxV hUV hU hV letters Fhom i]

/-- 上一定理的显式首末 frame 版本；不再把 block 终点隐藏在 `edgeChainEnd` 中。
@isnad1 id=other.5h8v.s12.6e3e47ea8ecb from=translated src=- shape=a6e5f92f vocab=64b7c5bc
-/
theorem leftBoundaryFramedCellEdges_eq_rebaseLetter_explicit
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hUV : IsPathConnected (U ∩ V))
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
    let start := A.leftBoundaryCombinedStartFrame
      hxU hxV hUV hU hV letters Fhom i ⟨0, hL⟩
    let finish := A.leftBoundaryCombinedEndFrame
      hxU hxV hUV hU hV letters Fhom i (finLastOfPos L hL)
    reverseEdgeChainProduct
        (A.leftBoundaryFramedCellEdgeChain
          hxU hxV hUV hU hV letters Fhom i) =
      rebaseEdge start finish
        (Monoid.PushoutI.of (letters.reverse.get i).1 (letters.reverse.get i).2) := by
  dsimp only
  rw [A.leftBoundaryFramedCellEdges_eq_rebaseLetter
    hxU hxV hUV hU hV letters Fhom i]
  rw [A.leftBoundaryBlockEdgeChain_end
    hxU hxV hUV hU hV letters Fhom i]

end PathConcatAlignedSquareSubdivision

end SandronesLibrary.Topology
