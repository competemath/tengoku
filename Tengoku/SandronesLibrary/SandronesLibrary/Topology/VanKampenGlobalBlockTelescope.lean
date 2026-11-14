/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.VanKampenLetterBlockTelescope

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# van Kampen 字母 blocks 的全局 telescope

本文件把每个输入 letter block 的单 block telescope 结果组成第二层 edge chain，利用跨 block
combined-frame 相容性消去全部中间 block frames。它同时证明先 flatten 全部真实细边再整体反序相乘，
等于先在每个 block 内反序相乘再按反序 block chain 相乘。

本文件不把第二层 letter chain 识别为原输入字母词，不证明完整左边界消失，也不处理 residual gauge、
kernel、单射或最终 van Kampen 同构。

当前条目：`topology.fundamental-group.van-kampen-global-block-telescope`。
-/

open Set
open scoped unitInterval

noncomputable section

namespace SandronesLibrary.Topology

variable {X : Type*} [TopologicalSpace X]

namespace PathConcatAlignedSquareSubdivision

/-- 第二层链以原输入字母为因子，并以各字母 block 已 telescope 后的首末 frame 为边界。

> **Entry**: topology.fundamental-group.van-kampen-global-block-telescope-/
noncomputable def leftBoundaryLetterBlockChain
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (Fhom : Path.Homotopy
      (binaryVanKampenLetterConcatLoop hxU hxV letters) (Path.refl x₀))
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V
      letters.reverse.length) :
    List ((binaryVanKampenPushout U V hxU hxV) ×
      binaryVanKampenPushout U V hxU hxV) :=
  List.ofFn fun i =>
    let L := pathConcatSegmentGridLength letters.reverse.length A.factor i
    let hL := pathConcatSegmentGridLength_pos letters.reverse.length A.factor
      A.factor_pos i
    (A.leftBoundaryCombinedEndFrame
        hxU hxV hUV hU hV letters Fhom i (finLastOfPos L hL),
      Monoid.PushoutI.of (letters.reverse.get i).1 (letters.reverse.get i).2)

/-- The parallel second-level chain whose factors are the actual fully framed
left-boundary cell-edge products of each input block.-/
noncomputable def leftBoundaryFramedBlockChain
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (Fhom : Path.Homotopy
      (binaryVanKampenLetterConcatLoop hxU hxV letters) (Path.refl x₀))
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V
      letters.reverse.length) :
    List ((binaryVanKampenPushout U V hxU hxV) ×
      binaryVanKampenPushout U V hxU hxV) :=
  List.ofFn fun i =>
    let L := pathConcatSegmentGridLength letters.reverse.length A.factor i
    let hL := pathConcatSegmentGridLength_pos letters.reverse.length A.factor
      A.factor_pos i
    (A.leftBoundaryCombinedEndFrame
        hxU hxV hUV hU hV letters Fhom i (finLastOfPos L hL),
      reverseEdgeChainProduct
        (A.leftBoundaryFramedCellEdgeChain
          hxU hxV hUV hU hV letters Fhom i))

/-- All actual framed left-boundary cell-edge chains, flattened in global grid
row order.-/
noncomputable def leftBoundaryAllFramedCellEdgeChain
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (Fhom : Path.Homotopy
      (binaryVanKampenLetterConcatLoop hxU hxV letters) (Path.refl x₀))
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V
      letters.reverse.length) :
    List ((binaryVanKampenPushout U V hxU hxV) ×
      binaryVanKampenPushout U V hxU hxV) :=
  (List.ofFn fun i => A.leftBoundaryFramedCellEdgeChain
    hxU hxV hUV hU hV letters Fhom i).flatten

/-- Reversing a flattened list and multiplying is the nested reverse product of
the blocks, in reverse block order.-/
private theorem reverse_flatten_prod {G : Type*} [Group G] (blocks : List (List G)) :
    blocks.flatten.reverse.prod =
      (blocks.map fun block => block.reverse.prod).reverse.prod := by
  induction blocks with
  | nil => rfl
  | cons block rest ih =>
      simp only [List.flatten_cons, List.reverse_append, List.prod_append,
        List.map_cons, List.reverse_cons, List.prod_singleton]
      rw [ih]

/-- Reversing and multiplying the flattened fine-edge chain is the same as
first multiplying within each block and then reversing the block chain.
@isnad1 id=eq.5h7v.s9.77dcf78c8eba from=translated src=- shape=e1f269c2 vocab=a26afbf4
-/
theorem reverseAllFramedCellEdges_eq_framedBlocks
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (Fhom : Path.Homotopy
      (binaryVanKampenLetterConcatLoop hxU hxV letters) (Path.refl x₀))
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V
      letters.reverse.length) :
    reverseEdgeChainProduct
        (A.leftBoundaryAllFramedCellEdgeChain
          hxU hxV hUV hU hV letters Fhom) =
      reverseEdgeChainProduct
        (A.leftBoundaryFramedBlockChain
          hxU hxV hUV hU hV letters Fhom) := by
  rw [reverseEdgeChainProduct_eq_reverse_map_snd_prod,
    reverseEdgeChainProduct_eq_reverse_map_snd_prod]
  simp only [PathConcatAlignedSquareSubdivision.leftBoundaryAllFramedCellEdgeChain,
    PathConcatAlignedSquareSubdivision.leftBoundaryFramedBlockChain,
    List.map_flatten, List.map_ofFn]
  simpa [Function.comp_def, reverseEdgeChainProduct_eq_reverse_map_snd_prod] using
    (reverse_flatten_prod
      (G := binaryVanKampenPushout U V hxU hxV)
      (List.ofFn fun i =>
        (A.leftBoundaryFramedCellEdgeChain
          hxU hxV hUV hU hV letters Fhom i).map Prod.snd))

/-- For a nonempty aligned input word, the flattened block-local fine-edge chain
is exactly the full right-anchored grid left-boundary word.
@isnad1 id=eq.6h7v.s9.98bb85bbbbc2 from=translated src=- shape=239bab70 vocab=0416cdd7
-/
theorem reverseAllFramedCellEdges_eq_gridLeftBoundaryWord
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (Fhom : Path.Homotopy
      (binaryVanKampenLetterConcatLoop hxU hxV letters) (Path.refl x₀))
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V
      letters.reverse.length)
    (hn : 0 < letters.reverse.length) :
    reverseEdgeChainProduct
        (A.leftBoundaryAllFramedCellEdgeChain
          hxU hxV hUV hU hV letters Fhom) =
      A.subdivision.rightAnchoredGridLeftBoundaryWordAt
        hxU hxV hUV hU hV
        (A.subdivision.steps - 1)
        (Nat.sub_lt A.subdivision.steps_pos Nat.zero_lt_one) := by
  rw [reverseEdgeChainProduct_eq_reverse_map_snd_prod,
    A.subdivision.rightAnchoredGridFullLeftBoundary_eq_reverseRows
      hxU hxV hUV hU hV,
    reverseEdgeChainProduct_eq_reverse_map_snd_prod]
  apply congrArg List.prod
  apply congrArg List.reverse
  let rowValue := fun r : Fin A.subdivision.steps =>
    let frames := A.subdivision.rightAnchoredGridRowFramesAt
      hxU hxV hUV hU hV r.val r.isLt
    let compat := A.subdivision.rightAnchoredGridRowFramesAt_compatible
      hxU hxV hUV hU hV r.val r.isLt
    (A.subdivision.framedHorizontalFullRowState
      hxU hxV hUV hU hV r frames compat).leftEdge
  have hindices := A.segmentGridEdgeIndices_flatten hn
  have hvalues := congrArg (List.map rowValue) hindices
  simp only [List.map_flatten, List.map_ofFn] at hvalues
  unfold PathConcatAlignedSquareSubdivision.leftBoundaryAllFramedCellEdgeChain
  simp only [List.map_ofFn]
  change
    ((List.ofFn fun i : Fin letters.reverse.length =>
      A.leftBoundaryFramedCellEdgeChain
        hxU hxV hUV hU hV letters Fhom i).flatten.map Prod.snd) =
      List.ofFn rowValue
  rw [List.map_flatten]
  simp only [List.map_ofFn]
  trans (List.ofFn (List.map rowValue ∘ fun i : Fin letters.reverse.length =>
      List.ofFn fun s : Fin
        (pathConcatSegmentGridLength letters.reverse.length A.factor i) =>
          A.segmentGridEdgeIndex i s)).flatten
  · apply congrArg List.flatten
    apply congrArg List.ofFn
    funext i
    dsimp only [Function.comp_apply]
    unfold PathConcatAlignedSquareSubdivision.leftBoundaryFramedCellEdgeChain
    rw [List.map_ofFn, List.map_ofFn]
    apply congrArg List.ofFn
    funext s
    exact A.rightAnchoredFramedLeftBoundaryCellEdge_eq_rowLeftEdge
      hxU hxV hUV hU hV letters Fhom i s
  · simpa [Function.comp_def] using hvalues

/-- For a nonempty input word, telescoping the second-level letter chain block by
block gives exactly the reverse product of the actual framed block products.-/
private theorem rebasedLetterBlockChain_eq_framedBlocks
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (Fhom : Path.Homotopy
      (binaryVanKampenLetterConcatLoop hxU hxV letters) (Path.refl x₀))
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V
      letters.reverse.length)
    (hn : 0 < letters.reverse.length) :
    let i₀ : Fin letters.reverse.length := ⟨0, hn⟩
    let hL₀ := pathConcatSegmentGridLength_pos letters.reverse.length A.factor
      A.factor_pos i₀
    let start := A.leftBoundaryCombinedStartFrame
      hxU hxV hUV hU hV letters Fhom i₀ ⟨0, hL₀⟩
    rebasedEdgeChainProduct start
        (A.leftBoundaryLetterBlockChain
          hxU hxV hUV hU hV letters Fhom) =
      reverseEdgeChainProduct
        (A.leftBoundaryFramedBlockChain
          hxU hxV hUV hU hV letters Fhom) := by
  dsimp only
  let startFrame := fun i : Fin letters.reverse.length =>
    A.leftBoundaryCombinedStartFrame hxU hxV hUV hU hV letters Fhom i
      ⟨0, pathConcatSegmentGridLength_pos letters.reverse.length A.factor
        A.factor_pos i⟩
  let endFrame := fun i : Fin letters.reverse.length =>
    A.leftBoundaryCombinedEndFrame hxU hxV hUV hU hV letters Fhom i
      (finLastOfPos
        (pathConcatSegmentGridLength letters.reverse.length A.factor i)
        (pathConcatSegmentGridLength_pos letters.reverse.length A.factor
          A.factor_pos i))
  let factor := fun i : Fin letters.reverse.length =>
    (Monoid.PushoutI.of (letters.reverse.get i).1 (letters.reverse.get i).2 :
      binaryVanKampenPushout U V hxU hxV)
  change rebasedEdgeChainProduct (startFrame ⟨0, hn⟩)
      (List.ofFn fun i => (endFrame i, factor i)) =
    reverseEdgeChainProduct (List.ofFn fun i =>
      (endFrame i, reverseEdgeChainProduct
        (A.leftBoundaryFramedCellEdgeChain
          hxU hxV hUV hU hV letters Fhom i)))
  rw [rebasedEdgeChainProduct_ofFn_eq_reverseEdgeChainProduct_of_pos
    letters.reverse.length hn startFrame endFrame factor]
  · apply congrArg reverseEdgeChainProduct
    apply congrArg List.ofFn
    funext i
    apply Prod.ext
    · rfl
    · exact (A.leftBoundaryFramedCellEdges_eq_rebaseLetter_explicit
        hxU hxV hUV hU hV letters Fhom i).symm
  · intro i j hij
    exact A.leftBoundaryCombinedBlockFrames_adjacent
      hxU hxV hUV hU hV letters Fhom i j hij

/-- The second telescope removes every intermediate whole-block frame, leaving
only one rebase around the complete reverse product of input-letter factors.
@isnad1 id=other.6h7v.s10.96aed3562a82 from=translated src=- shape=7e61e80b vocab=b1f741d6
-/
theorem leftBoundaryFramedBlocks_eq_rebaseLetterChain
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (Fhom : Path.Homotopy
      (binaryVanKampenLetterConcatLoop hxU hxV letters) (Path.refl x₀))
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V
      letters.reverse.length)
    (hn : 0 < letters.reverse.length) :
    let i₀ : Fin letters.reverse.length := ⟨0, hn⟩
    let hL₀ := pathConcatSegmentGridLength_pos letters.reverse.length A.factor
      A.factor_pos i₀
    let start := A.leftBoundaryCombinedStartFrame
      hxU hxV hUV hU hV letters Fhom i₀ ⟨0, hL₀⟩
    let chain := A.leftBoundaryLetterBlockChain
      hxU hxV hUV hU hV letters Fhom
    reverseEdgeChainProduct
        (A.leftBoundaryFramedBlockChain
          hxU hxV hUV hU hV letters Fhom) =
      rebaseEdge start (edgeChainEnd start chain)
        (reverseEdgeChainProduct chain) := by
  dsimp only
  rw [← A.rebasedLetterBlockChain_eq_framedBlocks
    hxU hxV hUV hU hV letters Fhom hn]
  exact rebasedEdgeChainProduct_eq_rebaseEdge _ _

end PathConcatAlignedSquareSubdivision

end SandronesLibrary.Topology
