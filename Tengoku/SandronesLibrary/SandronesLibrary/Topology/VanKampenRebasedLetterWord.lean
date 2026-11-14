/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.VanKampenGlobalBlockTelescope

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# van Kampen 真实左边界与 rebased 字母词

本文件把每个 dyadic block 的真实左边界细边拼接识别为原输入道路 segment，证明两层反序有限乘积
恢复原 `binaryVanKampenLetterWord`，并将完整真实网格左边界词改写为该原字母词在全局首末 frames
下的一次 rebase。右锚定网格左边界消失最终给出这个 rebased 字母词等于一。

本文件不证明首末 residual frames 相等或可消去，也不证明 kernel 平凡、规范同态单射或最终
van Kampen 同构。

当前条目：`topology.fundamental-group.van-kampen-rebased-letter-word`。
-/

open Set
open scoped unitInterval

noncomputable section

namespace SandronesLibrary.Topology

variable {X : Type*} [TopologicalSpace X]

/-- 将真实最左网格边 transport 到输入道路对应细网格子区间的规范端点。

> **Entry**: topology.fundamental-group.van-kampen-rebased-letter-word-/
private def PathConcatAlignedSquareSubdivision.leftBoundarySegmentGridEdge
    {x₀ x₁ : X} {p q : Path x₀ x₁} (Fhom : Path.Homotopy p q)
    {U V : Set X} {n : ℕ}
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V n)
    (i : Fin n) (s : Fin (pathConcatSegmentGridLength n A.factor i)) :
    Path
      (p (pathConcatSegmentMeshPoint n A.factor A.factor_pos i s.castSucc))
      (p (pathConcatSegmentMeshPoint n A.factor A.factor_pos i s.succ)) :=
  (squareGridVerticalEdge (pathHomotopySquare Fhom)
      A.subdivision.steps A.subdivision.steps_pos 0
      (A.segmentGridEdgeIndex i s)).cast
    (by
      simp only [squareGridVertex, unitIntervalMeshPoint_zero,
        pathHomotopySquare_zero_left,
        A.unitIntervalMeshPoint_segmentGridEdgeIndex_castSucc])
    (by
      simp only [squareGridVertex, unitIntervalMeshPoint_zero,
        pathHomotopySquare_zero_left,
        A.unitIntervalMeshPoint_segmentGridEdgeIndex_succ])

/-- transport 后的真实最左网格边严格等于输入道路的 Mathlib 子道路。-/
private theorem PathConcatAlignedSquareSubdivision.leftBoundarySegmentGridEdge_eq_subpath
    {x₀ x₁ : X} {p q : Path x₀ x₁} (Fhom : Path.Homotopy p q)
    {U V : Set X} {n : ℕ}
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V n)
    (i : Fin n) (s : Fin (pathConcatSegmentGridLength n A.factor i)) :
    A.leftBoundarySegmentGridEdge Fhom i s =
      p.subpath
        (pathConcatSegmentMeshPoint n A.factor A.factor_pos i s.castSucc)
        (pathConcatSegmentMeshPoint n A.factor A.factor_pos i s.succ) := by
  apply Path.ext
  funext t
  unfold PathConcatAlignedSquareSubdivision.leftBoundarySegmentGridEdge
  rw [Path.cast_coe]
  exact A.leftBoundarySegmentGridEdge_apply Fhom i s t

/-- 同一个 concat segment 覆盖的全部真实最左网格边，按细网格顺序拼接。-/
private def PathConcatAlignedSquareSubdivision.leftBoundarySegmentGridConcat
    {x₀ x₁ : X} {p q : Path x₀ x₁} (Fhom : Path.Homotopy p q)
    {U V : Set X} {n : ℕ}
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V n)
    (i : Fin n) :
    Path
      (p (pathConcatSegmentMeshPoint n A.factor A.factor_pos i 0))
      (p (pathConcatSegmentMeshPoint n A.factor A.factor_pos i
        (Fin.last (pathConcatSegmentGridLength n A.factor i)))) :=
  Path.concat
    (p ∘ pathConcatSegmentMeshPoint n A.factor A.factor_pos i)
    (fun s => A.leftBoundarySegmentGridEdge Fhom i s)

/-- 一个 concat segment 内全部真实最左网格边的拼接，同伦于输入道路在该整个 dyadic block 上的
子道路。-/
private theorem PathConcatAlignedSquareSubdivision.leftBoundarySegmentGridConcat_homotopic_subpath
    {x₀ x₁ : X} {p q : Path x₀ x₁} (Fhom : Path.Homotopy p q)
    {U V : Set X} {n : ℕ}
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V n)
    (i : Fin n) :
    (A.leftBoundarySegmentGridConcat Fhom i).Homotopic
      (p.subpath
        (pathConcatSegmentMeshPoint n A.factor A.factor_pos i 0)
        (pathConcatSegmentMeshPoint n A.factor A.factor_pos i
          (Fin.last (pathConcatSegmentGridLength n A.factor i)))) := by
  have hedge : ∀ s : Fin (pathConcatSegmentGridLength n A.factor i),
      (A.leftBoundarySegmentGridEdge Fhom i s).Homotopic
        (p.subpath
          (pathConcatSegmentMeshPoint n A.factor A.factor_pos i s.castSucc)
          (pathConcatSegmentMeshPoint n A.factor A.factor_pos i s.succ)) := by
    intro s
    rw [A.leftBoundarySegmentGridEdge_eq_subpath Fhom i s]
  exact (Path.Homotopic.concat_hcomp
    (p ∘ pathConcatSegmentMeshPoint n A.factor A.factor_pos i)
    (fun s => A.leftBoundarySegmentGridEdge Fhom i s)
    (fun s => p.subpath
      (pathConcatSegmentMeshPoint n A.factor A.factor_pos i s.castSucc)
      (pathConcatSegmentMeshPoint n A.factor A.factor_pos i s.succ)) hedge).trans
    (Path.concatSegmentMeshSubpaths_homotopic p n A.factor A.factor_pos i)

/-- 当同伦起始道路本身是 `Path.concat vertices segments` 时，把一整个真实左边界网格块 transport
回对应输入 segment 的规范端点。-/
private def PathConcatAlignedSquareSubdivision.leftBoundaryConcatDyadicSegment
    {Y : Type*} [TopologicalSpace Y] {n : ℕ}
    (vertices : Fin (n + 1) → Y)
    (segments : (i : Fin n) → Path (vertices i.castSucc) (vertices i.succ))
    {q : Path (vertices 0) (vertices (Fin.last n))}
    (Fhom : Path.Homotopy (Path.concat vertices segments) q)
    {U V : Set Y}
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V n)
    (i : Fin n) : Path (vertices i.castSucc) (vertices i.succ) :=
  (A.leftBoundarySegmentGridConcat Fhom i).cast
    (by rw [pathConcatSegmentMeshPoint_zero,
      Path.concat_breakpoint_apply vertices segments i.castSucc])
    (by rw [pathConcatSegmentMeshPoint_last,
      Path.concat_breakpoint_apply vertices segments i.succ])

/-- 真实左边界的第 `i` 个完整 dyadic 网格块，同伦于原始输入 `segments i`。-/
theorem PathConcatAlignedSquareSubdivision.leftBoundaryConcatDyadicSegment_homotopic
    {Y : Type*} [TopologicalSpace Y] {n : ℕ}
    (vertices : Fin (n + 1) → Y)
    (segments : (i : Fin n) → Path (vertices i.castSucc) (vertices i.succ))
    {q : Path (vertices 0) (vertices (Fin.last n))}
    (Fhom : Path.Homotopy (Path.concat vertices segments) q)
    {U V : Set Y}
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V n)
    (i : Fin n) :
    (A.leftBoundaryConcatDyadicSegment vertices segments Fhom i).Homotopic
      (segments i) := by
  let γ := Path.concat vertices segments
  have hblock := A.leftBoundarySegmentGridConcat_homotopic_subpath Fhom i
  have hsource : vertices i.castSucc = γ
      (pathConcatSegmentMeshPoint n A.factor A.factor_pos i 0) := by
    rw [pathConcatSegmentMeshPoint_zero,
      Path.concat_breakpoint_apply vertices segments i.castSucc]
  have htarget : vertices i.succ = γ
      (pathConcatSegmentMeshPoint n A.factor A.factor_pos i
        (Fin.last (pathConcatSegmentGridLength n A.factor i))) := by
    rw [pathConcatSegmentMeshPoint_last,
      Path.concat_breakpoint_apply vertices segments i.succ]
  have hcast := hblock.pathCast hsource htarget
  have hright :
      ((γ.subpath
        (pathConcatSegmentMeshPoint n A.factor A.factor_pos i 0)
        (pathConcatSegmentMeshPoint n A.factor A.factor_pos i
          (Fin.last (pathConcatSegmentGridLength n A.factor i)))).cast hsource htarget) =
        Path.concatDyadicSegment vertices segments i := by
    apply Path.ext
    funext t
    change γ (Set.Icc.convexComb
      (pathConcatSegmentMeshPoint n A.factor A.factor_pos i 0)
      (pathConcatSegmentMeshPoint n A.factor A.factor_pos i
        (Fin.last (pathConcatSegmentGridLength n A.factor i))) t) =
      γ (Set.Icc.convexComb
        (pathConcatBreakpoint n i.castSucc)
        (pathConcatBreakpoint n i.succ) t)
    rw [pathConcatSegmentMeshPoint_zero, pathConcatSegmentMeshPoint_last]
  have hleft : A.leftBoundaryConcatDyadicSegment vertices segments Fhom i =
      (A.leftBoundarySegmentGridConcat Fhom i).cast hsource htarget := by
    apply Path.ext
    funext t
    rfl
  rw [hleft]
  exact hcast.trans (by
    rw [hright]
    exact Path.concatDyadicSegment_homotopic vertices segments i)

/-- 对反序列表取数组后做上述左乘 fold，恢复原列表映射后的乘积。-/
theorem reverseDfoldl_reverse_get_eq_map_prod
    {G : Type*} [Group G] (value : α → G) (items : List α) :
    Fin.dfoldl items.reverse.length (fun _ => G)
        (fun i acc => value (items.reverse.get i) * acc) 1 =
      (items.map value).prod := by
  rw [reverseDfoldl_eq_reverse_ofFn_prod]
  have hofn : List.ofFn (fun i => value (items.reverse.get i)) =
      items.reverse.map value := by
    simpa only [List.get_eq_getElem] using
      (List.ofFn_getElem_eq_map items.reverse value)
  rw [hofn]
  simp

/-- The recursive interpretation of a Pushout letter word is the ordinary list
product of the injected letter values.-/
theorem binaryVanKampenLetterWord_eq_map_prod
    {U V : Set X} {x₀ : X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV)) :
    binaryVanKampenLetterWord U V hxU hxV letters =
      (letters.map fun letter =>
        (Monoid.PushoutI.of letter.1 letter.2 :
          binaryVanKampenPushout U V hxU hxV)).prod := by
  induction letters with
  | nil => rfl
  | cons letter rest ih =>
      rcases letter with ⟨b, g⟩
      simp only [binaryVanKampenLetterWord, List.map_cons, List.prod_cons]
      rw [ih]

/-- The raw reverse product in the second-level block chain is exactly the
original, unreversed input Pushout word.-/
private theorem PathConcatAlignedSquareSubdivision.reverseLeftBoundaryLetterBlockChain_eq_word
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (Fhom : Path.Homotopy
      (binaryVanKampenLetterConcatLoop hxU hxV letters) (Path.refl x₀))
    (A : PathConcatAlignedSquareSubdivision (pathHomotopySquare Fhom) U V
      letters.reverse.length) :
    reverseEdgeChainProduct
        (A.leftBoundaryLetterBlockChain
          hxU hxV hUV hU hV letters Fhom) =
      binaryVanKampenLetterWord U V hxU hxV letters := by
  rw [reverseEdgeChainProduct_eq_reverse_map_snd_prod,
    binaryVanKampenLetterWord_eq_map_prod]
  simp only [PathConcatAlignedSquareSubdivision.leftBoundaryLetterBlockChain,
    List.map_ofFn]
  let value := fun letter : BinaryVanKampenLetter U V hxU hxV =>
    (Monoid.PushoutI.of letter.1 letter.2 :
      binaryVanKampenPushout U V hxU hxV)
  have hofn : List.ofFn (fun i => value (letters.reverse.get i)) =
      letters.reverse.map value := by
    simpa only [List.get_eq_getElem] using
      (List.ofFn_getElem_eq_map letters.reverse value)
  change (List.ofFn (fun i => value (letters.reverse.get i))).reverse.prod =
    (letters.map value).prod
  rw [hofn]
  simp

/-- The completed two-level telescope: the actual framed products of all
left-boundary blocks differ from the original Pushout word only by one global
start/end rebase.-/
theorem PathConcatAlignedSquareSubdivision.leftBoundaryFramedBlocks_eq_rebaseWord
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
        (binaryVanKampenLetterWord U V hxU hxV letters) := by
  dsimp only
  rw [A.leftBoundaryFramedBlocks_eq_rebaseLetterChain
    hxU hxV hUV hU hV letters Fhom hn]
  rw [A.reverseLeftBoundaryLetterBlockChain_eq_word
    hxU hxV hUV hU hV letters Fhom]

/-- The flattened actual fine-edge word on the complete left boundary is the
original Pushout word with only one global start/end change of frame.-/
theorem PathConcatAlignedSquareSubdivision.leftBoundaryAllFramedCellEdges_eq_rebaseWord
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
        (A.leftBoundaryAllFramedCellEdgeChain
          hxU hxV hUV hU hV letters Fhom) =
      rebaseEdge start (edgeChainEnd start chain)
        (binaryVanKampenLetterWord U V hxU hxV letters) := by
  dsimp only
  rw [A.reverseAllFramedCellEdges_eq_framedBlocks
    hxU hxV hUV hU hV letters Fhom]
  exact A.leftBoundaryFramedBlocks_eq_rebaseWord
    hxU hxV hUV hU hV letters Fhom hn

/-- The existing full-grid cancellation theorem now closes the complete
left-boundary telescope: the globally rebased input Pushout word is one.-/
theorem PathConcatAlignedSquareSubdivision.rebasedLetterWord_eq_one
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
    rebaseEdge start (edgeChainEnd start chain)
        (binaryVanKampenLetterWord U V hxU hxV letters) = 1 := by
  dsimp only
  rw [← A.leftBoundaryAllFramedCellEdges_eq_rebaseWord
    hxU hxV hUV hU hV letters Fhom hn]
  rw [A.reverseAllFramedCellEdges_eq_gridLeftBoundaryWord
    hxU hxV hUV hU hV letters Fhom hn]
  exact A.subdivision.rightAnchoredGridFullLeftBoundary_eq_one
    hxU hxV hUV hU hV

end SandronesLibrary.Topology
