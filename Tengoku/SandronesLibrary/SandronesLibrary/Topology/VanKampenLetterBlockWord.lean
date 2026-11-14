/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.PathConcatAlignedSubdivision

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# van Kampen 字母 block 的细边词恢复

本文件在单个输入字母指定的覆盖成员中，把 aligned block 的细网格边组成 connector-corrected
基本群词，并证明该词恢复原字母。它不处理 dual-label 比较、kernel 或最终 van Kampen 同构。

当前条目：

* `topology.fundamental-group.van-kampen-letter-block-word`。
-/

open Set
open scoped unitInterval

noncomputable section

namespace SandronesLibrary.Topology

variable {X : Type*} [TopologicalSpace X]

/-- 第 `i` 个输入字母 dyadic block 的第 `r` 个对齐网格顶点，作为该字母覆盖成员中的点。
> **Entry**: topology.fundamental-group.van-kampen-letter-block-word-/
def binaryVanKampenLetterBlockGridVertex
    {U V : Set X} {x₀ : X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (k : ℕ) (hk : 0 < k) (i : Fin letters.reverse.length)
    (r : Fin (pathConcatSegmentGridLength letters.reverse.length k i + 1)) :
    binaryOpenCoverPiece U V (letters.reverse.get i).1 :=
  binaryVanKampenLetterDyadicSegmentInPiece hxU hxV letters i
    (unitIntervalMeshPoint (pathConcatSegmentGridLength letters.reverse.length k i)
      (pathConcatSegmentGridLength_pos letters.reverse.length k hk i) r)

@[simp] theorem binaryVanKampenLetterBlockGridVertex_zero
    {U V : Set X} {x₀ : X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (k : ℕ) (hk : 0 < k) (i : Fin letters.reverse.length) :
    binaryVanKampenLetterBlockGridVertex hxU hxV letters k hk i 0 =
      binaryOpenCoverBasepoint hxU hxV (letters.reverse.get i).1 := by
  apply Subtype.ext
  simp [binaryVanKampenLetterBlockGridVertex]

@[simp] theorem binaryVanKampenLetterBlockGridVertex_last
    {U V : Set X} {x₀ : X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (k : ℕ) (hk : 0 < k) (i : Fin letters.reverse.length) :
    binaryVanKampenLetterBlockGridVertex hxU hxV letters k hk i
        (Fin.last (pathConcatSegmentGridLength letters.reverse.length k i)) =
      binaryOpenCoverBasepoint hxU hxV (letters.reverse.get i).1 := by
  apply Subtype.ext
  simp [binaryVanKampenLetterBlockGridVertex]

/-- 道路连通二开集的任一指定成员中，从公共基点到给定点的一条内部 connector。-/
private noncomputable def binaryOpenCoverPieceConnector
    {U V : Set X} {x₀ : X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (b : Bool) (z : binaryOpenCoverPiece U V b) :
    Path (binaryOpenCoverBasepoint hxU hxV b) z := by
  cases b
  · let q := (hU.joinedIn x₀ hxU z.1 z.2).somePath
    exact pathCodRestrict U q hxU z.2
      (hU.joinedIn x₀ hxU z.1 z.2).somePath_mem
  · let q := (hV.joinedIn x₀ hxV z.1 z.2).somePath
    exact pathCodRestrict V q hxV z.2
      (hV.joinedIn x₀ hxV z.1 z.2).somePath_mem

/-- 在输入字母指定覆盖成员内，从公共基点连接到 dyadic block 的任一对齐网格顶点；首末顶点
规范取常值 connector，中间顶点使用该覆盖成员的道路连通性。-/
noncomputable def binaryVanKampenLetterBlockGridConnector
    {U V : Set X} {x₀ : X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (k : ℕ) (hk : 0 < k) (i : Fin letters.reverse.length)
    (r : Fin (pathConcatSegmentGridLength letters.reverse.length k i + 1)) :
    Path (binaryOpenCoverBasepoint hxU hxV (letters.reverse.get i).1)
      (binaryVanKampenLetterBlockGridVertex hxU hxV letters k hk i r) := by
  by_cases hr0 : r = 0
  · subst r
    exact (Path.refl (binaryOpenCoverBasepoint hxU hxV
      (letters.reverse.get i).1)).cast rfl
        (binaryVanKampenLetterBlockGridVertex_zero hxU hxV letters k hk i)
  by_cases hrlast : r = Fin.last (pathConcatSegmentGridLength letters.reverse.length k i)
  · subst r
    exact (Path.refl (binaryOpenCoverBasepoint hxU hxV
      (letters.reverse.get i).1)).cast rfl
        (binaryVanKampenLetterBlockGridVertex_last hxU hxV letters k hk i)
  exact binaryOpenCoverPieceConnector hxU hxV hU hV
    (letters.reverse.get i).1
    (binaryVanKampenLetterBlockGridVertex hxU hxV letters k hk i r)

@[simp] theorem binaryVanKampenLetterBlockGridConnector_zero
    {U V : Set X} {x₀ : X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (k : ℕ) (hk : 0 < k) (i : Fin letters.reverse.length) :
    binaryVanKampenLetterBlockGridConnector hxU hxV hU hV letters k hk i 0 =
      (Path.refl (binaryOpenCoverBasepoint hxU hxV
        (letters.reverse.get i).1)).cast rfl
          (binaryVanKampenLetterBlockGridVertex_zero hxU hxV letters k hk i) := by
  rw [binaryVanKampenLetterBlockGridConnector, dite_eq_left rfl]

@[simp] theorem binaryVanKampenLetterBlockGridConnector_last
    {U V : Set X} {x₀ : X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (k : ℕ) (hk : 0 < k) (i : Fin letters.reverse.length) :
    binaryVanKampenLetterBlockGridConnector hxU hxV hU hV letters k hk i
        (Fin.last (pathConcatSegmentGridLength letters.reverse.length k i)) =
      (Path.refl (binaryOpenCoverBasepoint hxU hxV
        (letters.reverse.get i).1)).cast rfl
          (binaryVanKampenLetterBlockGridVertex_last hxU hxV letters k hk i) := by
  have hne : (Fin.last (pathConcatSegmentGridLength letters.reverse.length k i) :
      Fin (pathConcatSegmentGridLength letters.reverse.length k i + 1)) ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_last, Fin.val_zero] at this
    exact (Nat.ne_of_gt (pathConcatSegmentGridLength_pos
      letters.reverse.length k hk i)) this
  rw [binaryVanKampenLetterBlockGridConnector, dite_eq_right hne, dite_eq_left rfl]

/-- 把一个字母成员内的 dyadic block 视为 VK2 的全空间一维细分；其标准子道路正是局部细网格边。-/
private def binaryVanKampenLetterBlockGridSubdivision
    {U V : Set X} {x₀ : X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (k : ℕ) (hk : 0 < k) (i : Fin letters.reverse.length) :
    Path.BinaryOpenCoverSubdivision
      (binaryVanKampenLetterDyadicSegmentInPiece hxU hxV letters i)
      (Set.univ : Set (binaryOpenCoverPiece U V (letters.reverse.get i).1))
      Set.univ where
  steps := pathConcatSegmentGridLength letters.reverse.length k i
  steps_pos := pathConcatSegmentGridLength_pos letters.reverse.length k hk i
  label _ := false
  subpath_mem _ _ := Set.mem_univ _

/-- 上述全空间 block 细分的端点规范 `BasedConnectors`。-/
private noncomputable def binaryVanKampenLetterBlockGridBasedConnectors
    {U V : Set X} {x₀ : X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (k : ℕ) (hk : 0 < k) (i : Fin letters.reverse.length) :
    (binaryVanKampenLetterBlockGridSubdivision hxU hxV letters k hk i).BasedConnectors where
  connector := by
    intro r
    change Fin (pathConcatSegmentGridLength letters.reverse.length k i + 1) at r
    exact binaryVanKampenLetterBlockGridConnector
      hxU hxV hU hV letters k hk i r
  left_mem _ _ := Set.mem_univ _
  right_mem _ _ := Set.mem_univ _
  connector_zero := by
    apply Path.ext
    funext t
    change (binaryVanKampenLetterBlockGridConnector
      hxU hxV hU hV letters k hk i 0) t = _
    rw [binaryVanKampenLetterBlockGridConnector_zero, Path.cast_coe]
    unfold Path.BinaryOpenCoverSubdivision.firstReflConnector
    rw [Path.cast_coe]
  connector_last := by
    apply Path.ext
    funext t
    change (binaryVanKampenLetterBlockGridConnector
      hxU hxV hU hV letters k hk i
        (Fin.last (pathConcatSegmentGridLength letters.reverse.length k i))) t = _
    rw [binaryVanKampenLetterBlockGridConnector_last, Path.cast_coe]
    unfold Path.BinaryOpenCoverSubdivision.lastReflConnector
    rw [Path.cast_coe]

/-- 输入字母指定覆盖成员中的第 `s` 条 dyadic block 细网格边。-/
def binaryVanKampenLetterBlockGridEdgeInPiece
    {U V : Set X} {x₀ : X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (k : ℕ) (hk : 0 < k) (i : Fin letters.reverse.length)
    (s : Fin (pathConcatSegmentGridLength letters.reverse.length k i)) :
    Path
      (binaryVanKampenLetterBlockGridVertex hxU hxV letters k hk i s.castSucc)
      (binaryVanKampenLetterBlockGridVertex hxU hxV letters k hk i s.succ) :=
  (binaryVanKampenLetterDyadicSegmentInPiece hxU hxV letters i).subpath
    (unitIntervalMeshPoint (pathConcatSegmentGridLength letters.reverse.length k i)
      (pathConcatSegmentGridLength_pos letters.reverse.length k hk i) s.castSucc)
    (unitIntervalMeshPoint (pathConcatSegmentGridLength letters.reverse.length k i)
      (pathConcatSegmentGridLength_pos letters.reverse.length k hk i) s.succ)

/-- 字母成员内的每条细网格边，严格等于提升后的 dyadic segment 在局部一致网格上的子道路。-/
theorem binaryVanKampenLetterBlockGridEdgeInPiece_eq_subpath
    {U V : Set X} {x₀ : X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (k : ℕ) (hk : 0 < k) (i : Fin letters.reverse.length)
    (s : Fin (pathConcatSegmentGridLength letters.reverse.length k i)) :
    binaryVanKampenLetterBlockGridEdgeInPiece hxU hxV letters k hk i s =
      (binaryVanKampenLetterDyadicSegmentInPiece hxU hxV letters i).subpath
        (unitIntervalMeshPoint (pathConcatSegmentGridLength letters.reverse.length k i)
          (pathConcatSegmentGridLength_pos letters.reverse.length k hk i) s.castSucc)
        (unitIntervalMeshPoint (pathConcatSegmentGridLength letters.reverse.length k i)
          (pathConcatSegmentGridLength_pos letters.reverse.length k hk i) s.succ) := rfl

/-- 一个输入字母 dyadic block 在该字母覆盖成员中的完整 corrected-loop word。-/
def binaryVanKampenLetterBlockGridWord
    {U V : Set X} {x₀ : X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (k : ℕ) (hk : 0 < k) (i : Fin letters.reverse.length) :
    FundamentalGroup (binaryOpenCoverPiece U V (letters.reverse.get i).1)
      (binaryOpenCoverBasepoint hxU hxV (letters.reverse.get i).1) :=
  Path.correctedLoopWord
    (binaryVanKampenLetterBlockGridVertex hxU hxV letters k hk i)
    (binaryVanKampenLetterBlockGridEdgeInPiece hxU hxV letters k hk i)
    (binaryVanKampenLetterBlockGridConnector hxU hxV hU hV letters k hk i)

/-- 上述 block word 等于首末规范 connector 围住的整块网格边拼接类。-/
theorem binaryVanKampenLetterBlockGridWord_eq_concat
    {U V : Set X} {x₀ : X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (k : ℕ) (hk : 0 < k) (i : Fin letters.reverse.length) :
    binaryVanKampenLetterBlockGridWord hxU hxV hU hV letters k hk i =
      FundamentalGroup.fromPath
        ⟦Path.correctedLoop
          (binaryVanKampenLetterBlockGridConnector hxU hxV hU hV letters k hk i 0)
          (Path.concat
            (binaryVanKampenLetterBlockGridVertex hxU hxV letters k hk i)
            (binaryVanKampenLetterBlockGridEdgeInPiece hxU hxV letters k hk i))
          (binaryVanKampenLetterBlockGridConnector hxU hxV hU hV letters k hk i
            (Fin.last (pathConcatSegmentGridLength letters.reverse.length k i)))⟧ := by
  exact Path.correctedLoopWord_eq_concat
    (binaryVanKampenLetterBlockGridVertex hxU hxV letters k hk i)
    (binaryVanKampenLetterBlockGridEdgeInPiece hxU hxV letters k hk i)
    (binaryVanKampenLetterBlockGridConnector hxU hxV hU hV letters k hk i)

/-- 固定字母成员中的完整 dyadic block 细网格词，严格等于该输入字母的基本群元素。-/
theorem binaryVanKampenLetterBlockGridWord_eq_letter
    {U V : Set X} {x₀ : X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (letters : List (BinaryVanKampenLetter U V hxU hxV))
    (k : ℕ) (hk : 0 < k) (i : Fin letters.reverse.length) :
    binaryVanKampenLetterBlockGridWord hxU hxV hU hV letters k hk i =
      (letters.reverse.get i).2 := by
  let D := binaryVanKampenLetterBlockGridSubdivision hxU hxV letters k hk i
  let C := binaryVanKampenLetterBlockGridBasedConnectors
    hxU hxV hU hV letters k hk i
  let γ := binaryVanKampenLetterDyadicSegmentInPiece hxU hxV letters i
  have hword := D.correctedLoopWord_eq_loop C
  have hword' : binaryVanKampenLetterBlockGridWord
      hxU hxV hU hV letters k hk i = FundamentalGroup.fromPath ⟦γ⟧ := by
    unfold binaryVanKampenLetterBlockGridWord
    dsimp [D, C, binaryVanKampenLetterBlockGridSubdivision,
      binaryVanKampenLetterBlockGridBasedConnectors] at hword
    convert hword using 1 <;> rfl
  rw [hword']
  have hhom := binaryVanKampenLetterDyadicSegmentInPiece_homotopic_representative
    hxU hxV letters i
  have hmk : Path.Homotopic.Quotient.mk γ =
      Path.Homotopic.Quotient.mk
        (fundamentalGroupPathRepresentative
          (binaryOpenCoverBasepoint hxU hxV (letters.reverse.get i).1)
          (letters.reverse.get i).2) := Quotient.sound hhom
  calc
    FundamentalGroup.fromPath ⟦γ⟧ =
        FundamentalGroup.fromPath
          ⟦fundamentalGroupPathRepresentative
            (binaryOpenCoverBasepoint hxU hxV (letters.reverse.get i).1)
            (letters.reverse.get i).2⟧ :=
      congrArg FundamentalGroup.fromPath hmk
    _ = (letters.reverse.get i).2 :=
      fundamentalGroupPathRepresentative_mk _ _

end SandronesLibrary.Topology
