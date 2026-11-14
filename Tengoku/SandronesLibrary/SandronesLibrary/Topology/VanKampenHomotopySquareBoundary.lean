/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.VanKampenSurjectivity
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.VanKampenSquareSubdivision
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.HomotopySquareGrid

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# van Kampen 方格细分的单格边界关系

本文件把 Mathlib 的端点相对道路同伦写成参数方形，为一致方格细分的每个单格规定四条有向边，
将单格提升到其 Bool 标签对应的覆盖成员，并用四角 connector 构造 based edge。最终证明每个单格
的左逆、上逆、右正、下正边界词在二开覆盖 Pushout 中等于单位元。

当前条目：

* `topology.fundamental-group.van-kampen-cell-boundary`。

本文件只证明单格局部关系；不证明相邻格公共边抵消、整张网格边界消去、规范同态单射或最终
Seifert--van Kampen 等价。
-/

open Set
open scoped unitInterval

noncomputable section

namespace SandronesLibrary.Topology

variable {X : Type*} [TopologicalSpace X]

/-- 第 `(i,j)` 格的逆时针边界：下边、右边、上边逆、左边逆。

> **Entry**: topology.fundamental-group.van-kampen-cell-boundary-/
def squareGridCellBoundary (H : C(unitInterval × unitInterval, X))
    (N : ℕ) (hN : 0 < N) (i j : Fin N) :
    Path (squareGridVertex H N hN i.castSucc j.castSucc)
      (squareGridVertex H N hN i.castSucc j.castSucc) :=
  (squareGridHorizontalEdge H N hN i j.castSucc).trans
    ((squareGridVerticalEdge H N hN i.succ j).trans
      ((squareGridHorizontalEdge H N hN i j.succ).symm.trans
        (squareGridVerticalEdge H N hN i.castSucc j).symm))

/-- 单格边界的每一点位于该格标签指定的覆盖成员。
@isnad1 id=mem.0h8v.s8.8ec3b99e8e46 from=translated src=- shape=0b8a815d vocab=53712e33
-/
theorem BinaryOpenCoverSquareSubdivision.gridCellBoundary_mem
    {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V) (i j : Fin D.steps)
    (t : unitInterval) :
    squareGridCellBoundary H D.steps D.steps_pos i j t ∈
      binaryOpenCoverPiece U V (D.label i j) := by
  simp only [squareGridCellBoundary, Path.trans_apply, squareGridHorizontalEdge,
    squareGridVerticalEdge, Path.symm_apply]
  split_ifs with h₁ h₂ h₃
  · change H (Set.Icc.convexComb
        (unitIntervalMeshPoint D.steps D.steps_pos i.castSucc)
        (unitIntervalMeshPoint D.steps D.steps_pos i.succ) _,
      unitIntervalMeshPoint D.steps D.steps_pos j.castSucc) ∈
        binaryOpenCoverPiece U V (D.label i j)
    simpa only [unitSquareCellPoint, Set.Icc.convexComb_zero] using D.cell_mem i j _ 0
  · change H (unitIntervalMeshPoint D.steps D.steps_pos i.succ,
      Set.Icc.convexComb
        (unitIntervalMeshPoint D.steps D.steps_pos j.castSucc)
        (unitIntervalMeshPoint D.steps D.steps_pos j.succ) _) ∈
        binaryOpenCoverPiece U V (D.label i j)
    simpa only [unitSquareCellPoint, Set.Icc.convexComb_one] using D.cell_mem i j 1 _
  · change H (Set.Icc.convexComb
        (unitIntervalMeshPoint D.steps D.steps_pos i.castSucc)
        (unitIntervalMeshPoint D.steps D.steps_pos i.succ) _,
      unitIntervalMeshPoint D.steps D.steps_pos j.succ) ∈
        binaryOpenCoverPiece U V (D.label i j)
    simpa only [unitSquareCellPoint, Set.Icc.convexComb_one] using D.cell_mem i j _ 1
  · change H (unitIntervalMeshPoint D.steps D.steps_pos i.castSucc,
      Set.Icc.convexComb
        (unitIntervalMeshPoint D.steps D.steps_pos j.castSucc)
        (unitIntervalMeshPoint D.steps D.steps_pos j.succ) _) ∈
        binaryOpenCoverPiece U V (D.label i j)
    simpa only [unitSquareCellPoint, Set.Icc.convexComb_zero] using D.cell_mem i j 0 _

/-- 把第 `(i,j)` 格的连续映射提升到其标签指定的覆盖成员。-/
def BinaryOpenCoverSquareSubdivision.gridCellMapInPiece
    {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V) (i j : Fin D.steps) :
    C(unitInterval × unitInterval, binaryOpenCoverPiece U V (D.label i j)) where
  toFun z := ⟨H (unitSquareCellPoint D.steps D.steps_pos i j z.1 z.2),
    D.cell_mem i j z.1 z.2⟩
  continuous_toFun := by unfold unitSquareCellPoint; fun_prop

def BinaryOpenCoverSquareSubdivision.gridCellMapToSpace
    {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V) (i j : Fin D.steps) :
    C(unitInterval × unitInterval, X) :=
  (⟨Subtype.val, continuous_subtype_val⟩ :
    C(binaryOpenCoverPiece U V (D.label i j), X)).comp (D.gridCellMapInPiece i j)

/-- 标准单位方形的逆时针边界参数环路。
@isnad1 id=lt.0h0v.s3.a369faea5e76 from=translated src=- shape=91ed63c4 vocab=7f9bb019
-/
theorem unitSquareOnePos : 0 < (1 : ℕ) := by omega

def unitSquareBoundaryLoop :=
  squareGridCellBoundary (ContinuousMap.id (unitInterval × unitInterval)) 1 unitSquareOnePos 0 0

abbrev unitSquareBoundaryBasepoint : unitInterval × unitInterval :=
  squareGridVertex (ContinuousMap.id (unitInterval × unitInterval)) 1 unitSquareOnePos 0 0

/-- 单位方形中的任意基环路沿逐坐标凸组合收缩到基点，并固定端点。-/
def contractUnitSquareLoop {c : unitInterval × unitInterval} (P : Path c c) :
    Path.Homotopy P (Path.refl c) where
  toFun z :=
    (Set.Icc.convexComb (P z.2).1 c.1 z.1,
      Set.Icc.convexComb (P z.2).2 c.2 z.1)
  continuous_toFun := by fun_prop
  map_zero_left t := by simp
  map_one_left t := by simp
  prop' s t ht := by
    rcases ht with rfl | ht
    · simp [P.source]
    · rw [Set.mem_singleton_iff] at ht
      subst t
      simp [P.target]

/-- 全局四边定义的单格边界等于标准方形边界经该格映射后的像。
@isnad1 id=eq.0h8v.s10.65d035b9cccd from=translated src=- shape=ebb4857f vocab=3cf384aa
-/
theorem BinaryOpenCoverSquareSubdivision.gridCellBoundary_eq_map_unitSquareBoundary
    {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V) (i j : Fin D.steps)
    (t : unitInterval) :
    squareGridCellBoundary H D.steps D.steps_pos i j t =
      (unitSquareBoundaryLoop.map (D.gridCellMapToSpace i j).continuous) t := by
  change squareGridCellBoundary H D.steps D.steps_pos i j t =
    D.gridCellMapToSpace i j (unitSquareBoundaryLoop t)
  unfold unitSquareBoundaryLoop squareGridCellBoundary
  simp only [Path.trans_apply, squareGridHorizontalEdge, squareGridVerticalEdge,
    Path.symm_apply, Function.comp_apply]
  unfold BinaryOpenCoverSquareSubdivision.gridCellMapToSpace
    BinaryOpenCoverSquareSubdivision.gridCellMapInPiece unitSquareCellPoint
  simp only [ContinuousMap.coe_mk, ContinuousMap.comp_apply]
  split_ifs <;> simp [unitIntervalMeshPoint]

/-- 单格全局边界提升到其标签指定覆盖成员后的环路。-/
def BinaryOpenCoverSquareSubdivision.gridCellBoundaryInPiece
    {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V) (i j : Fin D.steps) :=
  unitSquareBoundaryLoop.map (D.gridCellMapInPiece i j).continuous

/-- 提升后的全局四边环路在相应覆盖成员内部端点相对收缩。-/
def BinaryOpenCoverSquareSubdivision.gridCellBoundaryHomotopyInPiece
    {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V) (i j : Fin D.steps) :=
  (contractUnitSquareLoop unitSquareBoundaryLoop).map (D.gridCellMapInPiece i j)

/-- 每个全局四边单格关系在相应覆盖成员基本群中等于单位元。
@isnad1 id=eq.0h7v.s11.1020145ea8e1 from=translated src=- shape=c4a6a2bb vocab=9a7560ec
-/
theorem BinaryOpenCoverSquareSubdivision.gridCellBoundaryInPiece_eq_one
    {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V) (i j : Fin D.steps) :
    FundamentalGroup.fromPath ⟦D.gridCellBoundaryInPiece i j⟧ = 1 := by
  have hh : Path.Homotopic (D.gridCellBoundaryInPiece i j) _ :=
    ⟨D.gridCellBoundaryHomotopyInPiece i j⟩
  have h : Path.Homotopic.Quotient.mk (D.gridCellBoundaryInPiece i j) =
      Path.Homotopic.Quotient.mk _ := Quotient.sound hh
  change Path.Homotopic.Quotient.mk (D.gridCellBoundaryInPiece i j) =
    Path.Homotopic.Quotient.refl _
  calc
    _ = Path.Homotopic.Quotient.mk _ := h
    _ = Path.Homotopic.Quotient.mk (Path.refl _) := by
      apply congr_arg Path.Homotopic.Quotient.mk
      ext t
      rfl
    _ = Path.Homotopic.Quotient.refl _ := Path.Homotopic.Quotient.mk_refl _

/--
@isnad1 id=eq.0h7v.s6.b367ae8ed37d from=translated src=- shape=7065d413 vocab=cf30e8f9
-/
theorem correctedLoop_reverse_eq_inv {x₀ z w : X}
    (left : Path x₀ z) (segment : Path z w) (right : Path x₀ w) :
    FundamentalGroup.fromPath ⟦Path.correctedLoop right segment.symm left⟧ =
      (FundamentalGroup.fromPath ⟦Path.correctedLoop left segment right⟧)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [Path.correctedLoop_product left segment right segment.symm left]
  rw [FundamentalGroup.one_def]
  unfold Path.correctedLoop FundamentalGroup.fromPath FundamentalGroup.fromArrow
  simp

/-- 标准单位格的四个网格顶点；`a,b : Fin 2` 分别选择横纵坐标 `0/1`。-/
abbrev unitSquareGridVertex (a b : Fin 2) : unitInterval × unitInterval :=
  squareGridVertex (ContinuousMap.id (unitInterval × unitInterval)) 1 unitSquareOnePos a b

/-- 第 `(i,j)` 格的一个角在其标签覆盖成员中的提升。-/
abbrev BinaryOpenCoverSquareSubdivision.gridCellVertexInPiece
    {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V) (i j : Fin D.steps)
    (a b : Fin 2) : binaryOpenCoverPiece U V (D.label i j) :=
  (D.gridCellMapInPiece i j) (unitSquareGridVertex a b)

def BinaryOpenCoverSquareSubdivision.gridCellVertexInPieceOfLabel
    {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V) (i j : Fin D.steps)
    (a b : Fin 2) (label : Bool) (hlabel : D.label i j = label) :
    binaryOpenCoverPiece U V label := by
  cases hlabel
  exact D.gridCellVertexInPiece i j a b

/-- 沿显式标签，在单格覆盖成员内连接公共基点到指定角。-/
def BinaryOpenCoverSquareSubdivision.gridCellVertexConnectorInPieceOfLabel
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j : Fin D.steps) (a b : Fin 2) (label : Bool)
    (hlabel : D.label i j = label) :
    Path (binaryOpenCoverBasepoint hxU hxV label)
      (D.gridCellVertexInPieceOfLabel i j a b label hlabel) := by
  cases label
  · let z := D.gridCellVertexInPieceOfLabel i j a b false hlabel
    let q := (hU.joinedIn x₀ hxU z.1 z.2).somePath
    exact pathCodRestrict U q hxU z.2 (hU.joinedIn x₀ hxU z.1 z.2).somePath_mem
  · let z := D.gridCellVertexInPieceOfLabel i j a b true hlabel
    let q := (hV.joinedIn x₀ hxV z.1 z.2).somePath
    exact pathCodRestrict V q hxV z.2 (hV.joinedIn x₀ hxV z.1 z.2).somePath_mem

/-- 沿单格实际标签得到的公共基点到指定角的覆盖成员内部连接。-/
def BinaryOpenCoverSquareSubdivision.gridCellVertexConnectorInPiece
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j : Fin D.steps) (a b : Fin 2) :
    Path (binaryOpenCoverBasepoint hxU hxV (D.label i j))
      (D.gridCellVertexInPiece i j a b) :=
  D.gridCellVertexConnectorInPieceOfLabel hxU hxV hU hV i j a b
    (D.label i j) rfl

/-- 同一格角 connector 使用任意两个显式标签证明时，送回底层空间后的道路函数相同。
@isnad1 id=eq.6h13v.s8.40cba4fad097 from=translated src=- shape=83d04831 vocab=ed1346e1
-/
theorem BinaryOpenCoverSquareSubdivision.coe_gridCellVertexConnectorInPieceOfLabel_eq
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j : Fin D.steps) (a b : Fin 2)
    (label₁ label₂ : Bool) (hlabel₁ : D.label i j = label₁)
    (hlabel₂ : D.label i j = label₂) (t : unitInterval) :
    ((D.gridCellVertexConnectorInPieceOfLabel hxU hxV hU hV
      i j a b label₁ hlabel₁ t : binaryOpenCoverPiece U V label₁) : X) =
    ((D.gridCellVertexConnectorInPieceOfLabel hxU hxV hU hV
      i j a b label₂ hlabel₂ t : binaryOpenCoverPiece U V label₂) : X) := by
  cases hlabel₁
  cases hlabel₂
  rfl

/-- 单格内从左到右的横边在公共覆盖基点处的修正基本群元素。-/
def BinaryOpenCoverSquareSubdivision.gridCellBasedHorizontalEdgeInPiece
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j : Fin D.steps) (row : Fin 2) :
    FundamentalGroup (binaryOpenCoverPiece U V (D.label i j))
      (binaryOpenCoverBasepoint hxU hxV (D.label i j)) :=
  FundamentalGroup.fromPath ⟦Path.correctedLoop
    (D.gridCellVertexConnectorInPiece hxU hxV hU hV i j 0 row)
    ((squareGridHorizontalEdge (ContinuousMap.id (unitInterval × unitInterval))
      1 unitSquareOnePos 0 row).map (D.gridCellMapInPiece i j).continuous)
    (D.gridCellVertexConnectorInPiece hxU hxV hU hV i j 1 row)⟧

/-- 单格内从下到上的竖边在公共覆盖基点处的修正基本群元素。-/
def BinaryOpenCoverSquareSubdivision.gridCellBasedVerticalEdgeInPiece
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j : Fin D.steps) (column : Fin 2) :
    FundamentalGroup (binaryOpenCoverPiece U V (D.label i j))
      (binaryOpenCoverBasepoint hxU hxV (D.label i j)) :=
  FundamentalGroup.fromPath ⟦Path.correctedLoop
    (D.gridCellVertexConnectorInPiece hxU hxV hU hV i j column 0)
    ((squareGridVerticalEdge (ContinuousMap.id (unitInterval × unitInterval))
      1 unitSquareOnePos column 0).map (D.gridCellMapInPiece i j).continuous)
    (D.gridCellVertexConnectorInPiece hxU hxV hU hV i j column 1)⟧

/--
@isnad1 id=eq.0h7v.s13.d8af59389ec8 from=translated src=- shape=e1ef79ad vocab=0f6aabee
-/
theorem BinaryOpenCoverSquareSubdivision.gridCellBoundaryInPiece_decompose
    {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V) (i j : Fin D.steps) :
    D.gridCellBoundaryInPiece i j =
      ((squareGridHorizontalEdge (ContinuousMap.id (unitInterval × unitInterval))
        1 unitSquareOnePos 0 0).map (D.gridCellMapInPiece i j).continuous).trans
        (((squareGridVerticalEdge (ContinuousMap.id (unitInterval × unitInterval))
          1 unitSquareOnePos 1 0).map (D.gridCellMapInPiece i j).continuous).trans
          (((squareGridHorizontalEdge (ContinuousMap.id (unitInterval × unitInterval))
            1 unitSquareOnePos 0 1).map (D.gridCellMapInPiece i j).continuous).symm.trans
            ((squareGridVerticalEdge (ContinuousMap.id (unitInterval × unitInterval))
              1 unitSquareOnePos 0 0).map (D.gridCellMapInPiece i j).continuous).symm)) := by
  unfold BinaryOpenCoverSquareSubdivision.gridCellBoundaryInPiece unitSquareBoundaryLoop
    squareGridCellBoundary
  simp only [Path.map_trans]
  rfl

/-- 用左下角连接把单格标准边界搬到公共覆盖基点。-/
def BinaryOpenCoverSquareSubdivision.gridCellBasedBoundaryViaCorners
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j : Fin D.steps) :
    FundamentalGroup (binaryOpenCoverPiece U V (D.label i j))
      (binaryOpenCoverBasepoint hxU hxV (D.label i j)) :=
  FundamentalGroup.fromPath ⟦Path.correctedLoop
    (D.gridCellVertexConnectorInPiece hxU hxV hU hV i j 0 0)
    (D.gridCellBoundaryInPiece i j)
    (D.gridCellVertexConnectorInPiece hxU hxV hU hV i j 0 0)⟧

/--
@isnad1 id=eq.4h8v.s8.f73d7d0ebc43 from=translated src=- shape=aaa2710e vocab=a8210d76
-/
theorem BinaryOpenCoverSquareSubdivision.gridCellBasedBoundaryViaCorners_eq_one
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j : Fin D.steps) :
    D.gridCellBasedBoundaryViaCorners hxU hxV hU hV i j = 1 := by
  let c := D.gridCellVertexConnectorInPiece hxU hxV hU hV i j 0 0
  let s := D.gridCellBoundaryInPiece i j
  change FundamentalGroup.fromPath ⟦Path.correctedLoop c s c⟧ = 1
  rw [FundamentalGroup.one_def]
  change Path.Homotopic.Quotient.mk (Path.correctedLoop c s c) =
    Path.Homotopic.Quotient.refl _
  unfold Path.correctedLoop
  simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm]
  have hs := D.gridCellBoundaryInPiece_eq_one i j
  change Path.Homotopic.Quotient.mk s = Path.Homotopic.Quotient.refl _ at hs
  rw [hs]
  simp

/-- 单格四条 piece 内修正边的反序乘积等于搬基点后的整条单格边界。
@isnad1 id=eq.4h8v.s11.8cb707b3ca5b from=translated src=- shape=438491b8 vocab=29253fed
-/
theorem BinaryOpenCoverSquareSubdivision.gridCellPieceEdgeWord_eq_boundary
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j : Fin D.steps) :
    (D.gridCellBasedVerticalEdgeInPiece hxU hxV hU hV i j 0)⁻¹ *
        (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i j 1)⁻¹ *
        D.gridCellBasedVerticalEdgeInPiece hxU hxV hU hV i j 1 *
        D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i j 0 =
      D.gridCellBasedBoundaryViaCorners hxU hxV hU hV i j := by
  unfold BinaryOpenCoverSquareSubdivision.gridCellBasedHorizontalEdgeInPiece
    BinaryOpenCoverSquareSubdivision.gridCellBasedVerticalEdgeInPiece
    BinaryOpenCoverSquareSubdivision.gridCellBasedBoundaryViaCorners
  rw [← correctedLoop_reverse_eq_inv
    (D.gridCellVertexConnectorInPiece hxU hxV hU hV i j 0 0)
    ((squareGridVerticalEdge (ContinuousMap.id (unitInterval × unitInterval))
      1 unitSquareOnePos 0 0).map (D.gridCellMapInPiece i j).continuous)
    (D.gridCellVertexConnectorInPiece hxU hxV hU hV i j 0 1)]
  rw [← correctedLoop_reverse_eq_inv
    (D.gridCellVertexConnectorInPiece hxU hxV hU hV i j 0 1)
    ((squareGridHorizontalEdge (ContinuousMap.id (unitInterval × unitInterval))
      1 unitSquareOnePos 0 1).map (D.gridCellMapInPiece i j).continuous)
    (D.gridCellVertexConnectorInPiece hxU hxV hU hV i j 1 1)]
  rw [Path.correctedLoop_product,
    Path.correctedLoop_product, Path.correctedLoop_product]
  rw [D.gridCellBoundaryInPiece_decompose i j]

/-- 单格四条 piece 内修正边的反序乘积为单位元。
@isnad1 id=eq.4h8v.s11.38f45bfb6513 from=translated src=- shape=ca6967c6 vocab=39b9f976
-/
theorem BinaryOpenCoverSquareSubdivision.gridCellPieceEdgeWord_eq_one
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j : Fin D.steps) :
    (D.gridCellBasedVerticalEdgeInPiece hxU hxV hU hV i j 0)⁻¹ *
        (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i j 1)⁻¹ *
        D.gridCellBasedVerticalEdgeInPiece hxU hxV hU hV i j 1 *
        D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i j 0 = 1 := by
  rw [D.gridCellPieceEdgeWord_eq_boundary hxU hxV hU hV i j,
    D.gridCellBasedBoundaryViaCorners_eq_one hxU hxV hU hV i j]

/-- 四条单格 piece 边分别进入合并自由积后组成的反序边词。-/
def BinaryOpenCoverSquareSubdivision.gridCellPushoutEdgeWord
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j : Fin D.steps) : binaryVanKampenPushout U V hxU hxV :=
  (Monoid.PushoutI.of (D.label i j)
      (D.gridCellBasedVerticalEdgeInPiece hxU hxV hU hV i j 0))⁻¹ *
    (Monoid.PushoutI.of (D.label i j)
      (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i j 1))⁻¹ *
    Monoid.PushoutI.of (D.label i j)
      (D.gridCellBasedVerticalEdgeInPiece hxU hxV hU hV i j 1) *
    Monoid.PushoutI.of (D.label i j)
      (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i j 0)

/-- 展开成四条边后的每个单格关系在合并自由积中为单位元。
@isnad1 id=eq.4h8v.s8.725c78ac336e from=translated src=- shape=4acd8163 vocab=2d50a66b
-/
theorem BinaryOpenCoverSquareSubdivision.gridCellPushoutEdgeWord_eq_one
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j : Fin D.steps) :
    D.gridCellPushoutEdgeWord hxU hxV hU hV i j = 1 := by
  unfold BinaryOpenCoverSquareSubdivision.gridCellPushoutEdgeWord
  rw [← map_inv, ← map_inv]
  rw [← map_mul, ← map_mul, ← map_mul]
  rw [D.gridCellPieceEdgeWord_eq_one hxU hxV hU hV i j]
  exact map_one (Monoid.PushoutI.of (D.label i j))

end SandronesLibrary.Topology
