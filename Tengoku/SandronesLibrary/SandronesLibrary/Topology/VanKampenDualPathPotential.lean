/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.VanKampenLetterBlockWord

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# van Kampen 双标签道路与顶点 potential

本文件把同时落在二开集两个不同标签中的道路提升到交集，比较交集规范 connector 与成员内局部
connector，并把端点变化统一写成坐标无关的 vertex potentials。它不建立完整 path rebase、左边界
telescope、kernel、单射或最终 van Kampen 同构。

当前条目：

* `topology.fundamental-group.van-kampen-dual-path-potential`。
-/

open Set
open scoped unitInterval

noncomputable section

namespace SandronesLibrary.Topology

variable {X : Type*} [TopologicalSpace X]

omit [TopologicalSpace X] in
/-- 若同一几何点同时属于两个不同标签的二开集成员，则它属于交集。这个小接口把后续逐边
比较中的 Bool 分支集中在一处。

> **Entry**: topology.fundamental-group.van-kampen-dual-path-potential
@isnad1 id=mem.3h6v.s5.a0013979cd46 from=translated src=- shape=d64a2dac vocab=36075a0e
-/
theorem mem_intersection_of_mem_binaryOpenCoverPieces_of_ne
    {U V : Set X} {x : X} {b c : Bool}
    (hb : x ∈ binaryOpenCoverPiece U V b)
    (hc : x ∈ binaryOpenCoverPiece U V c) (hne : b ≠ c) :
    x ∈ U ∩ V := by
  cases b <;> cases c <;> simp_all [binaryOpenCoverPiece]

/-- 一条同时落在两个不同覆盖标签中的道路，规范提升为交集中的道路。-/
def binaryOpenCoverDualPathInIntersection
    {U V : Set X} {z w : X} {b c : Bool} (q : Path z w)
    (hb : ∀ t, q t ∈ binaryOpenCoverPiece U V b)
    (hc : ∀ t, q t ∈ binaryOpenCoverPiece U V c) (hne : b ≠ c) :
    Path
      (⟨z, mem_intersection_of_mem_binaryOpenCoverPieces_of_ne
        (by simpa using hb 0) (by simpa using hc 0) hne⟩ : ↥(U ∩ V))
      (⟨w, mem_intersection_of_mem_binaryOpenCoverPieces_of_ne
        (by simpa using hb 1) (by simpa using hc 1) hne⟩ : ↥(U ∩ V)) where
  toFun t := ⟨q t,
    mem_intersection_of_mem_binaryOpenCoverPieces_of_ne (hb t) (hc t) hne⟩
  continuous_toFun := continuous_induced_rng.mpr q.continuous
  source' := Subtype.ext q.source
  target' := Subtype.ext q.target

/--
@isnad1 id=eq.3h9v.s8.20de2a8a6cf6 from=translated src=- shape=064ba069 vocab=987211a3
-/
@[simp] theorem coe_binaryOpenCoverDualPathInIntersection
    {U V : Set X} {z w : X} {b c : Bool} (q : Path z w)
    (hb : ∀ t, q t ∈ binaryOpenCoverPiece U V b)
    (hc : ∀ t, q t ∈ binaryOpenCoverPiece U V c) (hne : b ≠ c)
    (t : unitInterval) :
    (binaryOpenCoverDualPathInIntersection q hb hc hne t : X) = q t := rfl

/-- 将环境道路按给定成员性提升到某个二开集成员。端点证明由同一个逐点成员性函数产生，便于
后续统一 transport。-/
def binaryOpenCoverPathInPiece
    {U V : Set X} {z w : X} {b : Bool} (q : Path z w)
    (hb : ∀ t, q t ∈ binaryOpenCoverPiece U V b) :
    Path
      (⟨z, by simpa using hb 0⟩ : binaryOpenCoverPiece U V b)
      (⟨w, by simpa using hb 1⟩ : binaryOpenCoverPiece U V b) where
  toFun t := ⟨q t, hb t⟩
  continuous_toFun := continuous_induced_rng.mpr q.continuous
  source' := Subtype.ext q.source
  target' := Subtype.ext q.target

/--
@isnad1 id=eq.1h8v.s8.9c9a67bc45e1 from=translated src=- shape=0b695b59 vocab=fe8e9238
-/
@[simp] theorem coe_binaryOpenCoverPathInPiece
    {U V : Set X} {z w : X} {b : Bool} (q : Path z w)
    (hb : ∀ t, q t ∈ binaryOpenCoverPiece U V b) (t : unitInterval) :
    (binaryOpenCoverPathInPiece q hb t : X) = q t := rfl

/-- 双标签交集道路映入其中任一覆盖成员后，经端点 proof transport，严格恢复直接的成员提升。
这是异标签 Pushout defining relation 与两套局部 corrected-loop 之间的道路桥。-/
private theorem binaryOpenCoverDualPath_map_toPiece_cast_eq
    {U V : Set X} {z w : X} {b c d : Bool} (q : Path z w)
    (hb : ∀ t, q t ∈ binaryOpenCoverPiece U V b)
    (hc : ∀ t, q t ∈ binaryOpenCoverPiece U V c) (hne : b ≠ c)
    (hd : ∀ t, q t ∈ binaryOpenCoverPiece U V d) :
    let qUV := binaryOpenCoverDualPathInIntersection q hb hc hne
    let f := binaryOpenCoverIntersectionToPiece U V d
    let zUV : ↥(U ∩ V) :=
      ⟨z, mem_intersection_of_mem_binaryOpenCoverPieces_of_ne
        (by simpa using hb 0) (by simpa using hc 0) hne⟩
    let wUV : ↥(U ∩ V) :=
      ⟨w, mem_intersection_of_mem_binaryOpenCoverPieces_of_ne
        (by simpa using hb 1) (by simpa using hc 1) hne⟩
    let zd : binaryOpenCoverPiece U V d := ⟨z, by simpa using hd 0⟩
    let wd : binaryOpenCoverPiece U V d := ⟨w, by simpa using hd 1⟩
    let hz : zd = f zUV := by
      apply Subtype.ext
      change z = ((binaryOpenCoverIntersectionToPiece U V d zUV :
        binaryOpenCoverPiece U V d) : X)
      rw [coe_binaryOpenCoverIntersectionToPiece]
    let hw : wd = f wUV := by
      apply Subtype.ext
      change w = ((binaryOpenCoverIntersectionToPiece U V d wUV :
        binaryOpenCoverPiece U V d) : X)
      rw [coe_binaryOpenCoverIntersectionToPiece]
    (qUV.map f.continuous).cast hz hw = binaryOpenCoverPathInPiece q hd := by
  dsimp only
  apply Path.ext
  funext t
  rw [Path.cast_coe]
  apply Subtype.ext
  simp

/-- 双标签道路用交集 connector 归一化后在指定覆盖成员中的基本群元素。-/
def binaryOpenCoverDualPathPieceElement
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hUV : IsPathConnected (U ∩ V)) {z w : X} {b c : Bool}
    (q : Path z w) (hb : ∀ t, q t ∈ binaryOpenCoverPiece U V b)
    (hc : ∀ t, q t ∈ binaryOpenCoverPiece U V c) (hne : b ≠ c)
    (d : Bool) :
    FundamentalGroup (binaryOpenCoverPiece U V d)
      (binaryOpenCoverBasepoint hxU hxV d) :=
  binaryOpenCoverIntersectionMaps U V hxU hxV d
    (FundamentalGroup.fromPath ⟦Path.correctedLoop
      (binaryOpenCoverIntersectionConnector hxU hxV hUV _)
      (binaryOpenCoverDualPathInIntersection q hb hc hne)
      (binaryOpenCoverIntersectionConnector hxU hxV hUV _)⟧)

/-- 上述显式归一化元素就是交集基本群元素经相应包含映射的像。-/
private theorem binaryOpenCoverDualPathPieceElement_eq_map
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hUV : IsPathConnected (U ∩ V)) {z w : X} {b c : Bool}
    (q : Path z w) (hb : ∀ t, q t ∈ binaryOpenCoverPiece U V b)
    (hc : ∀ t, q t ∈ binaryOpenCoverPiece U V c) (hne : b ≠ c)
    (d : Bool) :
    binaryOpenCoverDualPathPieceElement hxU hxV hUV q hb hc hne d =
      binaryOpenCoverIntersectionMaps U V hxU hxV d
        (FundamentalGroup.fromPath ⟦Path.correctedLoop
          (binaryOpenCoverIntersectionConnector hxU hxV hUV _)
          (binaryOpenCoverDualPathInIntersection q hb hc hne)
          (binaryOpenCoverIntersectionConnector hxU hxV hUV _)⟧) := by
  rfl

/-- 交集归一化成员像的显式 corrected-loop 形式；这正是下一步与任意局部 connector 比较的左侧。-/
private theorem binaryOpenCoverDualPathPieceElement_eq_correctedLoop
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hUV : IsPathConnected (U ∩ V)) {z w : X} {b c : Bool}
    (q : Path z w) (hb : ∀ t, q t ∈ binaryOpenCoverPiece U V b)
    (hc : ∀ t, q t ∈ binaryOpenCoverPiece U V c) (hne : b ≠ c)
    (d : Bool) :
    let qUV := binaryOpenCoverDualPathInIntersection q hb hc hne
    let f := binaryOpenCoverIntersectionToPiece U V d
    let hbase := binaryOpenCoverBasepoint_eq_intersectionToPiece hxU hxV d
    binaryOpenCoverDualPathPieceElement hxU hxV hUV q hb hc hne d =
      FundamentalGroup.fromPath ⟦Path.correctedLoop
        ((binaryOpenCoverIntersectionConnector hxU hxV hUV _).map f.continuous |>.cast hbase rfl)
        (qUV.map f.continuous)
        ((binaryOpenCoverIntersectionConnector hxU hxV hUV _).map f.continuous |>.cast
          hbase rfl)⟧ := by
  cases d <;>
    exact fundamentalGroup_map_correctedLoop _ _ _ _

/-- `PushoutI` 的 defining relation 可按任意两个不同 Bool 标签定向使用。-/
private theorem binaryVanKampenPushout_of_intersection_eq_of_ne
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (g : FundamentalGroup (↥(U ∩ V))
      (binaryOpenCoverIntersectionBasepoint hxU hxV))
    {b c : Bool} (hne : b ≠ c) :
    (Monoid.PushoutI.of b (binaryOpenCoverIntersectionMaps U V hxU hxV b g) :
      binaryVanKampenPushout U V hxU hxV) =
      Monoid.PushoutI.of c (binaryOpenCoverIntersectionMaps U V hxU hxV c g) := by
  cases b <;> cases c
  · exact False.elim (hne rfl)
  · exact binaryVanKampenPushout_of_intersection_eq hxU hxV g
  · exact (binaryVanKampenPushout_of_intersection_eq hxU hxV g).symm
  · exact False.elim (hne rfl)

/-- 同一双标签道路的两个交集归一化成员像，经各自 Pushout 注入后严格相等。
@isnad1 id=eq.6h9v.s12.41f454f44438 from=translated src=- shape=a8ba3a01 vocab=c2b93b75
-/
theorem binaryOpenCoverDualPathPieceElements_pushout_eq
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hUV : IsPathConnected (U ∩ V)) {z w : X} {b c : Bool}
    (q : Path z w) (hb : ∀ t, q t ∈ binaryOpenCoverPiece U V b)
    (hc : ∀ t, q t ∈ binaryOpenCoverPiece U V c) (hne : b ≠ c) :
    (Monoid.PushoutI.of b
        (binaryOpenCoverDualPathPieceElement hxU hxV hUV q hb hc hne b) :
      binaryVanKampenPushout U V hxU hxV) =
      Monoid.PushoutI.of c
        (binaryOpenCoverDualPathPieceElement hxU hxV hUV q hb hc hne c) := by
  let g : FundamentalGroup (↥(U ∩ V))
      (binaryOpenCoverIntersectionBasepoint hxU hxV) :=
    FundamentalGroup.fromPath ⟦Path.correctedLoop
      (binaryOpenCoverIntersectionConnector hxU hxV hUV _)
      (binaryOpenCoverDualPathInIntersection q hb hc hne)
      (binaryOpenCoverIntersectionConnector hxU hxV hUV _)⟧
  rw [binaryOpenCoverDualPathPieceElement_eq_map,
    binaryOpenCoverDualPathPieceElement_eq_map]
  exact binaryVanKampenPushout_of_intersection_eq_of_ne hxU hxV g hne

/-- 在标签 `d` 成员中，把交集 connector 版本与任意局部 connector 版本放进同一个比较对象。-/
noncomputable def binaryOpenCoverDualPathConnectorComparison
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hUV : IsPathConnected (U ∩ V)) {z w : X} {b c d : Bool}
    (q : Path z w) (hb : ∀ t, q t ∈ binaryOpenCoverPiece U V b)
    (hc : ∀ t, q t ∈ binaryOpenCoverPiece U V c) (hne : b ≠ c)
    (hd : ∀ t, q t ∈ binaryOpenCoverPiece U V d)
    (localStart : Path (binaryOpenCoverBasepoint hxU hxV d)
      (⟨z, by simpa using hd 0⟩ : binaryOpenCoverPiece U V d))
    (localEnd : Path (binaryOpenCoverBasepoint hxU hxV d)
      (⟨w, by simpa using hd 1⟩ : binaryOpenCoverPiece U V d)) :
    CommonEdgeConnectorComparison (binaryOpenCoverPiece U V d)
      (binaryOpenCoverBasepoint hxU hxV d) := by
  let qUV := binaryOpenCoverDualPathInIntersection q hb hc hne
  let f := binaryOpenCoverIntersectionToPiece U V d
  let zUV : ↥(U ∩ V) :=
    ⟨z, mem_intersection_of_mem_binaryOpenCoverPieces_of_ne
      (by simpa using hb 0) (by simpa using hc 0) hne⟩
  let wUV : ↥(U ∩ V) :=
    ⟨w, mem_intersection_of_mem_binaryOpenCoverPieces_of_ne
      (by simpa using hb 1) (by simpa using hc 1) hne⟩
  let zd : binaryOpenCoverPiece U V d := ⟨z, by simpa using hd 0⟩
  let wd : binaryOpenCoverPiece U V d := ⟨w, by simpa using hd 1⟩
  let hbase := binaryOpenCoverBasepoint_eq_intersectionToPiece hxU hxV d
  let hz : zd = f zUV := by
    apply Subtype.ext
    change z = ((binaryOpenCoverIntersectionToPiece U V d zUV :
      binaryOpenCoverPiece U V d) : X)
    rw [coe_binaryOpenCoverIntersectionToPiece]
  let hw : wd = f wUV := by
    apply Subtype.ext
    change w = ((binaryOpenCoverIntersectionToPiece U V d wUV :
      binaryOpenCoverPiece U V d) : X)
    rw [coe_binaryOpenCoverIntersectionToPiece]
  exact
    { edgeSource := zd
      edgeTarget := wd
      edge := binaryOpenCoverPathInPiece q hd
      leftStart := ((binaryOpenCoverIntersectionConnector hxU hxV hUV zUV).map
        f.continuous).cast hbase hz
      leftEnd := ((binaryOpenCoverIntersectionConnector hxU hxV hUV wUV).map
        f.continuous).cast hbase hw
      rightStart := localStart
      rightEnd := localEnd }

/-- 同时 transport 修正环路的公共基点、两个边端点及三条道路，不改变底层基环路。-/
private theorem correctedLoop_cast_all_proof_irrel
    {x₀ z w x₀' z' w' : X}
    (left : Path x₀ z) (segment : Path z w) (right : Path x₀ w)
    (hxLeft hxRight : x₀' = x₀)
    (hzLeft hzSegment : z' = z) (hwSegment hwRight : w' = w) :
    Path.correctedLoop (left.cast hxLeft hzLeft)
        (segment.cast hzSegment hwSegment) (right.cast hxRight hwRight) =
      (Path.correctedLoop left segment right).cast hxLeft hxRight := by
  cases hxLeft
  cases hzLeft
  cases hwSegment
  simp only [Path.cast_rfl_rfl]

/-- 上述比较对象的交集 connector 一侧就是规范的双标签成员像。-/
private theorem binaryOpenCoverDualPathConnectorComparison_leftElement
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hUV : IsPathConnected (U ∩ V)) {z w : X} {b c d : Bool}
    (q : Path z w) (hb : ∀ t, q t ∈ binaryOpenCoverPiece U V b)
    (hc : ∀ t, q t ∈ binaryOpenCoverPiece U V c) (hne : b ≠ c)
    (hd : ∀ t, q t ∈ binaryOpenCoverPiece U V d)
    (localStart : Path (binaryOpenCoverBasepoint hxU hxV d)
      (⟨z, by simpa using hd 0⟩ : binaryOpenCoverPiece U V d))
    (localEnd : Path (binaryOpenCoverBasepoint hxU hxV d)
      (⟨w, by simpa using hd 1⟩ : binaryOpenCoverPiece U V d)) :
    (binaryOpenCoverDualPathConnectorComparison hxU hxV hUV q hb hc hne hd
      localStart localEnd).leftElement =
      binaryOpenCoverDualPathPieceElement hxU hxV hUV q hb hc hne d := by
  rw [binaryOpenCoverDualPathPieceElement_eq_correctedLoop]
  unfold CommonEdgeConnectorComparison.leftElement
    binaryOpenCoverDualPathConnectorComparison
  dsimp only [CommonEdgeConnectorComparison.leftStart,
    CommonEdgeConnectorComparison.edge, CommonEdgeConnectorComparison.leftEnd]
  let qUV := binaryOpenCoverDualPathInIntersection q hb hc hne
  let f := binaryOpenCoverIntersectionToPiece U V d
  let zUV : ↥(U ∩ V) :=
    ⟨z, mem_intersection_of_mem_binaryOpenCoverPieces_of_ne
      (by simpa using hb 0) (by simpa using hc 0) hne⟩
  let wUV : ↥(U ∩ V) :=
    ⟨w, mem_intersection_of_mem_binaryOpenCoverPieces_of_ne
      (by simpa using hb 1) (by simpa using hc 1) hne⟩
  let zd : binaryOpenCoverPiece U V d := ⟨z, by simpa using hd 0⟩
  let wd : binaryOpenCoverPiece U V d := ⟨w, by simpa using hd 1⟩
  let hbase := binaryOpenCoverBasepoint_eq_intersectionToPiece hxU hxV d
  let hz : zd = f zUV := by
    apply Subtype.ext
    change z = ((binaryOpenCoverIntersectionToPiece U V d zUV :
      binaryOpenCoverPiece U V d) : X)
    rw [coe_binaryOpenCoverIntersectionToPiece]
  let hw : wd = f wUV := by
    apply Subtype.ext
    change w = ((binaryOpenCoverIntersectionToPiece U V d wUV :
      binaryOpenCoverPiece U V d) : X)
    rw [coe_binaryOpenCoverIntersectionToPiece]
  have hedge := binaryOpenCoverDualPath_map_toPiece_cast_eq q hb hc hne hd
  dsimp only at hedge
  rw [← hedge]
  exact congrArg Path.Homotopic.Quotient.mk
    (correctedLoop_cast_all_proof_irrel
      ((binaryOpenCoverIntersectionConnector hxU hxV hUV zUV).map f.continuous)
      (qUV.map f.continuous)
      ((binaryOpenCoverIntersectionConnector hxU hxV hUV wUV).map f.continuous)
      hbase hbase hz hz hw hw)

/-- 任意局部 connector 版本由交集规范元素及两个端点变化因子精确给出。
@isnad1 id=other.7h12v.s10.c53d3143d930 from=translated src=- shape=e8f0d5b1 vocab=edc41148
-/
theorem binaryOpenCoverDualPathConnectorComparison_relation
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hUV : IsPathConnected (U ∩ V)) {z w : X} {b c d : Bool}
    (q : Path z w) (hb : ∀ t, q t ∈ binaryOpenCoverPiece U V b)
    (hc : ∀ t, q t ∈ binaryOpenCoverPiece U V c) (hne : b ≠ c)
    (hd : ∀ t, q t ∈ binaryOpenCoverPiece U V d)
    (localStart : Path (binaryOpenCoverBasepoint hxU hxV d)
      (⟨z, by simpa using hd 0⟩ : binaryOpenCoverPiece U V d))
    (localEnd : Path (binaryOpenCoverBasepoint hxU hxV d)
      (⟨w, by simpa using hd 1⟩ : binaryOpenCoverPiece U V d)) :
    let C := binaryOpenCoverDualPathConnectorComparison hxU hxV hUV
      q hb hc hne hd localStart localEnd
    C.endChange⁻¹ *
        binaryOpenCoverDualPathPieceElement hxU hxV hUV q hb hc hne d *
        C.startChange = C.rightElement := by
  dsimp only
  rw [← binaryOpenCoverDualPathConnectorComparison_leftElement
    hxU hxV hUV q hb hc hne hd localStart localEnd]
  exact (binaryOpenCoverDualPathConnectorComparison hxU hxV hUV
    q hb hc hne hd localStart localEnd).rightElement_eq

/-- 方格角 potential 是坐标无关 vertex potential 在实际单格标签与规范角 connector 上的特例。
@isnad1 id=eq.6h11v.s8.4c94f300995f from=translated src=- shape=07278417 vocab=8d421e5b
-/
theorem BinaryOpenCoverSquareSubdivision.gridCellVertexPotentialFromIntersection_eq_vertexPotential
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (z : ↥(U ∩ V)) (i j : Fin D.steps) (a b : Fin 2)
    (hz : binaryOpenCoverIntersectionToPiece U V (D.label i j) z =
      D.gridCellVertexInPiece i j a b) :
    D.gridCellVertexPotentialFromIntersection hxU hxV hUV hU hV
        z i j a b hz =
      binaryOpenCoverVertexPotentialFromIntersection hxU hxV hUV z
        (D.label i j) (D.gridCellVertexInPiece i j a b)
        (D.gridCellVertexConnectorInPiece hxU hxV hU hV i j a b) hz := by
  rfl

/-- vertex potential 不依赖把同一个交集像识别为局部端点时所用的等式证明。
@isnad1 id=eq.5h8v.s8.390d725766ba from=translated src=- shape=dc117a26 vocab=bcf7863c
-/
theorem binaryOpenCoverVertexPotentialFromIntersection_proof_irrel
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hUV : IsPathConnected (U ∩ V)) (z : ↥(U ∩ V)) (d : Bool)
    (w : binaryOpenCoverPiece U V d)
    (localConnector : Path (binaryOpenCoverBasepoint hxU hxV d) w)
    (hz₁ hz₂ : binaryOpenCoverIntersectionToPiece U V d z = w) :
    binaryOpenCoverVertexPotentialFromIntersection hxU hxV hUV z d w localConnector hz₁ =
      binaryOpenCoverVertexPotentialFromIntersection hxU hxV hUV z d w localConnector hz₂ := by
  rw [Subsingleton.elim hz₁ hz₂]

/-- 把交集点、成员端点和局部 connector 同时沿相等搬运，不改变 vertex potential。
@isnad1 id=eq.8h11v.s9.5e83addc6df4 from=translated src=- shape=3ddcb74e vocab=e4c24e88
-/
theorem binaryOpenCoverVertexPotentialFromIntersection_cast
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hUV : IsPathConnected (U ∩ V)) (d : Bool)
    (z₁ z₂ : ↥(U ∩ V)) (hz : z₁ = z₂)
    (w₁ w₂ : binaryOpenCoverPiece U V d) (hw : w₁ = w₂)
    (local₁ : Path (binaryOpenCoverBasepoint hxU hxV d) w₁)
    (local₂ : Path (binaryOpenCoverBasepoint hxU hxV d) w₂)
    (hlocal : local₁.cast rfl hw.symm = local₂)
    (h₁ : binaryOpenCoverIntersectionToPiece U V d z₁ = w₁)
    (h₂ : binaryOpenCoverIntersectionToPiece U V d z₂ = w₂) :
    binaryOpenCoverVertexPotentialFromIntersection
        hxU hxV hUV z₁ d w₁ local₁ h₁ =
      binaryOpenCoverVertexPotentialFromIntersection
        hxU hxV hUV z₂ d w₂ local₂ h₂ := by
  subst z₂
  subst w₂
  simp only [Path.cast_rfl_rfl] at hlocal
  subst local₂
  exact binaryOpenCoverVertexPotentialFromIntersection_proof_irrel
    hxU hxV hUV z₁ d w₁ local₁ h₁ h₂

/-- `cast` 的标签变化版本：两个标签已知相等时，只需比较交集点、成员端点和 connector 的底层
函数，即可跨越整个 dependent transport 比较 vertex potentials。
@isnad1 id=eq.9h12v.s9.4bb4d8183a06 from=translated src=- shape=3665bcf8 vocab=98414eb2
-/
theorem binaryOpenCoverVertexPotentialFromIntersection_cast_label
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hUV : IsPathConnected (U ∩ V))
    (d₁ d₂ : Bool) (hd : d₁ = d₂)
    (z₁ z₂ : ↥(U ∩ V)) (hz : z₁ = z₂)
    (w₁ : binaryOpenCoverPiece U V d₁)
    (w₂ : binaryOpenCoverPiece U V d₂) (hw : (w₁ : X) = (w₂ : X))
    (local₁ : Path (binaryOpenCoverBasepoint hxU hxV d₁) w₁)
    (local₂ : Path (binaryOpenCoverBasepoint hxU hxV d₂) w₂)
    (hlocal : ∀ u, (local₁ u : X) = (local₂ u : X))
    (h₁ : binaryOpenCoverIntersectionToPiece U V d₁ z₁ = w₁)
    (h₂ : binaryOpenCoverIntersectionToPiece U V d₂ z₂ = w₂) :
    binaryOpenCoverVertexPotentialFromIntersection
        hxU hxV hUV z₁ d₁ w₁ local₁ h₁ =
      binaryOpenCoverVertexPotentialFromIntersection
        hxU hxV hUV z₂ d₂ w₂ local₂ h₂ := by
  subst d₂
  have hw' : w₁ = w₂ := by
    apply Subtype.ext
    exact hw
  apply binaryOpenCoverVertexPotentialFromIntersection_cast
    hxU hxV hUV d₁ z₁ z₂ hz w₁ w₂ hw' local₁ local₂
  · apply Path.ext
    funext u
    apply Subtype.ext
    rw [Path.cast_coe]
    exact hlocal u

/-- Mapping an intersection connector change into either cover member, with the
basepoint transport used by the binary-cover API made explicit.-/
private theorem binaryOpenCoverIntersectionMaps_connectorChange
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (d : Bool) {z : ↥(U ∩ V)}
    (p q : Path (binaryOpenCoverIntersectionBasepoint hxU hxV) z) :
    binaryOpenCoverIntersectionMaps U V hxU hxV d (connectorChange p q) =
      connectorChange
        ((p.map (binaryOpenCoverIntersectionToPiece U V d).continuous).cast
          (binaryOpenCoverBasepoint_eq_intersectionToPiece hxU hxV d) rfl)
        ((q.map (binaryOpenCoverIntersectionToPiece U V d).continuous).cast
          (binaryOpenCoverBasepoint_eq_intersectionToPiece hxU hxV d) rfl) := by
  cases d <;>
    exact fundamentalGroup_map_connectorChange
      (binaryOpenCoverIntersectionToPiece U V _) p q

/-- If two local connectors at the same intersection point are the images of one
intersection connector, their vertex potentials agree in the pushout, even when
the two cover labels differ.-/
private theorem binaryOpenCoverVertexPotentialFromIntersection_eq_of_intersectionConnector
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hUV : IsPathConnected (U ∩ V)) (z : ↥(U ∩ V))
    (q : Path (binaryOpenCoverIntersectionBasepoint hxU hxV) z)
    (d₁ d₂ : Bool)
    (w₁ : binaryOpenCoverPiece U V d₁)
    (w₂ : binaryOpenCoverPiece U V d₂)
    (local₁ : Path (binaryOpenCoverBasepoint hxU hxV d₁) w₁)
    (local₂ : Path (binaryOpenCoverBasepoint hxU hxV d₂) w₂)
    (hlocal₁ : ∀ u, (local₁ u : X) = q u)
    (hlocal₂ : ∀ u, (local₂ u : X) = q u)
    (h₁ : binaryOpenCoverIntersectionToPiece U V d₁ z = w₁)
    (h₂ : binaryOpenCoverIntersectionToPiece U V d₂ z = w₂) :
    binaryOpenCoverVertexPotentialFromIntersection
        hxU hxV hUV z d₁ w₁ local₁ h₁ =
      binaryOpenCoverVertexPotentialFromIntersection
        hxU hxV hUV z d₂ w₂ local₂ h₂ := by
  let p := binaryOpenCoverIntersectionConnector hxU hxV hUV z
  let g : FundamentalGroup (↥(U ∩ V))
      (binaryOpenCoverIntersectionBasepoint hxU hxV) := connectorChange p q
  have hpotential (d : Bool) (w : binaryOpenCoverPiece U V d)
      (pLocal : Path (binaryOpenCoverBasepoint hxU hxV d) w)
      (hlocal : ∀ u, (pLocal u : X) = q u)
      (h : binaryOpenCoverIntersectionToPiece U V d z = w) :
      binaryOpenCoverVertexPotentialFromIntersection
          hxU hxV hUV z d w pLocal h =
        Monoid.PushoutI.of d
          (binaryOpenCoverIntersectionMaps U V hxU hxV d g) := by
    unfold binaryOpenCoverVertexPotentialFromIntersection
    dsimp only [g]
    rw [binaryOpenCoverIntersectionMaps_connectorChange hxU hxV d p q]
    let mappedP :=
      ((p.map (binaryOpenCoverIntersectionToPiece U V d).continuous).cast
        (binaryOpenCoverBasepoint_eq_intersectionToPiece hxU hxV d) rfl)
    let mappedQ :=
      ((q.map (binaryOpenCoverIntersectionToPiece U V d).continuous).cast
        (binaryOpenCoverBasepoint_eq_intersectionToPiece hxU hxV d) rfl)
    rw [← connectorChange_cast mappedP mappedQ h.symm]
    apply congrArg (Monoid.PushoutI.of d)
    apply congrArg₂ connectorChange
    · apply Path.ext
      funext u
      apply Subtype.ext
      dsimp only [mappedP]
      rw [Path.cast_coe, Path.cast_coe]
      cases d <;>
        exact coe_binaryOpenCoverIntersectionConnectorInPiece
          hxU hxV hUV _ z u
    · apply Path.ext
      funext u
      apply Subtype.ext
      dsimp only [mappedQ]
      rw [Path.cast_coe, Path.cast_coe]
      cases d <;> exact hlocal u
  rw [hpotential d₁ w₁ local₁ hlocal₁ h₁,
    hpotential d₂ w₂ local₂ hlocal₂ h₂]
  by_cases hd : d₁ = d₂
  · subst d₂
    rfl
  · exact binaryVanKampenPushout_of_intersection_eq_of_ne hxU hxV g hd

/-- At the distinguished intersection basepoint, any two member connectors that
are constant after coercion to the ambient space define the same pushout
potential, independently of their cover labels.
@isnad1 id=eq.7h10v.s9.1c20d412b0bc from=translated src=- shape=34318ce3 vocab=8cf977fd
-/
theorem binaryOpenCoverVertexPotentialFromIntersection_basepoint_eq_of_coe
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hUV : IsPathConnected (U ∩ V)) (d₁ d₂ : Bool)
    (w₁ : binaryOpenCoverPiece U V d₁)
    (w₂ : binaryOpenCoverPiece U V d₂)
    (local₁ : Path (binaryOpenCoverBasepoint hxU hxV d₁) w₁)
    (local₂ : Path (binaryOpenCoverBasepoint hxU hxV d₂) w₂)
    (hlocal₁ : ∀ u, (local₁ u : X) = x₀)
    (hlocal₂ : ∀ u, (local₂ u : X) = x₀)
    (h₁ : binaryOpenCoverIntersectionToPiece U V d₁
      (binaryOpenCoverIntersectionBasepoint hxU hxV) = w₁)
    (h₂ : binaryOpenCoverIntersectionToPiece U V d₂
      (binaryOpenCoverIntersectionBasepoint hxU hxV) = w₂) :
    binaryOpenCoverVertexPotentialFromIntersection hxU hxV hUV
        (binaryOpenCoverIntersectionBasepoint hxU hxV)
        d₁ w₁ local₁ h₁ =
      binaryOpenCoverVertexPotentialFromIntersection hxU hxV hUV
        (binaryOpenCoverIntersectionBasepoint hxU hxV)
        d₂ w₂ local₂ h₂ := by
  apply binaryOpenCoverVertexPotentialFromIntersection_eq_of_intersectionConnector
    hxU hxV hUV (binaryOpenCoverIntersectionBasepoint hxU hxV)
      (Path.refl (binaryOpenCoverIntersectionBasepoint hxU hxV))
      d₁ d₂ w₁ w₂ local₁ local₂
  · intro u
    exact (hlocal₁ u).trans rfl
  · intro u
    exact (hlocal₂ u).trans rfl

/-- A point of either cover member whose ambient value is the distinguished
basepoint is the image of the intersection basepoint.
@isnad1 id=eq.3h6v.s7.51925fccd3b8 from=translated src=- shape=d2c58185 vocab=ae0bafe0
-/
theorem binaryOpenCoverIntersectionToPiece_basepoint_eq_of_coe
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (d : Bool) (w : binaryOpenCoverPiece U V d) (hw : (w : X) = x₀) :
    binaryOpenCoverIntersectionToPiece U V d
        (binaryOpenCoverIntersectionBasepoint hxU hxV) = w := by
  apply Subtype.ext
  simpa only [coe_binaryOpenCoverIntersectionToPiece] using hw.symm

/-- 共同成员 connector potential 的跨标签 transport：标签相等时，比较底层端点及两条 connector
函数即可。
@isnad1 id=eq.6h12v.s9.ce2bc8272ba0 from=translated src=- shape=acd12d49 vocab=f320b00b
-/
theorem binaryOpenCoverConnectorPotential_cast_label
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (d₁ d₂ : Bool) (hd : d₁ = d₂)
    (w₁ : binaryOpenCoverPiece U V d₁)
    (w₂ : binaryOpenCoverPiece U V d₂) (hw : (w₁ : X) = (w₂ : X))
    (reference₁ local₁ : Path (binaryOpenCoverBasepoint hxU hxV d₁) w₁)
    (reference₂ local₂ : Path (binaryOpenCoverBasepoint hxU hxV d₂) w₂)
    (href : ∀ u, (reference₁ u : X) = (reference₂ u : X))
    (hlocal : ∀ u, (local₁ u : X) = (local₂ u : X)) :
    binaryOpenCoverConnectorPotential hxU hxV d₁ w₁ reference₁ local₁ =
      binaryOpenCoverConnectorPotential hxU hxV d₂ w₂ reference₂ local₂ := by
  subst d₂
  have hw' : w₁ = w₂ := by
    apply Subtype.ext
    exact hw
  have href' : reference₁.cast rfl hw'.symm = reference₂ := by
    apply Path.ext
    funext u
    apply Subtype.ext
    rw [Path.cast_coe]
    exact href u
  have hlocal' : local₁.cast rfl hw'.symm = local₂ := by
    apply Path.ext
    funext u
    apply Subtype.ext
    rw [Path.cast_coe]
    exact hlocal u
  unfold binaryOpenCoverConnectorPotential
  apply congrArg (Monoid.PushoutI.of d₁)
  calc
    connectorChange reference₁ local₁ =
        connectorChange (reference₁.cast rfl hw'.symm)
          (local₁.cast rfl hw'.symm) :=
      (connectorChange_cast reference₁ local₁ hw'.symm).symm
    _ = connectorChange reference₂ local₂ := by rw [href', hlocal']

/-- 任意共同成员 comparison 的起点逆变化，在该点已知属于交集时，等于两套局部 connectors 的
统一 vertex potentials 之比。
@isnad1 id=eq.4h7v.s12.9bb0ea839467 from=translated src=- shape=1a0a46de vocab=d466f9ef
-/
theorem CommonEdgeConnectorComparison.pushout_startChange_inv_eq_vertexPotentials
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hUV : IsPathConnected (U ∩ V)) (d : Bool)
    (C : CommonEdgeConnectorComparison (binaryOpenCoverPiece U V d)
      (binaryOpenCoverBasepoint hxU hxV d))
    (z : ↥(U ∩ V))
    (hz : binaryOpenCoverIntersectionToPiece U V d z = C.edgeSource) :
    ((Monoid.PushoutI.of d C.startChange :
        binaryVanKampenPushout U V hxU hxV)⁻¹) =
      transitionFromPotentials
        (binaryOpenCoverVertexPotentialFromIntersection
          hxU hxV hUV z d C.edgeSource C.leftStart hz)
        (binaryOpenCoverVertexPotentialFromIntersection
          hxU hxV hUV z d C.edgeSource C.rightStart hz) := by
  let f := Monoid.PushoutI.of
    (φ := binaryOpenCoverIntersectionMaps U V hxU hxV) d
  let reference :=
    (binaryOpenCoverIntersectionConnectorInPiece hxU hxV hUV d z).cast
      (binaryOpenCoverBasepoint_eq_intersectionToPiece hxU hxV d) hz.symm
  change (f C.startChange)⁻¹ = _
  rw [C.map_startChange_inv_eq_potentials f reference]
  rfl

/-- 上一结论的终点版本。
@isnad1 id=eq.4h7v.s12.cdffc84ac1ee from=translated src=- shape=1a0a46de vocab=0f5e7d36
-/
theorem CommonEdgeConnectorComparison.pushout_endChange_inv_eq_vertexPotentials
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hUV : IsPathConnected (U ∩ V)) (d : Bool)
    (C : CommonEdgeConnectorComparison (binaryOpenCoverPiece U V d)
      (binaryOpenCoverBasepoint hxU hxV d))
    (z : ↥(U ∩ V))
    (hz : binaryOpenCoverIntersectionToPiece U V d z = C.edgeTarget) :
    ((Monoid.PushoutI.of d C.endChange :
        binaryVanKampenPushout U V hxU hxV)⁻¹) =
      transitionFromPotentials
        (binaryOpenCoverVertexPotentialFromIntersection
          hxU hxV hUV z d C.edgeTarget C.leftEnd hz)
        (binaryOpenCoverVertexPotentialFromIntersection
          hxU hxV hUV z d C.edgeTarget C.rightEnd hz) := by
  let f := Monoid.PushoutI.of
    (φ := binaryOpenCoverIntersectionMaps U V hxU hxV) d
  let reference :=
    (binaryOpenCoverIntersectionConnectorInPiece hxU hxV hUV d z).cast
      (binaryOpenCoverBasepoint_eq_intersectionToPiece hxU hxV d) hz.symm
  change (f C.endChange)⁻¹ = _
  rw [C.map_endChange_inv_eq_potentials f reference]
  rfl

/-- 双标签道路在起点的 comparison potential，正是坐标无关的交集 vertex potential。
@isnad1 id=other.7h12v.s12.8dda6b23fe91 from=translated src=- shape=c8f8ce7e vocab=b313d9f5
-/
theorem binaryOpenCoverDualPathConnectorComparison_startPotential_eq
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hUV : IsPathConnected (U ∩ V)) {z w : X} {b c d : Bool}
    (q : Path z w) (hb : ∀ t, q t ∈ binaryOpenCoverPiece U V b)
    (hc : ∀ t, q t ∈ binaryOpenCoverPiece U V c) (hne : b ≠ c)
    (hd : ∀ t, q t ∈ binaryOpenCoverPiece U V d)
    (localStart : Path (binaryOpenCoverBasepoint hxU hxV d)
      (⟨z, by simpa using hd 0⟩ : binaryOpenCoverPiece U V d))
    (localEnd : Path (binaryOpenCoverBasepoint hxU hxV d)
      (⟨w, by simpa using hd 1⟩ : binaryOpenCoverPiece U V d)) :
    let C := binaryOpenCoverDualPathConnectorComparison hxU hxV hUV
      q hb hc hne hd localStart localEnd
    let zUV : ↥(U ∩ V) :=
      ⟨z, mem_intersection_of_mem_binaryOpenCoverPieces_of_ne
        (by simpa using hb 0) (by simpa using hc 0) hne⟩
    let zd : binaryOpenCoverPiece U V d := ⟨z, by simpa using hd 0⟩
    let hz : binaryOpenCoverIntersectionToPiece U V d zUV = zd := by
      apply Subtype.ext
      rw [coe_binaryOpenCoverIntersectionToPiece]
    ((Monoid.PushoutI.of d C.startChange :
        binaryVanKampenPushout U V hxU hxV)⁻¹) =
      binaryOpenCoverVertexPotentialFromIntersection
        hxU hxV hUV zUV d zd localStart hz := by
  dsimp only
  let C := binaryOpenCoverDualPathConnectorComparison hxU hxV hUV
    q hb hc hne hd localStart localEnd
  rw [C.map_startChange_inv]
  rfl

/-- 双标签道路在终点的 comparison potential，同样是该终点的交集 vertex potential。
@isnad1 id=other.7h12v.s12.b12796637bcd from=translated src=- shape=1bd43671 vocab=8f4c886b
-/
theorem binaryOpenCoverDualPathConnectorComparison_endPotential_eq
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hUV : IsPathConnected (U ∩ V)) {z w : X} {b c d : Bool}
    (q : Path z w) (hb : ∀ t, q t ∈ binaryOpenCoverPiece U V b)
    (hc : ∀ t, q t ∈ binaryOpenCoverPiece U V c) (hne : b ≠ c)
    (hd : ∀ t, q t ∈ binaryOpenCoverPiece U V d)
    (localStart : Path (binaryOpenCoverBasepoint hxU hxV d)
      (⟨z, by simpa using hd 0⟩ : binaryOpenCoverPiece U V d))
    (localEnd : Path (binaryOpenCoverBasepoint hxU hxV d)
      (⟨w, by simpa using hd 1⟩ : binaryOpenCoverPiece U V d)) :
    let C := binaryOpenCoverDualPathConnectorComparison hxU hxV hUV
      q hb hc hne hd localStart localEnd
    let wUV : ↥(U ∩ V) :=
      ⟨w, mem_intersection_of_mem_binaryOpenCoverPieces_of_ne
        (by simpa using hb 1) (by simpa using hc 1) hne⟩
    let wd : binaryOpenCoverPiece U V d := ⟨w, by simpa using hd 1⟩
    let hw : binaryOpenCoverIntersectionToPiece U V d wUV = wd := by
      apply Subtype.ext
      rw [coe_binaryOpenCoverIntersectionToPiece]
    ((Monoid.PushoutI.of d C.endChange :
        binaryVanKampenPushout U V hxU hxV)⁻¹) =
      binaryOpenCoverVertexPotentialFromIntersection
        hxU hxV hUV wUV d wd localEnd hw := by
  dsimp only
  let C := binaryOpenCoverDualPathConnectorComparison hxU hxV hUV
    q hb hc hne hd localStart localEnd
  rw [C.map_endChange_inv]
  rfl

/-- 两个双标签道路 comparison 在同一共享环境顶点使用同一个局部 connector 时，前一条的终点
potential 与后一条的起点 potential 严格相同。所有成员性 proof transport 都由统一 vertex
potential 消去。
@isnad1 id=other.12h20v.s13.21da235b5b0d from=translated src=- shape=bdf5eebf vocab=b3fbd0ef
-/
theorem binaryOpenCoverDualPathConnectorComparison_sharedPotential
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hUV : IsPathConnected (U ∩ V)) {a v₁ v₂ w : X} (hv : v₁ = v₂)
    {b₁ c₁ b₂ c₂ d : Bool}
    (q₁ : Path a v₁)
    (hb₁ : ∀ t, q₁ t ∈ binaryOpenCoverPiece U V b₁)
    (hc₁ : ∀ t, q₁ t ∈ binaryOpenCoverPiece U V c₁) (hne₁ : b₁ ≠ c₁)
    (q₂ : Path v₂ w)
    (hb₂ : ∀ t, q₂ t ∈ binaryOpenCoverPiece U V b₂)
    (hc₂ : ∀ t, q₂ t ∈ binaryOpenCoverPiece U V c₂) (hne₂ : b₂ ≠ c₂)
    (hd₁ : ∀ t, q₁ t ∈ binaryOpenCoverPiece U V d)
    (hd₂ : ∀ t, q₂ t ∈ binaryOpenCoverPiece U V d)
    (localStart₁ : Path (binaryOpenCoverBasepoint hxU hxV d)
      (⟨a, by simpa using hd₁ 0⟩ : binaryOpenCoverPiece U V d))
    (localEnd₁ : Path (binaryOpenCoverBasepoint hxU hxV d)
      (⟨v₁, by simpa using hd₁ 1⟩ : binaryOpenCoverPiece U V d))
    (localStart₂ : Path (binaryOpenCoverBasepoint hxU hxV d)
      (⟨v₂, by simpa using hd₂ 0⟩ : binaryOpenCoverPiece U V d))
    (localEnd₂ : Path (binaryOpenCoverBasepoint hxU hxV d)
      (⟨w, by simpa using hd₂ 1⟩ : binaryOpenCoverPiece U V d))
    (hlocal :
      let w₁ : binaryOpenCoverPiece U V d := ⟨v₁, by simpa using hd₁ 1⟩
      let w₂ : binaryOpenCoverPiece U V d := ⟨v₂, by simpa using hd₂ 0⟩
      let hw : w₁ = w₂ := by apply Subtype.ext; exact hv
      localEnd₁.cast rfl hw.symm = localStart₂) :
    let C₁ := binaryOpenCoverDualPathConnectorComparison hxU hxV hUV
      q₁ hb₁ hc₁ hne₁ hd₁ localStart₁ localEnd₁
    let C₂ := binaryOpenCoverDualPathConnectorComparison hxU hxV hUV
      q₂ hb₂ hc₂ hne₂ hd₂ localStart₂ localEnd₂
    ((Monoid.PushoutI.of d C₁.endChange :
        binaryVanKampenPushout U V hxU hxV)⁻¹) =
      ((Monoid.PushoutI.of d C₂.startChange :
        binaryVanKampenPushout U V hxU hxV)⁻¹) := by
  dsimp only
  rw [binaryOpenCoverDualPathConnectorComparison_endPotential_eq
      hxU hxV hUV q₁ hb₁ hc₁ hne₁ hd₁ localStart₁ localEnd₁,
    binaryOpenCoverDualPathConnectorComparison_startPotential_eq
      hxU hxV hUV q₂ hb₂ hc₂ hne₂ hd₂ localStart₂ localEnd₂]
  apply binaryOpenCoverVertexPotentialFromIntersection_cast
    hxU hxV hUV d
  · apply Subtype.ext
    exact hv
  · exact hlocal
  · apply Subtype.ext
    exact hv

end SandronesLibrary.Topology
