/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.VanKampenEdgeGauge

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# van Kampen 网格顶点的 connector potential

本文件把同一顶点处两条基点 connector 的变化写成基本群 cocycle，并以
`transitionFromPotentials source target = target * source⁻¹` 表示边 transition。它证明全同标签四格
中央点的传播 coherence，并唯一建立交集参考与成员内参考两类 potential 构造，供后续混合标签层
复用。

当前条目：

* `topology.fundamental-group.van-kampen-vertex-potential`。

本文件不处理混合标签中央点，不执行整行或整网格 telescope，也不证明单射或 van Kampen 同构。
-/

open Set
open scoped unitInterval

noncomputable section

namespace SandronesLibrary.Topology

variable {X : Type*} [TopologicalSpace X]

/-- 同一端点的两条 connector 之间的基本群变化元素。

> **Entry**: topology.fundamental-group.van-kampen-vertex-potential-/
def connectorChange {x₀ z : X} (fromConnector toConnector : Path x₀ z) :
    FundamentalGroup X x₀ :=
  FundamentalGroup.fromPath
    ⟦Path.correctedLoop fromConnector (Path.refl z) toConnector⟧

/-- connector 变化满足严格 cocycle：经中间 connector 的两次变化等于直接变化。-/
theorem connectorChange_mul {x₀ z : X}
    (first middle last : Path x₀ z) :
    connectorChange middle last * connectorChange first middle =
      connectorChange first last := by
  unfold connectorChange
  rw [Path.correctedLoop_product first (Path.refl z) middle (Path.refl z) last]
  unfold Path.correctedLoop FundamentalGroup.fromPath FundamentalGroup.fromArrow
  simp

@[simp] theorem connectorChange_self {x₀ z : X} (q : Path x₀ z) :
    connectorChange q q = 1 := by
  rw [FundamentalGroup.one_def]
  unfold connectorChange Path.correctedLoop FundamentalGroup.fromPath
    FundamentalGroup.fromArrow
  simp

theorem connectorChange_reverse {x₀ z : X} (p q : Path x₀ z) :
    connectorChange q p = (connectorChange p q)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [connectorChange_mul]
  exact connectorChange_self p

/-- 连续映射把 connector 变化元素送到映射后 connector 的变化元素。-/
theorem fundamentalGroup_map_connectorChange
    {S T : Type*} [TopologicalSpace S] [TopologicalSpace T]
    (f : C(S, T)) {base z : S} (p q : Path base z) :
    FundamentalGroup.map f base (connectorChange p q) =
      connectorChange (p.map f.continuous) (q.map f.continuous) := by
  unfold connectorChange
  rw [fundamentalGroup_map_correctedLoop]
  congr 1

/-- 任意群同态保持 connector cocycle。-/
theorem map_connectorChange_mul
    {S G : Type*} [TopologicalSpace S] [Group G] {base z : S}
    (f : FundamentalGroup S base →* G)
    (first middle last : Path base z) :
    f (connectorChange middle last) * f (connectorChange first middle) =
      f (connectorChange first last) := by
  rw [← map_mul, connectorChange_mul]

theorem CommonEdgeConnectorComparison.startChange_eq_connectorChange
    {S : Type*} [TopologicalSpace S] {base : S}
    (C : CommonEdgeConnectorComparison S base) :
    C.startChange = connectorChange C.rightStart C.leftStart := rfl

theorem CommonEdgeConnectorComparison.endChange_eq_connectorChange
    {S : Type*} [TopologicalSpace S] {base : S}
    (C : CommonEdgeConnectorComparison S base) :
    C.endChange = connectorChange C.rightEnd C.leftEnd := rfl

/-- 四条 connector 构成的方块中，两条两步变化路径给出同一元素。-/
theorem connectorChange_square {x₀ z : X}
    (bottomLeft bottomRight topLeft topRight : Path x₀ z) :
    connectorChange topLeft topRight * connectorChange bottomLeft topLeft =
      connectorChange bottomRight topRight * connectorChange bottomLeft bottomRight := by
  rw [connectorChange_mul, connectorChange_mul]

/-- connector 方块路径无关在任意目标群中的像。-/
private theorem map_connectorChange_square
    {S G : Type*} [TopologicalSpace S] [Group G] {base z : S}
    (f : FundamentalGroup S base →* G)
    (bottomLeft bottomRight topLeft topRight : Path base z) :
    f (connectorChange topLeft topRight) * f (connectorChange bottomLeft topLeft) =
      f (connectorChange bottomRight topRight) *
        f (connectorChange bottomLeft bottomRight) := by
  rw [← map_mul, ← map_mul, connectorChange_square]

/-- 由同一参考 connector 的两个顶点 potential 得到从 source frame 到 target frame 的 transition。-/
def transitionFromPotentials {G : Type*} [Group G]
    (sourcePotential targetPotential : G) : G :=
  targetPotential * sourcePotential⁻¹

/-- 一条边本身就是两端 potentials 的变化比时，在这两个 frames 下规范化为单位元。-/
@[simp] theorem rebaseEdge_transitionFromPotentials
    {G : Type*} [Group G] (sourcePotential targetPotential : G) :
    rebaseEdge sourcePotential targetPotential
      (transitionFromPotentials sourcePotential targetPotential) = 1 := by
  simp [rebaseEdge, transitionFromPotentials]

/-- 相对同一参考 connector 的两个 potentials 之比，正是两条目标 connector
之间的变化元素。-/
theorem connectorChange_eq_transitionFromPotentials
    {x₀ z : X} (reference startConnector endConnector : Path x₀ z) :
    connectorChange startConnector endConnector =
      transitionFromPotentials
        (connectorChange reference startConnector)
        (connectorChange reference endConnector) := by
  unfold transitionFromPotentials
  calc
    connectorChange startConnector endConnector =
        connectorChange startConnector endConnector * 1 := by rw [mul_one]
    _ = connectorChange startConnector endConnector *
          (connectorChange reference startConnector *
            (connectorChange reference startConnector)⁻¹) := by
        rw [mul_inv_cancel]
    _ = (connectorChange startConnector endConnector *
          connectorChange reference startConnector) *
            (connectorChange reference startConnector)⁻¹ := by
        rw [mul_assoc]
    _ = connectorChange reference endConnector *
          (connectorChange reference startConnector)⁻¹ := by
        congr 1
        exact connectorChange_mul reference startConnector endConnector

/-- 常值中间边的修正环路，使用相对同一参考 connector 的两端 potentials
作为 frames 后严格规范化为单位元。-/
theorem rebase_correctedLoop_refl_eq_one
    {x₀ z : X} (reference startConnector endConnector : Path x₀ z) :
    rebaseEdge
        (connectorChange reference startConnector)
        (connectorChange reference endConnector)
        (FundamentalGroup.fromPath
          ⟦Path.correctedLoop startConnector (Path.refl z) endConnector⟧) = 1 := by
  change rebaseEdge
      (connectorChange reference startConnector)
      (connectorChange reference endConnector)
      (connectorChange startConnector endConnector) = 1
  have hedge := connectorChange_eq_transitionFromPotentials
    reference startConnector endConnector
  rw [hedge]
  exact rebaseEdge_transitionFromPotentials
    (connectorChange reference startConnector)
    (connectorChange reference endConnector)

/-- 群同态保持 potential 比值。-/
theorem map_transitionFromPotentials
    {G K : Type*} [Group G] [Group K] (f : G →* K) (source target : G) :
    f (transitionFromPotentials source target) =
      transitionFromPotentials (f source) (f target) := by
  simp [transitionFromPotentials]

/-- 群同态保持边的 frame 规范化。-/
theorem map_rebaseEdge
    {G K : Type*} [Group G] [Group K] (f : G →* K)
    (startChange endChange edge : G) :
    f (rebaseEdge startChange endChange edge) =
      rebaseEdge (f startChange) (f endChange) (f edge) := by
  simp [rebaseEdge]

/-- 上述常值边规范化结论在任意目标群中仍成立；特别可取为进入
`Monoid.PushoutI` 的单侧生成元同态。-/
theorem map_rebase_correctedLoop_refl_eq_one
    {x₀ z : X} {G : Type*} [Group G]
    (f : FundamentalGroup X x₀ →* G)
    (reference startConnector endConnector : Path x₀ z) :
    rebaseEdge
        (f (connectorChange reference startConnector))
        (f (connectorChange reference endConnector))
        (f (FundamentalGroup.fromPath
          ⟦Path.correctedLoop startConnector (Path.refl z) endConnector⟧)) = 1 := by
  rw [← map_rebaseEdge]
  rw [rebase_correctedLoop_refl_eq_one, map_one]

/-- 应用时的稳定版本：中间边只需在 `Path` 类型中证明等于常值道路，
端点 cast 的证明对象可以由 proof irrelevance 消去。-/
theorem map_rebase_correctedLoop_eq_one_of_segment_eq_refl
    {x₀ z : X} {G : Type*} [Group G]
    (f : FundamentalGroup X x₀ →* G)
    (reference startConnector endConnector : Path x₀ z)
    (segment : Path z z) (hsegment : segment = Path.refl z) :
    rebaseEdge
        (f (connectorChange reference startConnector))
        (f (connectorChange reference endConnector))
        (f (FundamentalGroup.fromPath
          ⟦Path.correctedLoop startConnector segment endConnector⟧)) = 1 := by
  subst segment
  exact map_rebase_correctedLoop_refl_eq_one
    f reference startConnector endConnector

/-- 原始边的两端只要都能 cast 到同一参考端点，且 cast 后的边是常值道路，
则可直接对原始修正环路应用 potential-frame 规范化。-/
theorem map_rebase_correctedLoop_eq_one_of_cast_eq_refl
    {x₀ z w r : X} {G : Type*} [Group G]
    (f : FundamentalGroup X x₀ →* G)
    (reference : Path x₀ r) (startConnector : Path x₀ z)
    (segment : Path z w) (endConnector : Path x₀ w)
    (hz : r = z) (hw : r = w)
    (hsegment : segment.cast hz hw = Path.refl r) :
    rebaseEdge
        (f (connectorChange reference (startConnector.cast rfl hz)))
        (f (connectorChange reference (endConnector.cast rfl hw)))
        (f (FundamentalGroup.fromPath
          ⟦Path.correctedLoop startConnector segment endConnector⟧)) = 1 := by
  have h := map_rebase_correctedLoop_eq_one_of_segment_eq_refl
    f reference (startConnector.cast rfl hz) (endConnector.cast rfl hw)
      (segment.cast hz hw) hsegment
  rw [correctedLoop_cast startConnector segment endConnector hz hw] at h
  exact h

@[simp] theorem transitionFromPotentials_self
    {G : Type*} [Group G] (p : G) :
    transitionFromPotentials p p = 1 := by
  simp [transitionFromPotentials]

/-- potential 给出的 transition 严格复合。-/
theorem transitionFromPotentials_mul
    {G : Type*} [Group G] (a b c : G) :
    transitionFromPotentials b c * transitionFromPotentials a b =
      transitionFromPotentials a c := by
  simp [transitionFromPotentials, mul_assoc]

/-- 四个格角 connector potential 自动给出横后竖与竖后横相同的 frame 传播。-/
theorem transitionFromPotentials_square
    {G : Type*} [Group G]
    (bottomLeft bottomRight topLeft topRight : G) :
    transitionFromPotentials bottomRight topRight *
        transitionFromPotentials bottomLeft bottomRight =
      transitionFromPotentials topLeft topRight *
        transitionFromPotentials bottomLeft topLeft := by
  rw [transitionFromPotentials_mul, transitionFromPotentials_mul]

/-- 一条边的 transition 若由端点两侧的 potentials 比值给出，则任意 source frame 可一致传播。-/
theorem rebaseEdge_potential_transition
    {G : Type*} [Group G]
    (sourceStart sourceEnd targetStart targetEnd edge : G) :
    rebaseEdge
        (transitionFromPotentials sourceStart targetStart)
        (transitionFromPotentials sourceEnd targetEnd) edge =
      rebaseEdge (targetStart * sourceStart⁻¹)
        (targetEnd * sourceEnd⁻¹) edge := by
  rfl

/-- 一个内部网格顶点处，四条相邻边 transition 若来自四个格 connector potentials，
则横后竖与竖后横的 frame 传播相同。-/
theorem edgeTransitions_gridVertex_square
    {G : Type*} [Group G]
    (horizontalBottom verticalRight verticalLeft horizontalTop : EdgeTransitions G)
    (bottomLeft bottomRight topLeft topRight : G)
    (hHorizontalBottom : horizontalBottom.endChange =
      transitionFromPotentials bottomLeft bottomRight)
    (hVerticalRight : verticalRight.startChange =
      transitionFromPotentials bottomRight topRight)
    (hVerticalLeft : verticalLeft.endChange =
      transitionFromPotentials bottomLeft topLeft)
    (hHorizontalTop : horizontalTop.startChange =
      transitionFromPotentials topLeft topRight) :
    verticalRight.startChange * horizontalBottom.endChange =
      horizontalTop.startChange * verticalLeft.endChange := by
  rw [hHorizontalBottom, hVerticalRight, hVerticalLeft, hHorizontalTop]
  exact transitionFromPotentials_square bottomLeft bottomRight topLeft topRight

/-- 水平异标签边起点 transition 由交集参考 connector 的两侧 potentials 给出。-/
theorem BinaryOpenCoverSquareSubdivision.horizontalSwitchEdgeTransitions_start_potential
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (hswitch : D.label i j ≠ D.label k j) :
    let CL := D.horizontalSwitchLeftConnectorComparison hxU hxV hUV hU hV
      i k j hshared hswitch
    let CR := D.horizontalSwitchRightConnectorComparison hxU hxV hUV hU hV
      i k j hshared hswitch
    let T := D.horizontalSwitchEdgeTransitions hxU hxV hUV hU hV
      i k j hshared hswitch
    T.startChange = transitionFromPotentials
      ((Monoid.PushoutI.of (D.label i j) CL.startChange :
        binaryVanKampenPushout U V hxU hxV)⁻¹)
      ((Monoid.PushoutI.of (D.label k j) CR.startChange :
        binaryVanKampenPushout U V hxU hxV)⁻¹) := by
  dsimp only
  unfold BinaryOpenCoverSquareSubdivision.horizontalSwitchEdgeTransitions
  simp [transitionFromPotentials]

/-- 水平异标签边终点 transition 的 potential 表示。-/
theorem BinaryOpenCoverSquareSubdivision.horizontalSwitchEdgeTransitions_end_potential
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (hswitch : D.label i j ≠ D.label k j) :
    let CL := D.horizontalSwitchLeftConnectorComparison hxU hxV hUV hU hV
      i k j hshared hswitch
    let CR := D.horizontalSwitchRightConnectorComparison hxU hxV hUV hU hV
      i k j hshared hswitch
    let T := D.horizontalSwitchEdgeTransitions hxU hxV hUV hU hV
      i k j hshared hswitch
    T.endChange = transitionFromPotentials
      ((Monoid.PushoutI.of (D.label i j) CL.endChange :
        binaryVanKampenPushout U V hxU hxV)⁻¹)
      ((Monoid.PushoutI.of (D.label k j) CR.endChange :
        binaryVanKampenPushout U V hxU hxV)⁻¹) := by
  dsimp only
  unfold BinaryOpenCoverSquareSubdivision.horizontalSwitchEdgeTransitions
  simp [transitionFromPotentials]

/-- 竖直异标签边起点 transition 由交集参考 connector 的两侧 potentials 给出。-/
theorem BinaryOpenCoverSquareSubdivision.verticalSwitchEdgeTransitions_start_potential
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (hswitch : D.label i j ≠ D.label i l) :
    let CB := D.verticalSwitchBottomConnectorComparison hxU hxV hUV hU hV
      i j l hshared hswitch
    let CT := D.verticalSwitchTopConnectorComparison hxU hxV hUV hU hV
      i j l hshared hswitch
    let T := D.verticalSwitchEdgeTransitions hxU hxV hUV hU hV
      i j l hshared hswitch
    T.startChange = transitionFromPotentials
      ((Monoid.PushoutI.of (D.label i j) CB.startChange :
        binaryVanKampenPushout U V hxU hxV)⁻¹)
      ((Monoid.PushoutI.of (D.label i l) CT.startChange :
        binaryVanKampenPushout U V hxU hxV)⁻¹) := by
  dsimp only
  unfold BinaryOpenCoverSquareSubdivision.verticalSwitchEdgeTransitions
  simp [transitionFromPotentials]

/-- 竖直异标签边终点 transition 的 potential 表示。-/
theorem BinaryOpenCoverSquareSubdivision.verticalSwitchEdgeTransitions_end_potential
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (hswitch : D.label i j ≠ D.label i l) :
    let CB := D.verticalSwitchBottomConnectorComparison hxU hxV hUV hU hV
      i j l hshared hswitch
    let CT := D.verticalSwitchTopConnectorComparison hxU hxV hUV hU hV
      i j l hshared hswitch
    let T := D.verticalSwitchEdgeTransitions hxU hxV hUV hU hV
      i j l hshared hswitch
    T.endChange = transitionFromPotentials
      ((Monoid.PushoutI.of (D.label i j) CB.endChange :
        binaryVanKampenPushout U V hxU hxV)⁻¹)
      ((Monoid.PushoutI.of (D.label i l) CT.endChange :
        binaryVanKampenPushout U V hxU hxV)⁻¹) := by
  dsimp only
  unfold BinaryOpenCoverSquareSubdivision.verticalSwitchEdgeTransitions
  simp [transitionFromPotentials]

/-- 相对于任意共同参考 connector 的两个 potentials，其比值就是两 connector 的直接变化。-/
theorem transitionFromConnectorPotentials
    {x₀ z : X} (reference source target : Path x₀ z) :
    transitionFromPotentials
        (connectorChange reference source)
        (connectorChange reference target) =
      connectorChange source target := by
  rw [connectorChange_reverse source reference]
  unfold transitionFromPotentials
  rw [inv_inv, connectorChange_mul]

/-- 上述参考 connector 公式在任意目标群同态中的版本。-/
theorem map_transitionFromConnectorPotentials
    {S G : Type*} [TopologicalSpace S] [Group G] {base z : S}
    (f : FundamentalGroup S base →* G)
    (reference source target : Path base z) :
    transitionFromPotentials
        (f (connectorChange reference source))
        (f (connectorChange reference target)) =
      f (connectorChange source target) := by
  unfold transitionFromPotentials
  rw [← map_inv, ← map_mul]
  rw [← transitionFromPotentials, transitionFromConnectorPotentials]

theorem CommonEdgeConnectorComparison.map_startChange_inv
    {S G : Type*} [TopologicalSpace S] [Group G] {base : S}
    (C : CommonEdgeConnectorComparison S base)
    (f : FundamentalGroup S base →* G) :
    (f C.startChange)⁻¹ = f (connectorChange C.leftStart C.rightStart) := by
  rw [C.startChange_eq_connectorChange, ← map_inv,
    ← connectorChange_reverse]

theorem CommonEdgeConnectorComparison.map_endChange_inv
    {S G : Type*} [TopologicalSpace S] [Group G] {base : S}
    (C : CommonEdgeConnectorComparison S base)
    (f : FundamentalGroup S base →* G) :
    (f C.endChange)⁻¹ = f (connectorChange C.leftEnd C.rightEnd) := by
  rw [C.endChange_eq_connectorChange, ← map_inv,
    ← connectorChange_reverse]

theorem CommonEdgeConnectorComparison.map_startChange_inv_eq_potentials
    {S G : Type*} [TopologicalSpace S] [Group G] {base : S}
    (C : CommonEdgeConnectorComparison S base)
    (f : FundamentalGroup S base →* G)
    (reference : Path base C.edgeSource) :
    (f C.startChange)⁻¹ = transitionFromPotentials
      (f (connectorChange reference C.leftStart))
      (f (connectorChange reference C.rightStart)) := by
  rw [C.map_startChange_inv]
  symm
  exact map_transitionFromConnectorPotentials f reference C.leftStart C.rightStart

theorem CommonEdgeConnectorComparison.map_endChange_inv_eq_potentials
    {S G : Type*} [TopologicalSpace S] [Group G] {base : S}
    (C : CommonEdgeConnectorComparison S base)
    (f : FundamentalGroup S base →* G)
    (reference : Path base C.edgeTarget) :
    (f C.endChange)⁻¹ = transitionFromPotentials
      (f (connectorChange reference C.leftEnd))
      (f (connectorChange reference C.rightEnd)) := by
  rw [C.map_endChange_inv]
  symm
  exact map_transitionFromConnectorPotentials f reference C.leftEnd C.rightEnd

/-- 同时把两条 connector transport 到相等端点，不改变 connector change。-/
theorem connectorChange_cast {x₀ z z' : X}
    (p q : Path x₀ z) (hz : z' = z) :
    connectorChange (p.cast rfl hz) (q.cast rfl hz) = connectorChange p q := by
  cases hz
  rfl

/-- 两条 connector 使用不同的 proof-irrelevant 终点 transport 证明时，change 仍不变。-/
theorem connectorChange_cast_proof_irrel {x₀ z z' : X}
    (p q : Path x₀ z) (hp hq : z' = z) :
    connectorChange (p.cast rfl hp) (q.cast rfl hq) = connectorChange p q := by
  rw [Subsingleton.elim hp hq]
  exact connectorChange_cast p q hq

/-- 四个同一 piece 的公共边 comparison transport 到共同网格顶点后满足方块 coherence。-/
private theorem commonEdgeComparisons_gridVertex_square
    {S G : Type*} [TopologicalSpace S] [Group G] {base z : S}
    (f : FundamentalGroup S base →* G)
    (horizontalBottom verticalRight verticalLeft horizontalTop :
      CommonEdgeConnectorComparison S base)
    (hHorizontalBottom : z = horizontalBottom.edgeTarget)
    (hVerticalRight : z = verticalRight.edgeSource)
    (hVerticalLeft : z = verticalLeft.edgeTarget)
    (hHorizontalTop : z = horizontalTop.edgeSource)
    (bottomLeft bottomRight topLeft topRight : Path base z)
    (hBottomLeft : horizontalBottom.leftEnd.cast rfl hHorizontalBottom = bottomLeft)
    (hBottomRight : horizontalBottom.rightEnd.cast rfl hHorizontalBottom = bottomRight)
    (hRightBottom : verticalRight.leftStart.cast rfl hVerticalRight = bottomRight)
    (hRightTop : verticalRight.rightStart.cast rfl hVerticalRight = topRight)
    (hLeftBottom : verticalLeft.leftEnd.cast rfl hVerticalLeft = bottomLeft)
    (hLeftTop : verticalLeft.rightEnd.cast rfl hVerticalLeft = topLeft)
    (hTopLeft : horizontalTop.leftStart.cast rfl hHorizontalTop = topLeft)
    (hTopRight : horizontalTop.rightStart.cast rfl hHorizontalTop = topRight) :
    (f verticalRight.startChange)⁻¹ * (f horizontalBottom.endChange)⁻¹ =
      (f horizontalTop.startChange)⁻¹ * (f verticalLeft.endChange)⁻¹ := by
  rw [verticalRight.map_startChange_inv, horizontalBottom.map_endChange_inv,
    horizontalTop.map_startChange_inv, verticalLeft.map_endChange_inv]
  rw [← connectorChange_cast verticalRight.leftStart verticalRight.rightStart hVerticalRight,
    ← connectorChange_cast horizontalBottom.leftEnd horizontalBottom.rightEnd hHorizontalBottom,
    ← connectorChange_cast horizontalTop.leftStart horizontalTop.rightStart hHorizontalTop,
    ← connectorChange_cast verticalLeft.leftEnd verticalLeft.rightEnd hVerticalLeft]
  rw [hBottomLeft, hBottomRight, hRightBottom, hRightTop,
    hLeftBottom, hLeftTop, hTopLeft, hTopRight]
  exact (map_connectorChange_square f bottomLeft bottomRight topLeft topRight).symm

omit [TopologicalSpace X] in
@[simp] private theorem coe_binaryOpenCoverPiece_label_cast
    {U V : Set X} {b c : Bool} (h : b = c) (z : binaryOpenCoverPiece U V c) :
    (((h.symm ▸ z : binaryOpenCoverPiece U V b) : X)) = z := by
  cases h
  rfl

/-- 以显式共同 Bool 标签承载水平同标签 comparison，避免多格证明中的依赖消去。-/
def BinaryOpenCoverSquareSubdivision.horizontalCommonEdgeConnectorComparisonOfLabel
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j : Fin D.steps) (hshared : i.succ = k.castSucc)
    (b : Bool) (hleft : D.label i j = b) (hright : D.label k j = b) :
    CommonEdgeConnectorComparison (binaryOpenCoverPiece U V b)
      (binaryOpenCoverBasepoint hxU hxV b) := by
  exact hleft ▸ D.horizontalCommonEdgeConnectorComparison hxU hxV hU hV
    i k j hshared (hleft.trans hright.symm)

/-- 以显式共同 Bool 标签承载竖直同标签 comparison。-/
def BinaryOpenCoverSquareSubdivision.verticalCommonEdgeConnectorComparisonOfLabel
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j l : Fin D.steps) (hshared : j.succ = l.castSucc)
    (b : Bool) (hbottom : D.label i j = b) (htop : D.label i l = b) :
    CommonEdgeConnectorComparison (binaryOpenCoverPiece U V b)
      (binaryOpenCoverBasepoint hxU hxV b) := by
  exact hbottom ▸ D.verticalCommonEdgeConnectorComparison hxU hxV hU hV
    i j l hshared (hbottom.trans htop.symm)

@[simp] private theorem coe_commonEdgeConnectorComparison_label_cast_edgeSource
    {U V : Set X} {x₀ : X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    {b c : Bool} (h : b = c)
    (C : CommonEdgeConnectorComparison (binaryOpenCoverPiece U V b)
      (binaryOpenCoverBasepoint hxU hxV b)) :
    ((((h ▸ C).edgeSource : binaryOpenCoverPiece U V c)) : X) = C.edgeSource := by
  cases h
  rfl

@[simp] private theorem coe_commonEdgeConnectorComparison_label_cast_edgeTarget
    {U V : Set X} {x₀ : X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    {b c : Bool} (h : b = c)
    (C : CommonEdgeConnectorComparison (binaryOpenCoverPiece U V b)
      (binaryOpenCoverBasepoint hxU hxV b)) :
    ((((h ▸ C).edgeTarget : binaryOpenCoverPiece U V c)) : X) = C.edgeTarget := by
  cases h
  rfl

@[simp] private theorem coe_commonEdgeConnectorComparison_label_cast_leftStart
    {U V : Set X} {x₀ : X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    {b c : Bool} (h : b = c)
    (C : CommonEdgeConnectorComparison (binaryOpenCoverPiece U V b)
      (binaryOpenCoverBasepoint hxU hxV b)) (t : unitInterval) :
    (((h ▸ C).leftStart t : binaryOpenCoverPiece U V c) : X) = C.leftStart t := by
  cases h
  rfl

@[simp] private theorem coe_commonEdgeConnectorComparison_label_cast_leftEnd
    {U V : Set X} {x₀ : X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    {b c : Bool} (h : b = c)
    (C : CommonEdgeConnectorComparison (binaryOpenCoverPiece U V b)
      (binaryOpenCoverBasepoint hxU hxV b)) (t : unitInterval) :
    (((h ▸ C).leftEnd t : binaryOpenCoverPiece U V c) : X) = C.leftEnd t := by
  cases h
  rfl

@[simp] private theorem coe_commonEdgeConnectorComparison_label_cast_rightStart
    {U V : Set X} {x₀ : X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    {b c : Bool} (h : b = c)
    (C : CommonEdgeConnectorComparison (binaryOpenCoverPiece U V b)
      (binaryOpenCoverBasepoint hxU hxV b)) (t : unitInterval) :
    (((h ▸ C).rightStart t : binaryOpenCoverPiece U V c) : X) = C.rightStart t := by
  cases h
  rfl

@[simp] private theorem coe_commonEdgeConnectorComparison_label_cast_rightEnd
    {U V : Set X} {x₀ : X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    {b c : Bool} (h : b = c)
    (C : CommonEdgeConnectorComparison (binaryOpenCoverPiece U V b)
      (binaryOpenCoverBasepoint hxU hxV b)) (t : unitInterval) :
    (((h ▸ C).rightEnd t : binaryOpenCoverPiece U V c) : X) = C.rightEnd t := by
  cases h
  rfl

/-- 显式共同标签包装下，下水平终点与右竖直起点直接相等。-/
private theorem
    BinaryOpenCoverSquareSubdivision.commonCentralVertexOfLabel_horizontalBottom_verticalRight
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j l : Fin D.steps)
    (hHorizontal : i.succ = k.castSucc) (hVertical : j.succ = l.castSucc)
    (b : Bool)
    (hBL : D.label i j = b) (hBR : D.label k j = b)
    (hTR : D.label k l = b) :
    let HB := D.horizontalCommonEdgeConnectorComparisonOfLabel hxU hxV hU hV
      i k j hHorizontal b hBL hBR
    let VR := D.verticalCommonEdgeConnectorComparisonOfLabel hxU hxV hU hV
      k j l hVertical b hBR hTR
    HB.edgeTarget = VR.edgeSource := by
  apply Subtype.ext
  rw [show D.horizontalCommonEdgeConnectorComparisonOfLabel hxU hxV hU hV
      i k j hHorizontal b hBL hBR =
      hBL ▸ D.horizontalCommonEdgeConnectorComparison hxU hxV hU hV
        i k j hHorizontal (hBL.trans hBR.symm) by rfl]
  rw [show D.verticalCommonEdgeConnectorComparisonOfLabel hxU hxV hU hV
      k j l hVertical b hBR hTR =
      hBR ▸ D.verticalCommonEdgeConnectorComparison hxU hxV hU hV
        k j l hVertical (hBR.trans hTR.symm) by rfl]
  rw [coe_commonEdgeConnectorComparison_label_cast_edgeTarget,
    coe_commonEdgeConnectorComparison_label_cast_edgeSource]
  simp [BinaryOpenCoverSquareSubdivision.horizontalCommonEdgeConnectorComparison,
    BinaryOpenCoverSquareSubdivision.verticalCommonEdgeConnectorComparison,
    squareGridVertex, hHorizontal]

/-- 显式共同标签下，右下格在两条 incident comparisons 中使用同一中央 connector。-/
private theorem BinaryOpenCoverSquareSubdivision.commonCentralConnectorOfLabel_rightBottom
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j l : Fin D.steps)
    (hHorizontal : i.succ = k.castSucc) (hVertical : j.succ = l.castSucc)
    (b : Bool)
    (hBL : D.label i j = b) (hBR : D.label k j = b)
    (hTR : D.label k l = b) :
    let HB := D.horizontalCommonEdgeConnectorComparisonOfLabel hxU hxV hU hV
      i k j hHorizontal b hBL hBR
    let VR := D.verticalCommonEdgeConnectorComparisonOfLabel hxU hxV hU hV
      k j l hVertical b hBR hTR
    let hpoint := D.commonCentralVertexOfLabel_horizontalBottom_verticalRight
      hxU hxV hU hV i k j l hHorizontal hVertical b hBL hBR hTR
    VR.leftStart.cast rfl hpoint = HB.rightEnd := by
  apply Path.ext
  calc
    ((D.verticalCommonEdgeConnectorComparisonOfLabel hxU hxV hU hV
        k j l hVertical b hBR hTR).leftStart.cast rfl
          (D.commonCentralVertexOfLabel_horizontalBottom_verticalRight
            hxU hxV hU hV i k j l hHorizontal hVertical b hBL hBR hTR) :
      unitInterval → binaryOpenCoverPiece U V b) =
        (D.verticalCommonEdgeConnectorComparisonOfLabel hxU hxV hU hV
          k j l hVertical b hBR hTR).leftStart :=
      Path.cast_coe _ _ _
    _ = (D.horizontalCommonEdgeConnectorComparisonOfLabel hxU hxV hU hV
          i k j hHorizontal b hBL hBR).rightEnd := by
      funext t
      apply Subtype.ext
      rw [show D.verticalCommonEdgeConnectorComparisonOfLabel hxU hxV hU hV
          k j l hVertical b hBR hTR =
          hBR ▸ D.verticalCommonEdgeConnectorComparison hxU hxV hU hV
            k j l hVertical (hBR.trans hTR.symm) by rfl]
      rw [show D.horizontalCommonEdgeConnectorComparisonOfLabel hxU hxV hU hV
          i k j hHorizontal b hBL hBR =
          hBL ▸ D.horizontalCommonEdgeConnectorComparison hxU hxV hU hV
            i k j hHorizontal (hBL.trans hBR.symm) by rfl]
      rw [coe_commonEdgeConnectorComparison_label_cast_leftStart,
        coe_commonEdgeConnectorComparison_label_cast_rightEnd]
      unfold BinaryOpenCoverSquareSubdivision.verticalCommonEdgeConnectorComparison
        BinaryOpenCoverSquareSubdivision.horizontalCommonEdgeConnectorComparison
      rw [Path.cast_coe, Path.cast_coe]
      simpa
        using D.coe_gridCellVertexConnectorInPieceOfLabel_eq hxU hxV hU hV
          k j 0 1 (D.label k j) (D.label i j) rfl
          (hBL.trans hBR.symm).symm t

/-- 显式共同标签包装下，下水平终点与左竖直终点直接相等。-/
private theorem
    BinaryOpenCoverSquareSubdivision.commonCentralVertexOfLabel_horizontalBottom_verticalLeft
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j l : Fin D.steps)
    (hHorizontal : i.succ = k.castSucc) (hVertical : j.succ = l.castSucc)
    (b : Bool)
    (hBL : D.label i j = b) (hBR : D.label k j = b)
    (hTL : D.label i l = b) :
    let HB := D.horizontalCommonEdgeConnectorComparisonOfLabel hxU hxV hU hV
      i k j hHorizontal b hBL hBR
    let VL := D.verticalCommonEdgeConnectorComparisonOfLabel hxU hxV hU hV
      i j l hVertical b hBL hTL
    HB.edgeTarget = VL.edgeTarget := by
  apply Subtype.ext
  rw [show D.horizontalCommonEdgeConnectorComparisonOfLabel hxU hxV hU hV
      i k j hHorizontal b hBL hBR =
      hBL ▸ D.horizontalCommonEdgeConnectorComparison hxU hxV hU hV
        i k j hHorizontal (hBL.trans hBR.symm) by rfl]
  rw [show D.verticalCommonEdgeConnectorComparisonOfLabel hxU hxV hU hV
      i j l hVertical b hBL hTL =
      hBL ▸ D.verticalCommonEdgeConnectorComparison hxU hxV hU hV
        i j l hVertical (hBL.trans hTL.symm) by rfl]
  rw [coe_commonEdgeConnectorComparison_label_cast_edgeTarget,
    coe_commonEdgeConnectorComparison_label_cast_edgeTarget]
  rfl

/-- 显式共同标签包装下，下水平终点与上水平起点直接相等。-/
private theorem
    BinaryOpenCoverSquareSubdivision.commonCentralVertexOfLabel_horizontalBottom_horizontalTop
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j l : Fin D.steps)
    (hHorizontal : i.succ = k.castSucc) (hVertical : j.succ = l.castSucc)
    (b : Bool)
    (hBL : D.label i j = b) (hBR : D.label k j = b)
    (hTL : D.label i l = b) (hTR : D.label k l = b) :
    let HB := D.horizontalCommonEdgeConnectorComparisonOfLabel hxU hxV hU hV
      i k j hHorizontal b hBL hBR
    let HT := D.horizontalCommonEdgeConnectorComparisonOfLabel hxU hxV hU hV
      i k l hHorizontal b hTL hTR
    HB.edgeTarget = HT.edgeSource := by
  apply Subtype.ext
  rw [show D.horizontalCommonEdgeConnectorComparisonOfLabel hxU hxV hU hV
      i k j hHorizontal b hBL hBR =
      hBL ▸ D.horizontalCommonEdgeConnectorComparison hxU hxV hU hV
        i k j hHorizontal (hBL.trans hBR.symm) by rfl]
  rw [show D.horizontalCommonEdgeConnectorComparisonOfLabel hxU hxV hU hV
      i k l hHorizontal b hTL hTR =
      hTL ▸ D.horizontalCommonEdgeConnectorComparison hxU hxV hU hV
        i k l hHorizontal (hTL.trans hTR.symm) by rfl]
  rw [coe_commonEdgeConnectorComparison_label_cast_edgeTarget,
    coe_commonEdgeConnectorComparison_label_cast_edgeSource]
  simp [BinaryOpenCoverSquareSubdivision.horizontalCommonEdgeConnectorComparison,
    squareGridVertex, hVertical]

/-- 显式共同标签下，左下格在两条 incident comparisons 中使用同一中央 connector。-/
private theorem BinaryOpenCoverSquareSubdivision.commonCentralConnectorOfLabel_leftBottom
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j l : Fin D.steps)
    (hHorizontal : i.succ = k.castSucc) (hVertical : j.succ = l.castSucc)
    (b : Bool)
    (hBL : D.label i j = b) (hBR : D.label k j = b)
    (hTL : D.label i l = b) :
    let HB := D.horizontalCommonEdgeConnectorComparisonOfLabel hxU hxV hU hV
      i k j hHorizontal b hBL hBR
    let VL := D.verticalCommonEdgeConnectorComparisonOfLabel hxU hxV hU hV
      i j l hVertical b hBL hTL
    let hpoint := D.commonCentralVertexOfLabel_horizontalBottom_verticalLeft
      hxU hxV hU hV i k j l hHorizontal hVertical b hBL hBR hTL
    VL.leftEnd.cast rfl hpoint = HB.leftEnd := by
  apply Path.ext
  calc
    ((D.verticalCommonEdgeConnectorComparisonOfLabel hxU hxV hU hV
        i j l hVertical b hBL hTL).leftEnd.cast rfl
          (D.commonCentralVertexOfLabel_horizontalBottom_verticalLeft
            hxU hxV hU hV i k j l hHorizontal hVertical b hBL hBR hTL) :
      unitInterval → binaryOpenCoverPiece U V b) =
        (D.verticalCommonEdgeConnectorComparisonOfLabel hxU hxV hU hV
          i j l hVertical b hBL hTL).leftEnd :=
      Path.cast_coe _ _ _
    _ = (D.horizontalCommonEdgeConnectorComparisonOfLabel hxU hxV hU hV
          i k j hHorizontal b hBL hBR).leftEnd := by
      funext t
      apply Subtype.ext
      rw [show D.verticalCommonEdgeConnectorComparisonOfLabel hxU hxV hU hV
          i j l hVertical b hBL hTL =
          hBL ▸ D.verticalCommonEdgeConnectorComparison hxU hxV hU hV
            i j l hVertical (hBL.trans hTL.symm) by rfl]
      rw [show D.horizontalCommonEdgeConnectorComparisonOfLabel hxU hxV hU hV
          i k j hHorizontal b hBL hBR =
          hBL ▸ D.horizontalCommonEdgeConnectorComparison hxU hxV hU hV
            i k j hHorizontal (hBL.trans hBR.symm) by rfl]
      rw [coe_commonEdgeConnectorComparison_label_cast_leftEnd,
        coe_commonEdgeConnectorComparison_label_cast_leftEnd]
      unfold BinaryOpenCoverSquareSubdivision.verticalCommonEdgeConnectorComparison
        BinaryOpenCoverSquareSubdivision.horizontalCommonEdgeConnectorComparison
      simp only [Path.cast_coe]

/-- 显式共同标签下，左上格在两条 incident comparisons 中使用同一中央 connector。-/
private theorem BinaryOpenCoverSquareSubdivision.commonCentralConnectorOfLabel_leftTop
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j l : Fin D.steps)
    (hHorizontal : i.succ = k.castSucc) (hVertical : j.succ = l.castSucc)
    (b : Bool)
    (hBL : D.label i j = b) (hBR : D.label k j = b)
    (hTL : D.label i l = b) (hTR : D.label k l = b) :
    let _HB := D.horizontalCommonEdgeConnectorComparisonOfLabel hxU hxV hU hV
      i k j hHorizontal b hBL hBR
    let VL := D.verticalCommonEdgeConnectorComparisonOfLabel hxU hxV hU hV
      i j l hVertical b hBL hTL
    let HT := D.horizontalCommonEdgeConnectorComparisonOfLabel hxU hxV hU hV
      i k l hHorizontal b hTL hTR
    let hleft := D.commonCentralVertexOfLabel_horizontalBottom_verticalLeft
      hxU hxV hU hV i k j l hHorizontal hVertical b hBL hBR hTL
    let htop := D.commonCentralVertexOfLabel_horizontalBottom_horizontalTop
      hxU hxV hU hV i k j l hHorizontal hVertical b hBL hBR hTL hTR
    VL.rightEnd.cast rfl hleft = HT.leftStart.cast rfl htop := by
  apply Path.ext
  calc
    ((D.verticalCommonEdgeConnectorComparisonOfLabel hxU hxV hU hV
        i j l hVertical b hBL hTL).rightEnd.cast rfl
          (D.commonCentralVertexOfLabel_horizontalBottom_verticalLeft
            hxU hxV hU hV i k j l hHorizontal hVertical b hBL hBR hTL) :
      unitInterval → binaryOpenCoverPiece U V b) =
        (D.verticalCommonEdgeConnectorComparisonOfLabel hxU hxV hU hV
          i j l hVertical b hBL hTL).rightEnd :=
      Path.cast_coe _ _ _
    _ = (D.horizontalCommonEdgeConnectorComparisonOfLabel hxU hxV hU hV
          i k l hHorizontal b hTL hTR).leftStart := by
      funext t
      apply Subtype.ext
      rw [show D.verticalCommonEdgeConnectorComparisonOfLabel hxU hxV hU hV
          i j l hVertical b hBL hTL =
          hBL ▸ D.verticalCommonEdgeConnectorComparison hxU hxV hU hV
            i j l hVertical (hBL.trans hTL.symm) by rfl]
      rw [show D.horizontalCommonEdgeConnectorComparisonOfLabel hxU hxV hU hV
          i k l hHorizontal b hTL hTR =
          hTL ▸ D.horizontalCommonEdgeConnectorComparison hxU hxV hU hV
            i k l hHorizontal (hTL.trans hTR.symm) by rfl]
      rw [coe_commonEdgeConnectorComparison_label_cast_rightEnd,
        coe_commonEdgeConnectorComparison_label_cast_leftStart]
      unfold BinaryOpenCoverSquareSubdivision.verticalCommonEdgeConnectorComparison
        BinaryOpenCoverSquareSubdivision.horizontalCommonEdgeConnectorComparison
      rw [Path.cast_coe, Path.cast_coe]
      simpa using D.coe_gridCellVertexConnectorInPieceOfLabel_eq hxU hxV hU hV
        i l 1 0 (D.label i j) (D.label i l)
        (hBL.trans hTL.symm).symm rfl t
    _ = ((D.horizontalCommonEdgeConnectorComparisonOfLabel hxU hxV hU hV
          i k l hHorizontal b hTL hTR).leftStart.cast rfl
            (D.commonCentralVertexOfLabel_horizontalBottom_horizontalTop
              hxU hxV hU hV i k j l hHorizontal hVertical b hBL hBR hTL hTR) :
        unitInterval → binaryOpenCoverPiece U V b) :=
      (Path.cast_coe _ _ _).symm

/-- 显式共同标签下，右上格在两条 incident comparisons 中使用同一中央 connector。-/
private theorem BinaryOpenCoverSquareSubdivision.commonCentralConnectorOfLabel_rightTop
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j l : Fin D.steps)
    (hHorizontal : i.succ = k.castSucc) (hVertical : j.succ = l.castSucc)
    (b : Bool)
    (hBL : D.label i j = b) (hBR : D.label k j = b)
    (hTL : D.label i l = b) (hTR : D.label k l = b) :
    let _HB := D.horizontalCommonEdgeConnectorComparisonOfLabel hxU hxV hU hV
      i k j hHorizontal b hBL hBR
    let VR := D.verticalCommonEdgeConnectorComparisonOfLabel hxU hxV hU hV
      k j l hVertical b hBR hTR
    let HT := D.horizontalCommonEdgeConnectorComparisonOfLabel hxU hxV hU hV
      i k l hHorizontal b hTL hTR
    let hright := D.commonCentralVertexOfLabel_horizontalBottom_verticalRight
      hxU hxV hU hV i k j l hHorizontal hVertical b hBL hBR hTR
    let htop := D.commonCentralVertexOfLabel_horizontalBottom_horizontalTop
      hxU hxV hU hV i k j l hHorizontal hVertical b hBL hBR hTL hTR
    VR.rightStart.cast rfl hright = HT.rightStart.cast rfl htop := by
  apply Path.ext
  calc
    ((D.verticalCommonEdgeConnectorComparisonOfLabel hxU hxV hU hV
        k j l hVertical b hBR hTR).rightStart.cast rfl
          (D.commonCentralVertexOfLabel_horizontalBottom_verticalRight
            hxU hxV hU hV i k j l hHorizontal hVertical b hBL hBR hTR) :
      unitInterval → binaryOpenCoverPiece U V b) =
        (D.verticalCommonEdgeConnectorComparisonOfLabel hxU hxV hU hV
          k j l hVertical b hBR hTR).rightStart :=
      Path.cast_coe _ _ _
    _ = (D.horizontalCommonEdgeConnectorComparisonOfLabel hxU hxV hU hV
          i k l hHorizontal b hTL hTR).rightStart := by
      funext t
      apply Subtype.ext
      rw [show D.verticalCommonEdgeConnectorComparisonOfLabel hxU hxV hU hV
          k j l hVertical b hBR hTR =
          hBR ▸ D.verticalCommonEdgeConnectorComparison hxU hxV hU hV
            k j l hVertical (hBR.trans hTR.symm) by rfl]
      rw [show D.horizontalCommonEdgeConnectorComparisonOfLabel hxU hxV hU hV
          i k l hHorizontal b hTL hTR =
          hTL ▸ D.horizontalCommonEdgeConnectorComparison hxU hxV hU hV
            i k l hHorizontal (hTL.trans hTR.symm) by rfl]
      rw [coe_commonEdgeConnectorComparison_label_cast_rightStart,
        coe_commonEdgeConnectorComparison_label_cast_rightStart]
      unfold BinaryOpenCoverSquareSubdivision.verticalCommonEdgeConnectorComparison
        BinaryOpenCoverSquareSubdivision.horizontalCommonEdgeConnectorComparison
      rw [Path.cast_coe, Path.cast_coe]
      simpa using D.coe_gridCellVertexConnectorInPieceOfLabel_eq hxU hxV hU hV
        k l 0 0 (D.label k j) (D.label i l)
        (hBR.trans hTR.symm).symm (hTL.trans hTR.symm).symm t
    _ = ((D.horizontalCommonEdgeConnectorComparisonOfLabel hxU hxV hU hV
          i k l hHorizontal b hTL hTR).rightStart.cast rfl
            (D.commonCentralVertexOfLabel_horizontalBottom_horizontalTop
              hxU hxV hU hV i k j l hHorizontal hVertical b hBL hBR hTL hTR) :
        unitInterval → binaryOpenCoverPiece U V b) :=
      (Path.cast_coe _ _ _).symm

/-- 四个相邻小格具有同一标签时，中央顶点的四个换连接因子满足方块关系。-/
theorem BinaryOpenCoverSquareSubdivision.commonCentralTransition_square_of_label
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k j l : Fin D.steps)
    (hHorizontal : i.succ = k.castSucc) (hVertical : j.succ = l.castSucc)
    (b : Bool)
    (hBL : D.label i j = b) (hBR : D.label k j = b)
    (hTL : D.label i l = b) (hTR : D.label k l = b) :
    let HB := D.horizontalCommonEdgeConnectorComparisonOfLabel hxU hxV hU hV
      i k j hHorizontal b hBL hBR
    let VR := D.verticalCommonEdgeConnectorComparisonOfLabel hxU hxV hU hV
      k j l hVertical b hBR hTR
    let VL := D.verticalCommonEdgeConnectorComparisonOfLabel hxU hxV hU hV
      i j l hVertical b hBL hTL
    let HT := D.horizontalCommonEdgeConnectorComparisonOfLabel hxU hxV hU hV
      i k l hHorizontal b hTL hTR
    let f : FundamentalGroup (binaryOpenCoverPiece U V b)
        (binaryOpenCoverBasepoint hxU hxV b) →* binaryVanKampenPushout U V hxU hxV :=
      Monoid.PushoutI.of (φ := binaryOpenCoverIntersectionMaps U V hxU hxV) b
    (f VR.startChange)⁻¹ * (f HB.endChange)⁻¹ =
      (f HT.startChange)⁻¹ * (f VL.endChange)⁻¹ := by
  let HB := D.horizontalCommonEdgeConnectorComparisonOfLabel hxU hxV hU hV
    i k j hHorizontal b hBL hBR
  let VR := D.verticalCommonEdgeConnectorComparisonOfLabel hxU hxV hU hV
    k j l hVertical b hBR hTR
  let VL := D.verticalCommonEdgeConnectorComparisonOfLabel hxU hxV hU hV
    i j l hVertical b hBL hTL
  let HT := D.horizontalCommonEdgeConnectorComparisonOfLabel hxU hxV hU hV
    i k l hHorizontal b hTL hTR
  let f : FundamentalGroup (binaryOpenCoverPiece U V b)
      (binaryOpenCoverBasepoint hxU hxV b) →* binaryVanKampenPushout U V hxU hxV :=
    Monoid.PushoutI.of (φ := binaryOpenCoverIntersectionMaps U V hxU hxV) b
  let hright := D.commonCentralVertexOfLabel_horizontalBottom_verticalRight
    hxU hxV hU hV i k j l hHorizontal hVertical b hBL hBR hTR
  let hleft := D.commonCentralVertexOfLabel_horizontalBottom_verticalLeft
    hxU hxV hU hV i k j l hHorizontal hVertical b hBL hBR hTL
  let htop := D.commonCentralVertexOfLabel_horizontalBottom_horizontalTop
    hxU hxV hU hV i k j l hHorizontal hVertical b hBL hBR hTL hTR
  apply commonEdgeComparisons_gridVertex_square f HB VR VL HT rfl hright hleft htop
    HB.leftEnd HB.rightEnd (HT.leftStart.cast rfl htop) (HT.rightStart.cast rfl htop)
  · exact Path.cast_rfl_rfl _
  · exact Path.cast_rfl_rfl _
  · exact D.commonCentralConnectorOfLabel_rightBottom hxU hxV hU hV
      i k j l hHorizontal hVertical b hBL hBR hTR
  · exact D.commonCentralConnectorOfLabel_rightTop hxU hxV hU hV
      i k j l hHorizontal hVertical b hBL hBR hTL hTR
  · exact D.commonCentralConnectorOfLabel_leftBottom hxU hxV hU hV
      i k j l hHorizontal hVertical b hBL hBR hTL
  · exact D.commonCentralConnectorOfLabel_leftTop hxU hxV hU hV
      i k j l hHorizontal hVertical b hBL hBR hTL hTR
  · rfl
  · rfl

/-- 以一个交集点的规范 connector 为参考，记录同一点在任一覆盖成员中的局部 connector 所给出的
Pushout vertex potential。该定义与方格坐标无关。-/
def binaryOpenCoverVertexPotentialFromIntersection
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hUV : IsPathConnected (U ∩ V)) (z : ↥(U ∩ V)) (d : Bool)
    (w : binaryOpenCoverPiece U V d)
    (localConnector : Path (binaryOpenCoverBasepoint hxU hxV d) w)
    (hz : binaryOpenCoverIntersectionToPiece U V d z = w) :
    binaryVanKampenPushout U V hxU hxV :=
  let hbase := binaryOpenCoverBasepoint_eq_intersectionToPiece hxU hxV d
  let reference :=
    (binaryOpenCoverIntersectionConnectorInPiece hxU hxV hUV d z).cast
      hbase hz.symm
  Monoid.PushoutI.of d (connectorChange reference localConnector)
/-- 不要求顶点位于交集的共同成员 connector potential。它只记录相对于任意参考 connector 的
局部 connector 在 Pushout 中的像。-/
def binaryOpenCoverConnectorPotential
    {x₀ : X} {U V : Set X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (d : Bool) (w : binaryOpenCoverPiece U V d)
    (reference localConnector : Path (binaryOpenCoverBasepoint hxU hxV d) w) :
    binaryVanKampenPushout U V hxU hxV :=
  Monoid.PushoutI.of d (connectorChange reference localConnector)

end SandronesLibrary.Topology
