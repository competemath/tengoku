/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.VanKampenRebasedLetterWord

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# van Kampen 余规范消去

本文件比较顶点 potential 与边界 frame 的相对误差，并沿同伦方形的下、右、上三边传播这一余规范。
结论把完整左边界 telescope 的首末残余 frame 联系起来；本文件尚不证明 kernel 平凡或最终同构。
-/

open Set
open scoped unitInterval

noncomputable section

namespace SandronesLibrary.Topology

variable {X : Type*} [TopologicalSpace X]

omit [TopologicalSpace X] in
private theorem coe_binaryOpenCoverBasepoint_for_residualGauge
    {U V : Set X} {x₀ : X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (b : Bool) :
    ((binaryOpenCoverBasepoint hxU hxV b : binaryOpenCoverPiece U V b) : X) = x₀ := by
  cases b <;> rfl

/-- 若边 transition 是两端 potential 的比，而两端 frame 与该 transition 相容，则右余规范
`potential⁻¹ * frame` 穿过这条边保持不变。这是比较左边界 telescope 两端 frame 的代数传播步骤。

> **Entry**: topology.fundamental-group.van-kampen-residual-gauge
@isnad1 id=eq.2h6v.s6.6618d5084426 from=translated src=- shape=5cf9608c vocab=ed901023
-/
theorem potentialNormalizedFrame_eq_of_compatible
    {G : Type*} [Group G]
    (sourcePotential targetPotential sourceFrame targetFrame transition : G)
    (htransition : transition =
      transitionFromPotentials sourcePotential targetPotential)
    (hframe : targetFrame = transition * sourceFrame) :
    sourcePotential⁻¹ * sourceFrame = targetPotential⁻¹ * targetFrame := by
  rw [hframe, htransition]
  simp [transitionFromPotentials, mul_assoc]

/-- 若同一条边分别被一对 potential 和一对 frame 换基为单位元，则两端的右余规范相等。

> **Entry**: topology.fundamental-group.van-kampen-residual-gauge
@isnad1 id=eq.2h6v.s6.199f08843351 from=translated src=- shape=661b18fb vocab=4a305f90
-/
theorem potentialNormalizedFrame_eq_of_two_rebases
    {G : Type*} [Group G]
    (sourcePotential targetPotential sourceFrame targetFrame edge : G)
    (hpotential : rebaseEdge sourcePotential targetPotential edge = 1)
    (hframe : rebaseEdge sourceFrame targetFrame edge = 1) :
    sourcePotential⁻¹ * sourceFrame = targetPotential⁻¹ * targetFrame := by
  have hp : edge * sourcePotential = targetPotential := by
    have h := congrArg (fun z => targetPotential * z) hpotential
    simpa [rebaseEdge, mul_assoc] using h
  have hf : edge * sourceFrame = targetFrame := by
    have h := congrArg (fun z => targetFrame * z) hframe
    simpa [rebaseEdge, mul_assoc] using h
  rw [← hp, ← hf]
  simp [mul_assoc]

/-- At a boundary vertex that is literally the cover basepoint, the normalized
intersection potential is the familiar potential measured from the constant
connector.-/
private theorem BinaryOpenCoverSquareSubdivision.gridCellBasepointPotential_eq_reflPotential
    {x₀ : X} {H : C(unitInterval × unitInterval, X)} {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision H U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i j : Fin D.steps) (a b : Fin 2)
    (hvertex : D.gridCellVertexInPiece i j a b =
      binaryOpenCoverBasepoint hxU hxV (D.label i j)) :
    D.gridCellBasepointPotential hxU hxV hUV hU hV i j a b hvertex =
      Monoid.PushoutI.of
        (φ := binaryOpenCoverIntersectionMaps U V hxU hxV) (D.label i j)
        (connectorChange
          (Path.refl (binaryOpenCoverBasepoint hxU hxV (D.label i j)))
          ((D.gridCellVertexConnectorInPiece hxU hxV hU hV i j a b).cast
            rfl hvertex.symm)) := by
  let hz := D.intersectionBasepoint_eq_gridCellVertexInPiece_of_eq_basepoint
    hxU hxV i j a b hvertex
  let reference :=
    (binaryOpenCoverIntersectionConnectorInPiece hxU hxV hUV (D.label i j)
      (binaryOpenCoverIntersectionBasepoint hxU hxV)).cast
      (binaryOpenCoverBasepoint_eq_intersectionToPiece hxU hxV (D.label i j)) hz.symm
  change Monoid.PushoutI.of
      (φ := binaryOpenCoverIntersectionMaps U V hxU hxV) (D.label i j)
      (connectorChange reference
        (D.gridCellVertexConnectorInPiece hxU hxV hU hV i j a b)) = _
  apply congrArg (Monoid.PushoutI.of
    (φ := binaryOpenCoverIntersectionMaps U V hxU hxV) (D.label i j))
  rw [← connectorChange_cast reference
    (D.gridCellVertexConnectorInPiece hxU hxV hU hV i j a b) hvertex.symm]
  congr 1
  apply Path.ext
  funext u
  apply Subtype.ext
  rw [Path.cast_coe, Path.cast_coe]
  have href := congrArg (fun path : Path
      (binaryOpenCoverBasepoint hxU hxV (D.label i j))
      (binaryOpenCoverBasepoint hxU hxV (D.label i j)) =>
        ((path u : binaryOpenCoverPiece U V (D.label i j)) : X))
    (binaryOpenCoverIntersectionConnectorInPiece_basepoint
      hxU hxV hUV (D.label i j))
  rw [Path.cast_coe] at href
  exact href

/-- On the bottom boundary this normalized potential is exactly the earlier
bottom-boundary potential.-/
private theorem BinaryOpenCoverSquareSubdivision.gridCellBasepointPotential_bottom_eq
    {x₀ : X} {p q : Path x₀ x₀} (Fhom : Path.Homotopy p q)
    {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision (pathHomotopySquare Fhom) U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i : Fin D.steps) (a : Fin 2) :
    let row : Fin D.steps := ⟨0, D.steps_pos⟩
    let hvertex := D.gridCellVertexInPiece_bottom_eq_basepoint
      Fhom hxU hxV i a
    D.gridCellBasepointPotential
        hxU hxV hUV hU hV i row a 0 hvertex =
      D.gridCellBottomBoundaryPotential Fhom hxU hxV hU hV i a := by
  dsimp only
  rw [D.gridCellBasepointPotential_eq_reflPotential
    hxU hxV hUV hU hV]
  rfl

/-- The residual gauge is preserved from the left to the right corner inside
each bottom-boundary cell.-/
private theorem BinaryOpenCoverSquareSubdivision.bottomResidualGauge_inside
    {x₀ : X} {p q : Path x₀ x₀} (Fhom : Path.Homotopy p q)
    {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision (pathHomotopySquare Fhom) U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i : Fin D.steps) :
    let row : Fin D.steps := ⟨0, D.steps_pos⟩
    let hleft := D.gridCellVertexInPiece_bottom_eq_basepoint Fhom hxU hxV i 0
    let hright := D.gridCellVertexInPiece_bottom_eq_basepoint Fhom hxU hxV i 1
    let leftPotential := D.gridCellBasepointPotential
      hxU hxV hUV hU hV i row 0 0 hleft
    let rightPotential := D.gridCellBasepointPotential
      hxU hxV hUV hU hV i row 1 0 hright
    let frame := D.rightAnchoredGridRowFramesAt
      hxU hxV hUV hU hV 0 D.steps_pos i
    leftPotential⁻¹ * frame.bottomLeft =
      rightPotential⁻¹ * frame.bottomRight := by
  dsimp only
  let row : Fin D.steps := ⟨0, D.steps_pos⟩
  let hleft := D.gridCellVertexInPiece_bottom_eq_basepoint Fhom hxU hxV i 0
  let hright := D.gridCellVertexInPiece_bottom_eq_basepoint Fhom hxU hxV i 1
  let leftPotential := D.gridCellBasepointPotential
    hxU hxV hUV hU hV i row 0 0 hleft
  let rightPotential := D.gridCellBasepointPotential
    hxU hxV hUV hU hV i row 1 0 hright
  let frame := D.rightAnchoredGridRowFramesAt
    hxU hxV hUV hU hV 0 D.steps_pos i
  let edge : binaryVanKampenPushout U V hxU hxV :=
    Monoid.PushoutI.of (D.label i row)
      (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i row 0)
  have hpotential : rebaseEdge leftPotential rightPotential edge = 1 := by
    dsimp only [leftPotential, rightPotential, edge]
    rw [D.gridCellBasepointPotential_bottom_eq
        Fhom hxU hxV hUV hU hV i 0,
      D.gridCellBasepointPotential_bottom_eq
        Fhom hxU hxV hUV hU hV i 1]
    exact D.gridCellBottomEdge_rebase_eq_one Fhom hxU hxV hU hV i
  have hframe :=
    (D.rightAnchoredGridRowFramesAt_horizontal_edges
      hxU hxV hUV hU hV 0 D.steps_pos i).1
  exact potentialNormalizedFrame_eq_of_two_rebases
    leftPotential rightPotential frame.bottomLeft frame.bottomRight edge
      hpotential hframe

/-- The normalized basepoint potentials also normalize every actual top cell
edge to one.-/
private theorem BinaryOpenCoverSquareSubdivision.gridCellTopEdge_basepointPotential_rebase_eq_one
    {x₀ : X} {p q : Path x₀ x₀} (Fhom : Path.Homotopy p q)
    {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision (pathHomotopySquare Fhom) U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i : Fin D.steps) :
    let row : Fin D.steps :=
      ⟨D.steps - 1, Nat.sub_lt D.steps_pos Nat.zero_lt_one⟩
    let hstart := D.gridCellVertexInPiece_top_eq_basepoint Fhom hxU hxV i 0
    let hend := D.gridCellVertexInPiece_top_eq_basepoint Fhom hxU hxV i 1
    rebaseEdge
        (D.gridCellBasepointPotential hxU hxV hUV hU hV i row 0 1 hstart)
        (D.gridCellBasepointPotential hxU hxV hUV hU hV i row 1 1 hend)
        (Monoid.PushoutI.of (D.label i row)
          (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i row 1)) = 1 := by
  dsimp only
  let row : Fin D.steps :=
    ⟨D.steps - 1, Nat.sub_lt D.steps_pos Nat.zero_lt_one⟩
  let base := binaryOpenCoverBasepoint hxU hxV (D.label i row)
  let startConnector := D.gridCellVertexConnectorInPiece hxU hxV hU hV i row 0 1
  let endConnector := D.gridCellVertexConnectorInPiece hxU hxV hU hV i row 1 1
  let segment := ((squareGridHorizontalEdge
      (ContinuousMap.id (unitInterval × unitInterval))
      1 unitSquareOnePos 0 1).map (D.gridCellMapInPiece i row).continuous)
  let hstart := D.gridCellVertexInPiece_top_eq_basepoint Fhom hxU hxV i 0
  let hend := D.gridCellVertexInPiece_top_eq_basepoint Fhom hxU hxV i 1
  let hz : base = D.gridCellVertexInPiece i row 0 1 := hstart.symm
  let hw : base = D.gridCellVertexInPiece i row 1 1 := hend.symm
  have hbase : ((base : binaryOpenCoverPiece U V (D.label i row)) : X) = x₀ := by
    exact coe_binaryOpenCoverBasepoint_for_residualGauge hxU hxV (D.label i row)
  have hsegment : segment.cast hz hw = Path.refl base := by
    apply Path.ext
    funext t
    apply Subtype.ext
    rw [Path.cast_coe]
    dsimp only [segment, base]
    rw [D.coe_gridCellTopEdge_eq Fhom i t]
    exact hbase.symm
  rw [D.gridCellBasepointPotential_eq_reflPotential
      hxU hxV hUV hU hV i row 0 1 hstart,
    D.gridCellBasepointPotential_eq_reflPotential
      hxU hxV hUV hU hV i row 1 1 hend]
  change rebaseEdge
      (Monoid.PushoutI.of
        (φ := binaryOpenCoverIntersectionMaps U V hxU hxV) (D.label i row)
        (connectorChange (Path.refl base) (startConnector.cast rfl hz)))
      (Monoid.PushoutI.of
        (φ := binaryOpenCoverIntersectionMaps U V hxU hxV) (D.label i row)
        (connectorChange (Path.refl base) (endConnector.cast rfl hw)))
      (Monoid.PushoutI.of
        (φ := binaryOpenCoverIntersectionMaps U V hxU hxV) (D.label i row)
        (FundamentalGroup.fromPath
          ⟦Path.correctedLoop startConnector segment endConnector⟧)) = 1
  exact map_rebase_correctedLoop_eq_one_of_cast_eq_refl
    (Monoid.PushoutI.of
      (φ := binaryOpenCoverIntersectionMaps U V hxU hxV) (D.label i row))
      (Path.refl base) startConnector segment endConnector hz hw hsegment

/-- The residual gauge is preserved from the left to the right corner inside
each top-boundary cell.-/
private theorem BinaryOpenCoverSquareSubdivision.topResidualGauge_inside
    {x₀ : X} {p q : Path x₀ x₀} (Fhom : Path.Homotopy p q)
    {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision (pathHomotopySquare Fhom) U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i : Fin D.steps) :
    let row : Fin D.steps :=
      ⟨D.steps - 1, Nat.sub_lt D.steps_pos Nat.zero_lt_one⟩
    let hleft := D.gridCellVertexInPiece_top_eq_basepoint Fhom hxU hxV i 0
    let hright := D.gridCellVertexInPiece_top_eq_basepoint Fhom hxU hxV i 1
    let leftPotential := D.gridCellBasepointPotential
      hxU hxV hUV hU hV i row 0 1 hleft
    let rightPotential := D.gridCellBasepointPotential
      hxU hxV hUV hU hV i row 1 1 hright
    let frame := D.rightAnchoredGridRowFramesAt
      hxU hxV hUV hU hV row.val row.isLt i
    leftPotential⁻¹ * frame.topLeft =
      rightPotential⁻¹ * frame.topRight := by
  dsimp only
  let row : Fin D.steps :=
    ⟨D.steps - 1, Nat.sub_lt D.steps_pos Nat.zero_lt_one⟩
  let hleft := D.gridCellVertexInPiece_top_eq_basepoint Fhom hxU hxV i 0
  let hright := D.gridCellVertexInPiece_top_eq_basepoint Fhom hxU hxV i 1
  let leftPotential := D.gridCellBasepointPotential
    hxU hxV hUV hU hV i row 0 1 hleft
  let rightPotential := D.gridCellBasepointPotential
    hxU hxV hUV hU hV i row 1 1 hright
  let frame := D.rightAnchoredGridRowFramesAt
    hxU hxV hUV hU hV row.val row.isLt i
  let edge : binaryVanKampenPushout U V hxU hxV :=
    Monoid.PushoutI.of (D.label i row)
      (D.gridCellBasedHorizontalEdgeInPiece hxU hxV hU hV i row 1)
  have hpotential : rebaseEdge leftPotential rightPotential edge = 1 := by
    exact D.gridCellTopEdge_basepointPotential_rebase_eq_one
      Fhom hxU hxV hUV hU hV i
  have hframe :=
    (D.rightAnchoredGridRowFramesAt_horizontal_edges
      hxU hxV hUV hU hV row.val row.isLt i).2
  exact potentialNormalizedFrame_eq_of_two_rebases
    leftPotential rightPotential frame.topLeft frame.topRight edge
      hpotential hframe

/-- The normalized basepoint potentials normalize every actual right cell edge
to one.-/
private theorem BinaryOpenCoverSquareSubdivision.gridCellRightEdge_basepointPotential_rebase_eq_one
    {x₀ : X} {p : Path x₀ x₀}
    (Fhom : Path.Homotopy p (Path.refl x₀)) {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision (pathHomotopySquare Fhom) U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (j : Fin D.steps) :
    let col : Fin D.steps :=
      ⟨D.steps - 1, Nat.sub_lt D.steps_pos Nat.zero_lt_one⟩
    let hstart := D.gridCellVertexInPiece_right_eq_basepoint Fhom hxU hxV j 0
    let hend := D.gridCellVertexInPiece_right_eq_basepoint Fhom hxU hxV j 1
    rebaseEdge
        (D.gridCellBasepointPotential hxU hxV hUV hU hV col j 1 0 hstart)
        (D.gridCellBasepointPotential hxU hxV hUV hU hV col j 1 1 hend)
        (Monoid.PushoutI.of (D.label col j)
          (D.gridCellBasedVerticalEdgeInPiece hxU hxV hU hV col j 1)) = 1 := by
  dsimp only
  let col : Fin D.steps :=
    ⟨D.steps - 1, Nat.sub_lt D.steps_pos Nat.zero_lt_one⟩
  let base := binaryOpenCoverBasepoint hxU hxV (D.label col j)
  let startConnector := D.gridCellVertexConnectorInPiece hxU hxV hU hV col j 1 0
  let endConnector := D.gridCellVertexConnectorInPiece hxU hxV hU hV col j 1 1
  let segment := ((squareGridVerticalEdge
      (ContinuousMap.id (unitInterval × unitInterval))
      1 unitSquareOnePos 1 0).map (D.gridCellMapInPiece col j).continuous)
  let hstart := D.gridCellVertexInPiece_right_eq_basepoint Fhom hxU hxV j 0
  let hend := D.gridCellVertexInPiece_right_eq_basepoint Fhom hxU hxV j 1
  let hz : base = D.gridCellVertexInPiece col j 1 0 := hstart.symm
  let hw : base = D.gridCellVertexInPiece col j 1 1 := hend.symm
  have hbase : ((base : binaryOpenCoverPiece U V (D.label col j)) : X) = x₀ := by
    exact coe_binaryOpenCoverBasepoint_for_residualGauge hxU hxV (D.label col j)
  have hsegment : segment.cast hz hw = Path.refl base := by
    apply Path.ext
    funext t
    apply Subtype.ext
    rw [Path.cast_coe]
    dsimp only [segment, base]
    rw [D.coe_gridCellRightEdge_eq Fhom j t]
    exact hbase.symm
  rw [D.gridCellBasepointPotential_eq_reflPotential
      hxU hxV hUV hU hV col j 1 0 hstart,
    D.gridCellBasepointPotential_eq_reflPotential
      hxU hxV hUV hU hV col j 1 1 hend]
  change rebaseEdge
      (Monoid.PushoutI.of
        (φ := binaryOpenCoverIntersectionMaps U V hxU hxV) (D.label col j)
        (connectorChange (Path.refl base) (startConnector.cast rfl hz)))
      (Monoid.PushoutI.of
        (φ := binaryOpenCoverIntersectionMaps U V hxU hxV) (D.label col j)
        (connectorChange (Path.refl base) (endConnector.cast rfl hw)))
      (Monoid.PushoutI.of
        (φ := binaryOpenCoverIntersectionMaps U V hxU hxV) (D.label col j)
        (FundamentalGroup.fromPath
          ⟦Path.correctedLoop startConnector segment endConnector⟧)) = 1
  exact map_rebase_correctedLoop_eq_one_of_cast_eq_refl
    (Monoid.PushoutI.of
      (φ := binaryOpenCoverIntersectionMaps U V hxU hxV) (D.label col j))
      (Path.refl base) startConnector segment endConnector hz hw hsegment

/-- The residual gauge is preserved inside every right-boundary cell.-/
private theorem BinaryOpenCoverSquareSubdivision.rightResidualGauge_inside
    {x₀ : X} {p : Path x₀ x₀}
    (Fhom : Path.Homotopy p (Path.refl x₀)) {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision (pathHomotopySquare Fhom) U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (r : ℕ) (hr : r < D.steps) :
    let col : Fin D.steps :=
      ⟨D.steps - 1, Nat.sub_lt D.steps_pos Nat.zero_lt_one⟩
    let row : Fin D.steps := ⟨r, hr⟩
    let hbottom := D.gridCellVertexInPiece_right_eq_basepoint Fhom hxU hxV row 0
    let htop := D.gridCellVertexInPiece_right_eq_basepoint Fhom hxU hxV row 1
    let bottomPotential := D.gridCellBasepointPotential
      hxU hxV hUV hU hV col row 1 0 hbottom
    let topPotential := D.gridCellBasepointPotential
      hxU hxV hUV hU hV col row 1 1 htop
    let frame := D.rightAnchoredGridRowFramesAt hxU hxV hUV hU hV r hr col
    bottomPotential⁻¹ * frame.bottomRight =
      topPotential⁻¹ * frame.topRight := by
  dsimp only
  let col : Fin D.steps :=
    ⟨D.steps - 1, Nat.sub_lt D.steps_pos Nat.zero_lt_one⟩
  let row : Fin D.steps := ⟨r, hr⟩
  let hbottom := D.gridCellVertexInPiece_right_eq_basepoint Fhom hxU hxV row 0
  let htop := D.gridCellVertexInPiece_right_eq_basepoint Fhom hxU hxV row 1
  let bottomPotential := D.gridCellBasepointPotential
    hxU hxV hUV hU hV col row 1 0 hbottom
  let topPotential := D.gridCellBasepointPotential
    hxU hxV hUV hU hV col row 1 1 htop
  let frame := D.rightAnchoredGridRowFramesAt hxU hxV hUV hU hV r hr col
  let edge : binaryVanKampenPushout U V hxU hxV :=
    Monoid.PushoutI.of (D.label col row)
      (D.gridCellBasedVerticalEdgeInPiece hxU hxV hU hV col row 1)
  have hpotential : rebaseEdge bottomPotential topPotential edge = 1 :=
    D.gridCellRightEdge_basepointPotential_rebase_eq_one
      Fhom hxU hxV hUV hU hV row
  have hframe := D.rightAnchoredGridRowFramesAt_right_edge_eq_one
    hxU hxV hUV hU hV r hr
  exact potentialNormalizedFrame_eq_of_two_rebases
    bottomPotential topPotential frame.bottomRight frame.topRight edge
      hpotential hframe

/-- Rewriting a cell-to-target transition by vertex potentials exposes a
common target potential multiplied by the cell's residual right gauge.-/
private theorem transitionFromPotentials_mul_frame
    {G : Type*} [Group G]
    (cellPotential targetPotential frame : G) :
    transitionFromPotentials cellPotential targetPotential * frame =
      targetPotential * (cellPotential⁻¹ * frame) := by
  simp [transitionFromPotentials, mul_assoc]

/-- 若目标 potential 相等，且按 cell potential 归一化后的 frame 相等，则两组 combined frame 相等。

> **Entry**: topology.fundamental-group.van-kampen-residual-gauge
@isnad1 id=eq.2h7v.s7.7e3e3c3b8c61 from=translated src=- shape=5cf3c43b vocab=ed901023
-/
theorem combinedFrame_eq_of_target_and_normalized
    {G : Type*} [Group G]
    (cellPotential₁ cellPotential₂ targetPotential₁ targetPotential₂
      frame₁ frame₂ : G)
    (htarget : targetPotential₁ = targetPotential₂)
    (hnormalized : cellPotential₁⁻¹ * frame₁ =
      cellPotential₂⁻¹ * frame₂) :
    transitionFromPotentials cellPotential₁ targetPotential₁ * frame₁ =
      transitionFromPotentials cellPotential₂ targetPotential₂ * frame₂ := by
  rw [transitionFromPotentials_mul_frame,
    transitionFromPotentials_mul_frame, htarget, hnormalized]

/-- Bottom-vertex specialization of residual-gauge propagation across two
horizontally adjacent cells.-/
private theorem HorizontalCellFramesCompatible.potentialNormalized_bottom
    {G : Type*} [Group G] {T : EdgeTransitions G}
    {left right : CellVertexFrames G}
    (hframes : HorizontalCellFramesCompatible T left right)
    (leftPotential rightPotential : G)
    (htransition : T.startChange =
      transitionFromPotentials leftPotential rightPotential) :
    leftPotential⁻¹ * left.bottomRight =
      rightPotential⁻¹ * right.bottomLeft := by
  exact potentialNormalizedFrame_eq_of_compatible
    leftPotential rightPotential left.bottomRight right.bottomLeft
      T.startChange htransition hframes.bottom

/-- Top-vertex specialization of residual-gauge propagation across two
horizontally adjacent cells.-/
private theorem HorizontalCellFramesCompatible.potentialNormalized_top
    {G : Type*} [Group G] {T : EdgeTransitions G}
    {left right : CellVertexFrames G}
    (hframes : HorizontalCellFramesCompatible T left right)
    (leftPotential rightPotential : G)
    (htransition : T.endChange =
      transitionFromPotentials leftPotential rightPotential) :
    leftPotential⁻¹ * left.topRight =
      rightPotential⁻¹ * right.topLeft := by
  exact potentialNormalizedFrame_eq_of_compatible
    leftPotential rightPotential left.topRight right.topLeft
      T.endChange htransition hframes.top

/-- Right-vertex specialization of residual-gauge propagation across two
vertically adjacent cells.-/
private theorem VerticalCellFramesCompatible.potentialNormalized_right
    {G : Type*} [Group G] {T : EdgeTransitions G}
    {lower upper : CellVertexFrames G}
    (hframes : VerticalCellFramesCompatible T lower upper)
    (lowerPotential upperPotential : G)
    (htransition : T.endChange =
      transitionFromPotentials lowerPotential upperPotential) :
    lowerPotential⁻¹ * lower.topRight =
      upperPotential⁻¹ * upper.bottomRight := by
  exact potentialNormalizedFrame_eq_of_compatible
    lowerPotential upperPotential lower.topRight upper.bottomRight
      T.endChange htransition hframes.right

/-- Along the bottom boundary of a path-homotopy square, the residual gauge is
preserved across each pair of horizontally adjacent cells.-/
private theorem BinaryOpenCoverSquareSubdivision.bottomResidualGauge_adjacent
    {x₀ : X} {p q : Path x₀ x₀} (Fhom : Path.Homotopy p q)
    {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision (pathHomotopySquare Fhom) U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k : Fin D.steps) (hshared : i.succ = k.castSucc) :
    let row : Fin D.steps := ⟨0, D.steps_pos⟩
    let leftVertex := D.gridCellVertexInPiece_bottom_eq_basepoint
      Fhom hxU hxV i 1
    let rightVertex := D.gridCellVertexInPiece_bottom_eq_basepoint
      Fhom hxU hxV k 0
    let leftPotential := D.gridCellBasepointPotential
      hxU hxV hUV hU hV i row 1 0 leftVertex
    let rightPotential := D.gridCellBasepointPotential
      hxU hxV hUV hU hV k row 0 0 rightVertex
    let leftFrame := D.rightAnchoredGridRowFramesAt
      hxU hxV hUV hU hV 0 D.steps_pos i
    let rightFrame := D.rightAnchoredGridRowFramesAt
      hxU hxV hUV hU hV 0 D.steps_pos k
    leftPotential⁻¹ * leftFrame.bottomRight =
      rightPotential⁻¹ * rightFrame.bottomLeft := by
  dsimp only
  let row : Fin D.steps := ⟨0, D.steps_pos⟩
  let leftVertex := D.gridCellVertexInPiece_bottom_eq_basepoint
    Fhom hxU hxV i 1
  let rightVertex := D.gridCellVertexInPiece_bottom_eq_basepoint
    Fhom hxU hxV k 0
  let leftPotential := D.gridCellBasepointPotential
    hxU hxV hUV hU hV i row 1 0 leftVertex
  let rightPotential := D.gridCellBasepointPotential
    hxU hxV hUV hU hV k row 0 0 rightVertex
  let T := D.horizontalInternalEdgeTransitions
    hxU hxV hUV hU hV i k row hshared
  let leftFrame := D.rightAnchoredGridRowFramesAt
    hxU hxV hUV hU hV 0 D.steps_pos i
  let rightFrame := D.rightAnchoredGridRowFramesAt
    hxU hxV hUV hU hV 0 D.steps_pos k
  have htransition : T.startChange =
      transitionFromPotentials leftPotential rightPotential := by
    exact D.horizontalInternalEdgeTransitions_start_eq_gridCellPotentials
      hxU hxV hUV hU hV i k row hshared
      (binaryOpenCoverIntersectionBasepoint hxU hxV)
      (D.intersectionBasepoint_eq_gridCellVertexInPiece_of_eq_basepoint
        hxU hxV i row 1 0 leftVertex)
      (D.intersectionBasepoint_eq_gridCellVertexInPiece_of_eq_basepoint
        hxU hxV k row 0 0 rightVertex)
  have hframes := D.rightAnchoredGridRowFramesAt_compatible
    hxU hxV hUV hU hV 0 D.steps_pos i k hshared
  exact hframes.potentialNormalized_bottom
    leftPotential rightPotential htransition

/-- The corresponding residual gauge is preserved across horizontally
adjacent cells on the top boundary.-/
private theorem BinaryOpenCoverSquareSubdivision.topResidualGauge_adjacent
    {x₀ : X} {p q : Path x₀ x₀} (Fhom : Path.Homotopy p q)
    {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision (pathHomotopySquare Fhom) U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (i k : Fin D.steps) (hshared : i.succ = k.castSucc) :
    let row : Fin D.steps :=
      ⟨D.steps - 1, Nat.sub_lt D.steps_pos Nat.zero_lt_one⟩
    let leftVertex := D.gridCellVertexInPiece_top_eq_basepoint
      Fhom hxU hxV i 1
    let rightVertex := D.gridCellVertexInPiece_top_eq_basepoint
      Fhom hxU hxV k 0
    let leftPotential := D.gridCellBasepointPotential
      hxU hxV hUV hU hV i row 1 1 leftVertex
    let rightPotential := D.gridCellBasepointPotential
      hxU hxV hUV hU hV k row 0 1 rightVertex
    let leftFrame := D.rightAnchoredGridRowFramesAt
      hxU hxV hUV hU hV row.val row.isLt i
    let rightFrame := D.rightAnchoredGridRowFramesAt
      hxU hxV hUV hU hV row.val row.isLt k
    leftPotential⁻¹ * leftFrame.topRight =
      rightPotential⁻¹ * rightFrame.topLeft := by
  dsimp only
  let row : Fin D.steps :=
    ⟨D.steps - 1, Nat.sub_lt D.steps_pos Nat.zero_lt_one⟩
  let leftVertex := D.gridCellVertexInPiece_top_eq_basepoint
    Fhom hxU hxV i 1
  let rightVertex := D.gridCellVertexInPiece_top_eq_basepoint
    Fhom hxU hxV k 0
  let leftPotential := D.gridCellBasepointPotential
    hxU hxV hUV hU hV i row 1 1 leftVertex
  let rightPotential := D.gridCellBasepointPotential
    hxU hxV hUV hU hV k row 0 1 rightVertex
  let T := D.horizontalInternalEdgeTransitions
    hxU hxV hUV hU hV i k row hshared
  let leftFrame := D.rightAnchoredGridRowFramesAt
    hxU hxV hUV hU hV row.val row.isLt i
  let rightFrame := D.rightAnchoredGridRowFramesAt
    hxU hxV hUV hU hV row.val row.isLt k
  have htransition : T.endChange =
      transitionFromPotentials leftPotential rightPotential := by
    exact D.horizontalInternalEdgeTransitions_end_eq_gridCellPotentials
      hxU hxV hUV hU hV i k row hshared
      (binaryOpenCoverIntersectionBasepoint hxU hxV)
      (D.intersectionBasepoint_eq_gridCellVertexInPiece_of_eq_basepoint
        hxU hxV i row 1 1 leftVertex)
      (D.intersectionBasepoint_eq_gridCellVertexInPiece_of_eq_basepoint
        hxU hxV k row 0 1 rightVertex)
  have hframes := D.rightAnchoredGridRowFramesAt_compatible
    hxU hxV hUV hU hV row.val row.isLt i k hshared
  exact hframes.potentialNormalized_top
    leftPotential rightPotential htransition

/-- Along the constant right boundary, the residual gauge is preserved from
each row to its successor.-/
private theorem BinaryOpenCoverSquareSubdivision.rightResidualGauge_succ
    {x₀ : X} {p : Path x₀ x₀}
    (Fhom : Path.Homotopy p (Path.refl x₀)) {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision (pathHomotopySquare Fhom) U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (r : ℕ) (hr : r + 1 < D.steps) :
    let col : Fin D.steps :=
      ⟨D.steps - 1, Nat.sub_lt D.steps_pos Nat.zero_lt_one⟩
    let lowerRow : Fin D.steps :=
      ⟨r, Nat.lt_trans (Nat.lt_succ_self r) hr⟩
    let upperRow : Fin D.steps := ⟨r + 1, hr⟩
    let lowerVertex := D.gridCellVertexInPiece_right_eq_basepoint
      Fhom hxU hxV lowerRow 1
    let upperVertex := D.gridCellVertexInPiece_right_eq_basepoint
      Fhom hxU hxV upperRow 0
    let lowerPotential := D.gridCellBasepointPotential
      hxU hxV hUV hU hV col lowerRow 1 1 lowerVertex
    let upperPotential := D.gridCellBasepointPotential
      hxU hxV hUV hU hV col upperRow 1 0 upperVertex
    let lowerFrame := D.rightAnchoredGridRowFramesAt
      hxU hxV hUV hU hV r (Nat.lt_trans (Nat.lt_succ_self r) hr) col
    let upperFrame := D.rightAnchoredGridRowFramesAt
      hxU hxV hUV hU hV (r + 1) hr col
    lowerPotential⁻¹ * lowerFrame.topRight =
      upperPotential⁻¹ * upperFrame.bottomRight := by
  dsimp only
  let hp : r < D.steps := Nat.lt_trans (Nat.lt_succ_self r) hr
  let col : Fin D.steps :=
    ⟨D.steps - 1, Nat.sub_lt D.steps_pos Nat.zero_lt_one⟩
  let lowerRow : Fin D.steps := ⟨r, hp⟩
  let upperRow : Fin D.steps := ⟨r + 1, hr⟩
  have hshared : lowerRow.succ = upperRow.castSucc := by
    apply Fin.ext
    rfl
  let lowerVertex := D.gridCellVertexInPiece_right_eq_basepoint
    Fhom hxU hxV lowerRow 1
  let upperVertex := D.gridCellVertexInPiece_right_eq_basepoint
    Fhom hxU hxV upperRow 0
  let lowerPotential := D.gridCellBasepointPotential
    hxU hxV hUV hU hV col lowerRow 1 1 lowerVertex
  let upperPotential := D.gridCellBasepointPotential
    hxU hxV hUV hU hV col upperRow 1 0 upperVertex
  let T := D.verticalInternalEdgeTransitions
    hxU hxV hUV hU hV col lowerRow upperRow hshared
  let lowerFrame := D.rightAnchoredGridRowFramesAt
    hxU hxV hUV hU hV r hp col
  let upperFrame := D.rightAnchoredGridRowFramesAt
    hxU hxV hUV hU hV (r + 1) hr col
  have htransition : T.endChange =
      transitionFromPotentials lowerPotential upperPotential := by
    exact D.verticalInternalEdgeTransitions_end_eq_gridCellPotentials
      hxU hxV hUV hU hV col lowerRow upperRow hshared
      (binaryOpenCoverIntersectionBasepoint hxU hxV)
      (D.intersectionBasepoint_eq_gridCellVertexInPiece_of_eq_basepoint
        hxU hxV col lowerRow 1 1 lowerVertex)
      (D.intersectionBasepoint_eq_gridCellVertexInPiece_of_eq_basepoint
        hxU hxV col upperRow 1 0 upperVertex)
  have hframes := D.rightAnchoredGridRowFramesAt_vertical_compatible
    hxU hxV hUV hU hV r hr col
  exact hframes.potentialNormalized_right
    lowerPotential upperPotential htransition

/-- A value on a nonempty finite interval that is unchanged at every successor
is equal at the first and last indices.-/
private theorem fin_zero_eq_last_of_succ
    {G : Type*} {n : ℕ} (hn : 0 < n) (value : Fin n → G)
    (hstep : ∀ (r : ℕ) (hr : r + 1 < n),
      value ⟨r, Nat.lt_trans (Nat.lt_succ_self r) hr⟩ = value ⟨r + 1, hr⟩) :
    value ⟨0, hn⟩ = value ⟨n - 1, Nat.sub_lt hn Nat.zero_lt_one⟩ := by
  have hprefix : ∀ (m : ℕ) (hm : m < n),
      value ⟨0, hn⟩ = value ⟨m, hm⟩ := by
    intro m
    induction m with
    | zero =>
        intro hm
        rfl
    | succ m ih =>
        intro hm
        exact (ih (Nat.lt_trans (Nat.lt_succ_self m) hm)).trans
          (hstep m hm)
  exact hprefix (n - 1) (Nat.sub_lt hn Nat.zero_lt_one)

/-- Alternating inside-row and between-row propagation telescopes along the
complete constant right boundary.-/
private theorem BinaryOpenCoverSquareSubdivision.rightResidualGauge_first_eq_last
    {x₀ : X} {p : Path x₀ x₀}
    (Fhom : Path.Homotopy p (Path.refl x₀)) {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision (pathHomotopySquare Fhom) U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V) :
    let col : Fin D.steps :=
      ⟨D.steps - 1, Nat.sub_lt D.steps_pos Nat.zero_lt_one⟩
    let first : Fin D.steps := ⟨0, D.steps_pos⟩
    let last : Fin D.steps :=
      ⟨D.steps - 1, Nat.sub_lt D.steps_pos Nat.zero_lt_one⟩
    let firstVertex := D.gridCellVertexInPiece_right_eq_basepoint Fhom hxU hxV first 0
    let lastVertex := D.gridCellVertexInPiece_right_eq_basepoint Fhom hxU hxV last 1
    let firstPotential := D.gridCellBasepointPotential
      hxU hxV hUV hU hV col first 1 0 firstVertex
    let lastPotential := D.gridCellBasepointPotential
      hxU hxV hUV hU hV col last 1 1 lastVertex
    let firstFrame := D.rightAnchoredGridRowFramesAt
      hxU hxV hUV hU hV 0 D.steps_pos col
    let lastFrame := D.rightAnchoredGridRowFramesAt
      hxU hxV hUV hU hV last.val last.isLt col
    firstPotential⁻¹ * firstFrame.bottomRight =
      lastPotential⁻¹ * lastFrame.topRight := by
  dsimp only
  let col : Fin D.steps :=
    ⟨D.steps - 1, Nat.sub_lt D.steps_pos Nat.zero_lt_one⟩
  let first : Fin D.steps := ⟨0, D.steps_pos⟩
  let last : Fin D.steps :=
    ⟨D.steps - 1, Nat.sub_lt D.steps_pos Nat.zero_lt_one⟩
  let bottomGauge : Fin D.steps → binaryVanKampenPushout U V hxU hxV := fun row =>
    let hvertex := D.gridCellVertexInPiece_right_eq_basepoint Fhom hxU hxV row 0
    let potential := D.gridCellBasepointPotential
      hxU hxV hUV hU hV col row 1 0 hvertex
    let frame := D.rightAnchoredGridRowFramesAt
      hxU hxV hUV hU hV row.val row.isLt col
    potential⁻¹ * frame.bottomRight
  have hstep : ∀ (r : ℕ) (hr : r + 1 < D.steps),
      bottomGauge ⟨r, Nat.lt_trans (Nat.lt_succ_self r) hr⟩ =
        bottomGauge ⟨r + 1, hr⟩ := by
    intro r hr
    exact (D.rightResidualGauge_inside Fhom hxU hxV hUV hU hV r
      (Nat.lt_trans (Nat.lt_succ_self r) hr)).trans
        (D.rightResidualGauge_succ Fhom hxU hxV hUV hU hV r hr)
  have hbottom : bottomGauge first = bottomGauge last :=
    fin_zero_eq_last_of_succ D.steps_pos bottomGauge hstep
  exact hbottom.trans
    (D.rightResidualGauge_inside Fhom hxU hxV hUV hU hV last.val last.isLt)

/-- The alternating inside-cell and between-cell propagation telescopes across
the complete bottom boundary.-/
private theorem BinaryOpenCoverSquareSubdivision.bottomResidualGauge_first_eq_last
    {x₀ : X} {p q : Path x₀ x₀} (Fhom : Path.Homotopy p q)
    {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision (pathHomotopySquare Fhom) U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V) :
    let row : Fin D.steps := ⟨0, D.steps_pos⟩
    let first : Fin D.steps := ⟨0, D.steps_pos⟩
    let last : Fin D.steps :=
      ⟨D.steps - 1, Nat.sub_lt D.steps_pos Nat.zero_lt_one⟩
    let firstVertex := D.gridCellVertexInPiece_bottom_eq_basepoint Fhom hxU hxV first 0
    let lastVertex := D.gridCellVertexInPiece_bottom_eq_basepoint Fhom hxU hxV last 1
    let firstPotential := D.gridCellBasepointPotential
      hxU hxV hUV hU hV first row 0 0 firstVertex
    let lastPotential := D.gridCellBasepointPotential
      hxU hxV hUV hU hV last row 1 0 lastVertex
    let firstFrame := D.rightAnchoredGridRowFramesAt
      hxU hxV hUV hU hV 0 D.steps_pos first
    let lastFrame := D.rightAnchoredGridRowFramesAt
      hxU hxV hUV hU hV 0 D.steps_pos last
    firstPotential⁻¹ * firstFrame.bottomLeft =
      lastPotential⁻¹ * lastFrame.bottomRight := by
  dsimp only
  let row : Fin D.steps := ⟨0, D.steps_pos⟩
  let first : Fin D.steps := ⟨0, D.steps_pos⟩
  let last : Fin D.steps :=
    ⟨D.steps - 1, Nat.sub_lt D.steps_pos Nat.zero_lt_one⟩
  let leftGauge : Fin D.steps → binaryVanKampenPushout U V hxU hxV := fun i =>
    let hvertex := D.gridCellVertexInPiece_bottom_eq_basepoint Fhom hxU hxV i 0
    let potential := D.gridCellBasepointPotential
      hxU hxV hUV hU hV i row 0 0 hvertex
    let frame := D.rightAnchoredGridRowFramesAt
      hxU hxV hUV hU hV 0 D.steps_pos i
    potential⁻¹ * frame.bottomLeft
  have hstep : ∀ (r : ℕ) (hr : r + 1 < D.steps),
      leftGauge ⟨r, Nat.lt_trans (Nat.lt_succ_self r) hr⟩ =
        leftGauge ⟨r + 1, hr⟩ := by
    intro r hr
    let i : Fin D.steps := ⟨r, Nat.lt_trans (Nat.lt_succ_self r) hr⟩
    let k : Fin D.steps := ⟨r + 1, hr⟩
    have hshared : i.succ = k.castSucc := by
      apply Fin.ext
      rfl
    exact (D.bottomResidualGauge_inside Fhom hxU hxV hUV hU hV i).trans
      (D.bottomResidualGauge_adjacent Fhom hxU hxV hUV hU hV i k hshared)
  have hleft : leftGauge first = leftGauge last :=
    fin_zero_eq_last_of_succ D.steps_pos leftGauge hstep
  exact hleft.trans
    (D.bottomResidualGauge_inside Fhom hxU hxV hUV hU hV last)

/-- The same alternating telescope crosses the complete top boundary.-/
private theorem BinaryOpenCoverSquareSubdivision.topResidualGauge_first_eq_last
    {x₀ : X} {p q : Path x₀ x₀} (Fhom : Path.Homotopy p q)
    {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision (pathHomotopySquare Fhom) U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V) :
    let row : Fin D.steps :=
      ⟨D.steps - 1, Nat.sub_lt D.steps_pos Nat.zero_lt_one⟩
    let first : Fin D.steps := ⟨0, D.steps_pos⟩
    let last : Fin D.steps :=
      ⟨D.steps - 1, Nat.sub_lt D.steps_pos Nat.zero_lt_one⟩
    let firstVertex := D.gridCellVertexInPiece_top_eq_basepoint Fhom hxU hxV first 0
    let lastVertex := D.gridCellVertexInPiece_top_eq_basepoint Fhom hxU hxV last 1
    let firstPotential := D.gridCellBasepointPotential
      hxU hxV hUV hU hV first row 0 1 firstVertex
    let lastPotential := D.gridCellBasepointPotential
      hxU hxV hUV hU hV last row 1 1 lastVertex
    let firstFrame := D.rightAnchoredGridRowFramesAt
      hxU hxV hUV hU hV row.val row.isLt first
    let lastFrame := D.rightAnchoredGridRowFramesAt
      hxU hxV hUV hU hV row.val row.isLt last
    firstPotential⁻¹ * firstFrame.topLeft =
      lastPotential⁻¹ * lastFrame.topRight := by
  dsimp only
  let row : Fin D.steps :=
    ⟨D.steps - 1, Nat.sub_lt D.steps_pos Nat.zero_lt_one⟩
  let first : Fin D.steps := ⟨0, D.steps_pos⟩
  let last : Fin D.steps :=
    ⟨D.steps - 1, Nat.sub_lt D.steps_pos Nat.zero_lt_one⟩
  let leftGauge : Fin D.steps → binaryVanKampenPushout U V hxU hxV := fun i =>
    let hvertex := D.gridCellVertexInPiece_top_eq_basepoint Fhom hxU hxV i 0
    let potential := D.gridCellBasepointPotential
      hxU hxV hUV hU hV i row 0 1 hvertex
    let frame := D.rightAnchoredGridRowFramesAt
      hxU hxV hUV hU hV row.val row.isLt i
    potential⁻¹ * frame.topLeft
  have hstep : ∀ (r : ℕ) (hr : r + 1 < D.steps),
      leftGauge ⟨r, Nat.lt_trans (Nat.lt_succ_self r) hr⟩ =
        leftGauge ⟨r + 1, hr⟩ := by
    intro r hr
    let i : Fin D.steps := ⟨r, Nat.lt_trans (Nat.lt_succ_self r) hr⟩
    let k : Fin D.steps := ⟨r + 1, hr⟩
    have hshared : i.succ = k.castSucc := by
      apply Fin.ext
      rfl
    exact (D.topResidualGauge_inside Fhom hxU hxV hUV hU hV i).trans
      (D.topResidualGauge_adjacent Fhom hxU hxV hUV hU hV i k hshared)
  have hleft : leftGauge first = leftGauge last :=
    fin_zero_eq_last_of_succ D.steps_pos leftGauge hstep
  exact hleft.trans
    (D.topResidualGauge_inside Fhom hxU hxV hUV hU hV last)

/-- 依次组合下边、右边和上边的 telescope，证明整个方形左下角与左上角的 cell 余规范相等。

> **Entry**: topology.fundamental-group.van-kampen-residual-gauge
@isnad1 id=other.5h7v.s10.daf63990adea from=translated src=- shape=934cb4a6 vocab=aa271ec8
-/
theorem BinaryOpenCoverSquareSubdivision.leftResidualGauge_bottom_eq_top
    {x₀ : X} {p : Path x₀ x₀}
    (Fhom : Path.Homotopy p (Path.refl x₀)) {U V : Set X}
    (D : BinaryOpenCoverSquareSubdivision (pathHomotopySquare Fhom) U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (hUV : IsPathConnected (U ∩ V))
    (hU : IsPathConnected U) (hV : IsPathConnected V) :
    let first : Fin D.steps := ⟨0, D.steps_pos⟩
    let last : Fin D.steps :=
      ⟨D.steps - 1, Nat.sub_lt D.steps_pos Nat.zero_lt_one⟩
    let hbottom := D.gridCellVertexInPiece_bottom_eq_basepoint Fhom hxU hxV first 0
    let htop := D.gridCellVertexInPiece_top_eq_basepoint Fhom hxU hxV first 0
    let bottomPotential := D.gridCellBasepointPotential
      hxU hxV hUV hU hV first first 0 0 hbottom
    let topPotential := D.gridCellBasepointPotential
      hxU hxV hUV hU hV first last 0 1 htop
    let bottomFrame := D.rightAnchoredGridRowFramesAt
      hxU hxV hUV hU hV 0 D.steps_pos first
    let topFrame := D.rightAnchoredGridRowFramesAt
      hxU hxV hUV hU hV last.val last.isLt first
    bottomPotential⁻¹ * bottomFrame.bottomLeft =
      topPotential⁻¹ * topFrame.topLeft := by
  dsimp only
  have hbottom := D.bottomResidualGauge_first_eq_last
    Fhom hxU hxV hUV hU hV
  have hright := D.rightResidualGauge_first_eq_last
    Fhom hxU hxV hUV hU hV
  have htop := D.topResidualGauge_first_eq_last
    Fhom hxU hxV hUV hU hV
  exact hbottom.trans (hright.trans htop.symm)

end SandronesLibrary.Topology
