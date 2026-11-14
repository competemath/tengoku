/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.CoveringSubgroupPathClassStandard
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.SemilocallySimplyConnectedStandard
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.CoveringMapStandard
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.FundamentalGroupFunctorialityStandard
import Tengoku.Seed.Topology.LocallyConstant.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 子群道路类的 canonical covering topology

给定道路连通、局部道路连通且半局部单连通的空间 `X`，以及子群
`H ≤ π₁(X, x0)`，本文件给 C5b 的子群道路类商赋予 canonical chart 生成的拓扑，
并证明终点投影是 Mathlib `IsCoveringMap`。

图的离散索引是固定终点道路类在 `H` 作用下的轨道商。这只是局部坐标后端；
最终使用 `IsEvenlyCovered.to_isEvenlyCovered_preimage` 换成投影的实际 fiber。total-space
拓扑由所有 canonical product charts 的开集生成，不是底层 quotient 的 generic quotient
topology。

当前条目：

* `topology.covering.subgroup-canonical-chart-standard`。

本文件只建立与一个子群对应的 covering projection；不证明从任意 covering 恢复子群，
不证明 pointed/unpointed 分类，也不构造 universal cover。
-/

open Set Topology

namespace SandronesLibrary.Topology

noncomputable section

universe u

variable {X : Type u} [TopologicalSpace X] (x0 : X)
variable {x0} (H : Subgroup (FundamentalGroup X x0))

namespace CoveringSubgroupCanonicalChart

theorem quotient_map_trans {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {a b c : A} (p : Path.Homotopic.Quotient a b)
    (q : Path.Homotopic.Quotient b c) (f : C(A, B)) :
    (p.trans q).map f = (p.map f).trans (q.map f) := by
  refine Quotient.inductionOn p ?_
  intro p
  refine Quotient.inductionOn q ?_
  intro q
  exact congrArg Quotient.mk'' (Path.map_trans p q f.continuous)

theorem quotient_map_symm {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {a b : A} (p : Path.Homotopic.Quotient a b) (f : C(A, B)) :
    p.symm.map f = (p.map f).symm := by
  refine Quotient.inductionOn p ?_
  intro p
  exact congrArg Quotient.mk'' (Path.map_symm p f.continuous).symm

theorem quotient_symm_trans {A : Type*} [TopologicalSpace A]
    {a b c : A} (p : Path.Homotopic.Quotient a b)
    (q : Path.Homotopic.Quotient b c) :
    (p.trans q).symm = q.symm.trans p.symm := by
  refine Quotient.inductionOn p ?_
  intro p
  refine Quotient.inductionOn q ?_
  intro q
  exact congrArg Quotient.mk'' (Path.trans_symm p q)

/-- Fixed-endpoint presentation of a fiber before comparing it with the actual projection fiber.-/
def FixedRelated (y : X) (a b : Path.Homotopic.Quotient x0 y) : Prop :=
  ∃ h : H, h.1.trans a = b

theorem fixedRelated_refl (y : X) (a : Path.Homotopic.Quotient x0 y) :
    FixedRelated H y a a := by
  refine ⟨1, ?_⟩
  change (Path.Homotopic.Quotient.refl x0).trans a = a
  exact Path.Homotopic.Quotient.refl_trans a

theorem fixedRelated_symm (y : X) {a b : Path.Homotopic.Quotient x0 y} :
    FixedRelated H y a b → FixedRelated H y b a := by
  rintro ⟨h, rfl⟩
  refine ⟨h⁻¹, ?_⟩
  change h.1.symm.trans (h.1.trans a) = a
  rw [← Path.Homotopic.Quotient.trans_assoc,
    Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.refl_trans]

theorem fixedRelated_trans (y : X) {a b c : Path.Homotopic.Quotient x0 y} :
    FixedRelated H y a b → FixedRelated H y b c → FixedRelated H y a c := by
  rintro ⟨h, rfl⟩ ⟨k, rfl⟩
  refine ⟨h * k, ?_⟩
  change (k.1.trans h.1).trans a = k.1.trans (h.1.trans a)
  exact Path.Homotopic.Quotient.trans_assoc k.1 h.1 a

def fixedSetoid (y : X) : Setoid (Path.Homotopic.Quotient x0 y) where
  r := FixedRelated H y
  iseqv := ⟨fixedRelated_refl H y, fixedRelated_symm H y, fixedRelated_trans H y⟩

/-- Fixed-endpoint path classes, used as chart indices before identifying the actual fiber.-/
abbrev FixedPathClass (y : X) := Quotient (fixedSetoid H y)

/-- An open path-connected neighborhood whose based loops die in `X`.-/
structure SmallNeighborhood (y : X) where
  carrier : Set X
  center_mem : y ∈ carrier
  isOpen : IsOpen carrier
  isPathConnected : IsPathConnected carrier
  loops_trivial :
    ∀ q : FundamentalGroup carrier ⟨y, center_mem⟩,
      FundamentalGroup.map
        (⟨Subtype.val, continuous_subtype_val⟩ : C(carrier, X))
        ⟨y, center_mem⟩ q = 1

namespace SmallNeighborhood

variable {H} {y : X} (U : SmallNeighborhood y)

/-- A chosen path inside `U` from its center to each point.-/
noncomputable def localPath (z : U.carrier) :
    Path (⟨y, U.center_mem⟩ : U.carrier) z := by
  exact (U.isPathConnected.joinedIn y U.center_mem z z.2).joined_subtype.somePath

/-- The chosen local path, mapped back to `X` and passed to the homotopy quotient.-/
noncomputable def localPathClass (z : U.carrier) :
    Path.Homotopic.Quotient y z.1 :=
  Path.Homotopic.Quotient.map
    (Path.Homotopic.Quotient.mk (U.localPath z))
    (⟨Subtype.val, continuous_subtype_val⟩ : C(U.carrier, X))

/-- A path inside `U`, viewed as a path-homotopy class in the ambient space.-/
noncomputable def localSegmentClass {a b : U.carrier} (delta : Path a b) :
    Path.Homotopic.Quotient a.1 b.1 :=
  Path.Homotopic.Quotient.map
    (Path.Homotopic.Quotient.mk delta)
    (⟨Subtype.val, continuous_subtype_val⟩ : C(U.carrier, X))

/-- Chosen center paths are coherent with every path lying in the admissible neighborhood.-/
theorem localPathClass_trans_localSegmentClass {a b : U.carrier} (delta : Path a b) :
    (U.localPathClass a).trans (U.localSegmentClass delta) = U.localPathClass b := by
  let iUX : C(U.carrier, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let pa : Path.Homotopic.Quotient (⟨y, U.center_mem⟩ : U.carrier) a :=
    Path.Homotopic.Quotient.mk (U.localPath a)
  let pd : Path.Homotopic.Quotient a b := Path.Homotopic.Quotient.mk delta
  let pb : Path.Homotopic.Quotient (⟨y, U.center_mem⟩ : U.carrier) b :=
    Path.Homotopic.Quotient.mk (U.localPath b)
  let loop : FundamentalGroup U.carrier ⟨y, U.center_mem⟩ :=
    FundamentalGroup.fromPath ((pa.trans pd).trans pb.symm)
  have hloop := U.loops_trivial loop
  change (((pa.trans pd).trans pb.symm).map iUX) =
    Path.Homotopic.Quotient.refl y at hloop
  rw [quotient_map_trans, quotient_map_trans, quotient_map_symm] at hloop
  change (pa.map iUX).trans (pd.map iUX) = pb.map iUX
  calc
    (pa.map iUX).trans (pd.map iUX) =
        ((pa.map iUX).trans (pd.map iUX)).trans
          (Path.Homotopic.Quotient.refl (iUX b)) :=
      (Path.Homotopic.Quotient.trans_refl _).symm
    _ = ((pa.map iUX).trans (pd.map iUX)).trans
        ((pb.map iUX).symm.trans (pb.map iUX)) := by
      rw [Path.Homotopic.Quotient.symm_trans]
    _ = (((pa.map iUX).trans (pd.map iUX)).trans (pb.map iUX).symm).trans
        (pb.map iUX) :=
      (Path.Homotopic.Quotient.trans_assoc _ _ _).symm
    _ = (Path.Homotopic.Quotient.refl y).trans (pb.map iUX) := by rw [hloop]
    _ = pb.map iUX := Path.Homotopic.Quotient.refl_trans _

end SmallNeighborhood

/-- Extend a varying-endpoint based path by a path starting at its endpoint.-/
def append {z : X} (a : CoveringSubgroupBasedPath x0)
    (delta : Path.Homotopic.Quotient a.endpoint z) : CoveringSubgroupBasedPath x0 where
  endpoint := z
  path := a.path.trans delta

theorem related_append {z : X} {a b : CoveringSubgroupBasedPath x0}
    (hab : CoveringSubgroupBasedPath.Related H a b)
    (delta : Path.Homotopic.Quotient a.endpoint z) :
    CoveringSubgroupBasedPath.Related H
      (append a delta)
      (append b
        (delta.cast (CoveringSubgroupBasedPath.endpoint_eq_of_related H hab).symm rfl)) := by
  obtain ⟨h, rfl⟩ := hab
  refine ⟨h, ?_⟩
  unfold append CoveringSubgroupBasedPath.prepend
  congr 1
  simp only [Path.Homotopic.Quotient.cast_rfl_rfl]
  exact (Path.Homotopic.Quotient.trans_assoc h.1 a.path delta).symm

/-- The preimage of a base set under the endpoint projection.-/
abbrev ProjectionPreimage (U : Set X) :=
  {q : CoveringSubgroupPathClass x0 H // CoveringSubgroupPathClass.projection H q ∈ U}

/-- Set-level inverse chart: extend a fixed-endpoint class along the chosen local path.-/
noncomputable def chartInv {y : X} (U : SmallNeighborhood y) :
    U.carrier × FixedPathClass H y → ProjectionPreimage H U.carrier := by
  rintro ⟨z, q⟩
  refine Quotient.lift (fun alpha => ?_) (fun a b hab => ?_) q
  · refine ⟨Quotient.mk _
      ({ endpoint := z.1, path := alpha.trans (U.localPathClass z) } :
        CoveringSubgroupBasedPath x0), ?_⟩
    exact z.2
  · apply Subtype.ext
    apply Quotient.sound
    change CoveringSubgroupBasedPath.Related H
      ({ endpoint := z.1, path := a.trans (U.localPathClass z) } :
        CoveringSubgroupBasedPath x0)
      ({ endpoint := z.1, path := b.trans (U.localPathClass z) } :
        CoveringSubgroupBasedPath x0)
    rcases hab with ⟨h, rfl⟩
    refine ⟨h, ?_⟩
    unfold CoveringSubgroupBasedPath.prepend
    congr 1
    exact (Path.Homotopic.Quotient.trans_assoc h.1 a (U.localPathClass z)).symm

/-- Totalized forward chart used to descend through the quotient; outside `U` it takes a harmless
fallback value that is discarded after restricting to `ProjectionPreimage`.-/
noncomputable def chartToRepresentative [PathConnectedSpace X] {y : X}
    (U : SmallNeighborhood y) (z : X) (alpha : Path.Homotopic.Quotient x0 z) :
    X × FixedPathClass H y := by
  classical
  exact if hz : z ∈ U.carrier then
      (z, Quotient.mk _ (alpha.trans (U.localPathClass ⟨z, hz⟩).symm))
    else
      (y, Quotient.mk _
        (Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x0 y)))

theorem chartToRepresentative_prepend [PathConnectedSpace X] {y z : X}
    (U : SmallNeighborhood y) (h : H) (alpha : Path.Homotopic.Quotient x0 z) :
    chartToRepresentative H U z (h.1.trans alpha) =
      chartToRepresentative H U z alpha := by
  classical
  unfold chartToRepresentative
  by_cases hz : z ∈ U.carrier
  · rw [dite_eq_left hz, dite_eq_left hz]
    apply Prod.ext
    · rfl
    apply Quotient.sound
    change FixedRelated H y
      ((h.1.trans alpha).trans (U.localPathClass ⟨z, hz⟩).symm)
      (alpha.trans (U.localPathClass ⟨z, hz⟩).symm)
    refine ⟨h⁻¹, ?_⟩
    change h.1.symm.trans
      ((h.1.trans alpha).trans (U.localPathClass ⟨z, hz⟩).symm) =
      alpha.trans (U.localPathClass ⟨z, hz⟩).symm
    rw [← Path.Homotopic.Quotient.trans_assoc,
      ← Path.Homotopic.Quotient.trans_assoc,
      Path.Homotopic.Quotient.symm_trans,
      Path.Homotopic.Quotient.refl_trans]
  · rw [dite_eq_right hz, dite_eq_right hz]

noncomputable def chartToRaw [PathConnectedSpace X] {y : X} (U : SmallNeighborhood y) :
    CoveringSubgroupPathClass x0 H → X × FixedPathClass H y := by
  refine Quotient.lift
    (fun a => chartToRepresentative H U a.endpoint a.path) ?_
  intro a b hab
  obtain ⟨h, rfl⟩ := hab
  simpa [CoveringSubgroupBasedPath.prepend] using
    (chartToRepresentative_prepend H U h a.path).symm

theorem chartToRaw_fst_of_mem [PathConnectedSpace X] {y : X} (U : SmallNeighborhood y)
    (q : CoveringSubgroupPathClass x0 H)
    (hq : CoveringSubgroupPathClass.projection H q ∈ U.carrier) :
    (chartToRaw H U q).1 = CoveringSubgroupPathClass.projection H q := by
  refine Quotient.inductionOn q ?_ hq
  intro a ha
  simp only [CoveringSubgroupPathClass.projection, Quotient.lift_mk] at ha ⊢
  simp only [chartToRaw, Quotient.lift_mk]
  unfold chartToRepresentative
  rw [dite_eq_left ha]

/-- Set-level forward chart using the reversed chosen local path.-/
noncomputable def chartTo [PathConnectedSpace X] {y : X} (U : SmallNeighborhood y) :
    ProjectionPreimage H U.carrier → U.carrier × FixedPathClass H y := by
  intro q
  let c := chartToRaw H U q.1
  refine ⟨⟨c.1, ?_⟩, c.2⟩
  rw [chartToRaw_fst_of_mem H U q.1 q.2]
  exact q.2

theorem chartTo_fst [PathConnectedSpace X] {y : X} (U : SmallNeighborhood y)
    (q : ProjectionPreimage H U.carrier) :
    (chartTo H U q).1.1 = CoveringSubgroupPathClass.projection H q.1 := by
  unfold chartTo
  exact chartToRaw_fst_of_mem H U q.1 q.2

theorem chartInv_mk {y : X} (U : SmallNeighborhood y) (z : U.carrier)
    (alpha : Path.Homotopic.Quotient x0 y) :
    chartInv H U (z, Quotient.mk _ alpha) =
      ⟨Quotient.mk _
        ({ endpoint := z.1, path := alpha.trans (U.localPathClass z) } :
          CoveringSubgroupBasedPath x0), z.2⟩ := by
  rfl

theorem chartToRaw_mk [PathConnectedSpace X] {y : X} (U : SmallNeighborhood y)
    (a : CoveringSubgroupBasedPath x0) :
    chartToRaw H U (Quotient.mk _ a) =
      chartToRepresentative H U a.endpoint a.path := by
  rfl

theorem chartTo_mk [PathConnectedSpace X] {y : X} (U : SmallNeighborhood y)
    (a : CoveringSubgroupBasedPath x0)
    (ha : CoveringSubgroupPathClass.projection H (Quotient.mk _ a) ∈ U.carrier) :
    chartTo H U ⟨Quotient.mk _ a, ha⟩ =
      (⟨a.endpoint, ha⟩,
        Quotient.mk _
          (a.path.trans (U.localPathClass ⟨a.endpoint, ha⟩).symm)) := by
  have ha' : a.endpoint ∈ U.carrier := by exact ha
  unfold chartTo
  apply Prod.ext
  · apply Subtype.ext
    exact chartToRaw_fst_of_mem H U (Quotient.mk _ a) ha
  · change (chartToRaw H U (Quotient.mk _ a)).2 = _
    rw [chartToRaw_mk]
    unfold chartToRepresentative
    rw [dite_eq_left ha']

theorem chartTo_chartInv_mk [PathConnectedSpace X] {y : X}
    (U : SmallNeighborhood y) (z : U.carrier)
    (alpha : Path.Homotopic.Quotient x0 y) :
    chartTo H U (chartInv H U (z, Quotient.mk _ alpha)) =
      (z, Quotient.mk _ alpha) := by
  rw [chartInv_mk]
  let a : CoveringSubgroupBasedPath x0 :=
    { endpoint := z.1, path := alpha.trans (U.localPathClass z) }
  have ha : CoveringSubgroupPathClass.projection H
      (Quotient.mk _ a : CoveringSubgroupPathClass x0 H) ∈ U.carrier := z.2
  change chartTo H U
    (⟨(Quotient.mk _ a : CoveringSubgroupPathClass x0 H), ha⟩ :
      ProjectionPreimage H U.carrier) = (z, Quotient.mk _ alpha)
  unfold chartTo
  apply Prod.ext
  · apply Subtype.ext
    exact chartToRaw_fst_of_mem H U (Quotient.mk _ a) ha
  · change (chartToRaw H U (Quotient.mk _ a : CoveringSubgroupPathClass x0 H)).2 = _
    rw [chartToRaw_mk]
    unfold chartToRepresentative
    rw [dite_eq_left z.2]
    apply Quotient.sound
    change FixedRelated H y
      ((alpha.trans (U.localPathClass z)).trans (U.localPathClass z).symm)
      alpha
    refine ⟨1, ?_⟩
    change (Path.Homotopic.Quotient.refl x0).trans
      ((alpha.trans (U.localPathClass z)).trans (U.localPathClass z).symm) = alpha
    rw [Path.Homotopic.Quotient.refl_trans,
      Path.Homotopic.Quotient.trans_assoc,
      Path.Homotopic.Quotient.trans_symm,
      Path.Homotopic.Quotient.trans_refl]

theorem chartTo_chartInv [PathConnectedSpace X] {y : X} (U : SmallNeighborhood y)
    (q : U.carrier × FixedPathClass H y) :
    chartTo H U (chartInv H U q) = q := by
  rcases q with ⟨z, q⟩
  refine Quotient.inductionOn q ?_
  intro alpha
  exact chartTo_chartInv_mk H U z alpha

theorem chartInv_chartTo [PathConnectedSpace X] {y : X} (U : SmallNeighborhood y)
    (q : ProjectionPreimage H U.carrier) :
    chartInv H U (chartTo H U q) = q := by
  rcases q with ⟨q, hq⟩
  refine Quotient.inductionOn q ?_ hq
  intro a ha
  rw [chartTo_mk, chartInv_mk]
  apply Subtype.ext
  apply Quotient.sound
  change CoveringSubgroupBasedPath.Related H
    ({ endpoint := a.endpoint,
       path := (a.path.trans (U.localPathClass ⟨a.endpoint, ha⟩).symm).trans
         (U.localPathClass ⟨a.endpoint, ha⟩) } : CoveringSubgroupBasedPath x0)
    a
  refine ⟨1, ?_⟩
  unfold CoveringSubgroupBasedPath.prepend
  congr 1
  change (Path.Homotopic.Quotient.refl x0).trans
    ((a.path.trans (U.localPathClass ⟨a.endpoint, ha⟩).symm).trans
      (U.localPathClass ⟨a.endpoint, ha⟩)) = a.path
  rw [Path.Homotopic.Quotient.refl_trans,
    Path.Homotopic.Quotient.trans_assoc,
    Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.trans_refl]

/-- Canonical set equivalence over one admissible small neighborhood.-/
noncomputable def chartEquiv [PathConnectedSpace X] {y : X} (U : SmallNeighborhood y) :
    ProjectionPreimage H U.carrier ≃ U.carrier × FixedPathClass H y where
  toFun := chartTo H U
  invFun := chartInv H U
  left_inv := chartInv_chartTo H U
  right_inv := chartTo_chartInv H U

theorem projection_chartInv {y : X} (U : SmallNeighborhood y)
    (q : U.carrier × FixedPathClass H y) :
    CoveringSubgroupPathClass.projection H (chartInv H U q).1 = q.1.1 := by
  rcases q with ⟨z, q⟩
  refine Quotient.inductionOn q ?_
  intro alpha
  rfl

/-- The base overlap `U ∩ V`, retaining both membership certificates.-/
abbrev BaseOverlap {y z : X} (U : SmallNeighborhood y) (V : SmallNeighborhood z) :=
  {x : X // x ∈ U.carrier ∧ x ∈ V.carrier}

/-- Product-chart overlap: the base overlap times the discrete `U`-fiber coordinate.-/
abbrev ChartOverlap {y z : X} (U : SmallNeighborhood y) (V : SmallNeighborhood z) :=
  BaseOverlap U V × WithDiscreteTopology (FixedPathClass H y)

/-- Transition from the `U` product chart to the `V` product chart on their overlap.-/
noncomputable def chartTransition [PathConnectedSpace X] {y z : X}
    (U : SmallNeighborhood y) (V : SmallNeighborhood z) :
    ChartOverlap H U V → V.carrier × WithDiscreteTopology (FixedPathClass H z) := by
  intro q
  let ucoord : U.carrier × FixedPathClass H y :=
    (⟨q.1.1, q.1.2.1⟩, WithTopology.ofTopology q.2)
  let total := chartInv H U ucoord
  have hV : CoveringSubgroupPathClass.projection H total.1 ∈ V.carrier := by
    rw [projection_chartInv H U ucoord]
    exact q.1.2.2
  let c := chartTo H V ⟨total.1, hV⟩
  exact (c.1, WithTopology.toTopology ⊥ c.2)

theorem chartTransition_fst [PathConnectedSpace X] {y z : X}
    (U : SmallNeighborhood y) (V : SmallNeighborhood z) (q : ChartOverlap H U V) :
    (chartTransition H U V q).1 = (⟨q.1.1, q.1.2.2⟩ : V.carrier) := by
  apply Subtype.ext
  unfold chartTransition
  dsimp only
  rw [chartTo_fst, projection_chartInv]

theorem continuous_chartTransition_fst [PathConnectedSpace X] {y z : X}
    (U : SmallNeighborhood y) (V : SmallNeighborhood z) :
    Continuous (fun q : ChartOverlap H U V => (chartTransition H U V q).1) := by
  have hbase : Continuous
      (fun q : ChartOverlap H U V => (⟨q.1.1, q.1.2.2⟩ : V.carrier)) :=
    (continuous_subtype_val.comp continuous_fst).subtype_mk _
  apply hbase.congr
  intro q
  exact (chartTransition_fst H U V q).symm

/-- The discrete fiber coordinate of a transition map.-/
noncomputable def chartTransitionFiber [PathConnectedSpace X] {y z : X}
    (U : SmallNeighborhood y) (V : SmallNeighborhood z) :
    ChartOverlap H U V → WithDiscreteTopology (FixedPathClass H z) :=
  fun q => (chartTransition H U V q).2

theorem chartTransitionFiber_mk [PathConnectedSpace X] {y z : X}
    (U : SmallNeighborhood y) (V : SmallNeighborhood z)
    (a : BaseOverlap U V) (alpha : Path.Homotopic.Quotient x0 y) :
    chartTransitionFiber H U V
        (a, WithTopology.toTopology ⊥ (Quotient.mk _ alpha)) =
      WithTopology.toTopology ⊥
        (Quotient.mk _
          ((alpha.trans (U.localPathClass ⟨a.1, a.2.1⟩)).trans
            (V.localPathClass ⟨a.1, a.2.2⟩).symm) : FixedPathClass H z) := by
  unfold chartTransitionFiber chartTransition chartInv chartTo chartToRaw
  dsimp only [WithTopology.ofTopology_toTopology]
  simp only [Quotient.lift_mk]
  unfold chartToRepresentative
  rw [dite_eq_left a.2.2]

theorem chartTransitionFiber_mk_eq_of_joined [PathConnectedSpace X]
    {y z : X} (U : SmallNeighborhood y) (V : SmallNeighborhood z)
    {a b : BaseOverlap U V} (hab : Joined a b)
    (alpha : Path.Homotopic.Quotient x0 y) :
    chartTransitionFiber H U V
        (a, WithTopology.toTopology ⊥ (Quotient.mk _ alpha)) =
    chartTransitionFiber H U V
        (b, WithTopology.toTopology ⊥ (Quotient.mk _ alpha)) := by
  let fU : C(BaseOverlap U V, U.carrier) :=
    ⟨fun s => ⟨s.1, s.2.1⟩, continuous_subtype_val.subtype_mk _⟩
  let fV : C(BaseOverlap U V, V.carrier) :=
    ⟨fun s => ⟨s.1, s.2.2⟩, continuous_subtype_val.subtype_mk _⟩
  let deltaU : Path (⟨a.1, a.2.1⟩ : U.carrier) ⟨b.1, b.2.1⟩ :=
    hab.somePath.map fU.continuous
  let deltaV : Path (⟨a.1, a.2.2⟩ : V.carrier) ⟨b.1, b.2.2⟩ :=
    hab.somePath.map fV.continuous
  have hsegment : U.localSegmentClass deltaU = V.localSegmentClass deltaV := by
    unfold SmallNeighborhood.localSegmentClass deltaU deltaV
    change Path.Homotopic.Quotient.mk
        ((hab.somePath.map fU.continuous).map continuous_subtype_val) =
      Path.Homotopic.Quotient.mk
        ((hab.somePath.map fV.continuous).map continuous_subtype_val)
    apply congrArg Path.Homotopic.Quotient.mk
    rw [Path.map_map, Path.map_map]
  have hUcoh := U.localPathClass_trans_localSegmentClass deltaU
  have hVcoh := V.localPathClass_trans_localSegmentClass deltaV
  have hmiddle :
      (U.localPathClass ⟨a.1, a.2.1⟩).trans
          (V.localPathClass ⟨a.1, a.2.2⟩).symm =
        (U.localPathClass ⟨b.1, b.2.1⟩).trans
          (V.localPathClass ⟨b.1, b.2.2⟩).symm := by
    rw [← hUcoh, ← hVcoh, ← hsegment, quotient_symm_trans]
    symm
    calc
      ((U.localPathClass ⟨a.1, a.2.1⟩).trans
          (U.localSegmentClass deltaU)).trans
          ((U.localSegmentClass deltaU).symm.trans
            (V.localPathClass ⟨a.1, a.2.2⟩).symm) =
          (U.localPathClass ⟨a.1, a.2.1⟩).trans
            ((U.localSegmentClass deltaU).trans
              ((U.localSegmentClass deltaU).symm.trans
                (V.localPathClass ⟨a.1, a.2.2⟩).symm)) :=
        Path.Homotopic.Quotient.trans_assoc _ _ _
      _ = (U.localPathClass ⟨a.1, a.2.1⟩).trans
            (((U.localSegmentClass deltaU).trans
              (U.localSegmentClass deltaU).symm).trans
                (V.localPathClass ⟨a.1, a.2.2⟩).symm) := by
        rw [Path.Homotopic.Quotient.trans_assoc]
      _ = (U.localPathClass ⟨a.1, a.2.1⟩).trans
            ((Path.Homotopic.Quotient.refl _).trans
              (V.localPathClass ⟨a.1, a.2.2⟩).symm) := by
        rw [Path.Homotopic.Quotient.trans_symm]
      _ = (U.localPathClass ⟨a.1, a.2.1⟩).trans
            (V.localPathClass ⟨a.1, a.2.2⟩).symm := by
        rw [Path.Homotopic.Quotient.refl_trans]
  rw [chartTransitionFiber_mk, chartTransitionFiber_mk]
  have hfull :
      (alpha.trans (U.localPathClass ⟨a.1, a.2.1⟩)).trans
          (V.localPathClass ⟨a.1, a.2.2⟩).symm =
        (alpha.trans (U.localPathClass ⟨b.1, b.2.1⟩)).trans
          (V.localPathClass ⟨b.1, b.2.2⟩).symm := by
    rw [Path.Homotopic.Quotient.trans_assoc,
      Path.Homotopic.Quotient.trans_assoc]
    exact congrArg (fun p : Path.Homotopic.Quotient y z => alpha.trans p) hmiddle
  have hquot := congrArg
    (fun p : Path.Homotopic.Quotient x0 z => Quotient.mk (fixedSetoid H z) p) hfull
  exact congrArg
    (fun q : FixedPathClass H z => WithTopology.toTopology ⊥ q) hquot

theorem chartTransitionFiber_eq_of_joined [PathConnectedSpace X]
    {y z : X} (U : SmallNeighborhood y) (V : SmallNeighborhood z)
    {a b : BaseOverlap U V} (hab : Joined a b)
    (i : WithDiscreteTopology (FixedPathClass H y)) :
    chartTransitionFiber H U V (a, i) =
      chartTransitionFiber H U V (b, i) := by
  let qi : FixedPathClass H y := WithTopology.ofTopology i
  have hi : i = WithTopology.toTopology ⊥ qi := by
    exact (WithTopology.toTopology_ofTopology ⊥ i).symm
  rw [hi]
  refine Quotient.inductionOn qi ?_
  intro alpha
  exact chartTransitionFiber_mk_eq_of_joined H U V hab alpha

/-- Sets declared open by canonical charts; the fiber coordinate is discrete.-/
def ChartGenerator [PathConnectedSpace X] : Set (Set (CoveringSubgroupPathClass x0 H)) :=
  {s | ∃ (y : X) (U : SmallNeighborhood y)
      (w : Set (U.carrier × WithDiscreteTopology (FixedPathClass H y))),
      IsOpen w ∧
      s = {q | ∃ hq : CoveringSubgroupPathClass.projection H q ∈ U.carrier,
        let c := chartTo H U ⟨q, hq⟩
        (c.1, WithTopology.toTopology ⊥ c.2) ∈ w}}

/-- 由全部 canonical product charts 生成的 total-space 拓扑；它不是 generic quotient
topology。

> **Entry**: topology.covering.subgroup-canonical-chart-standard-/
@[instance_reducible] def coveringSubgroupTopology [PathConnectedSpace X] :
    TopologicalSpace (CoveringSubgroupPathClass x0 H) :=
  TopologicalSpace.generateFrom (ChartGenerator H)

noncomputable def chartToDiscrete [PathConnectedSpace X] {y : X}
    (U : SmallNeighborhood y) :
    ProjectionPreimage H U.carrier →
      U.carrier × WithDiscreteTopology (FixedPathClass H y) := fun q =>
  let c := chartTo H U q
  (c.1, WithTopology.toTopology ⊥ c.2)

noncomputable def chartInvDiscrete {y : X} (U : SmallNeighborhood y) :
    U.carrier × WithDiscreteTopology (FixedPathClass H y) →
      ProjectionPreimage H U.carrier := fun q =>
  chartInv H U (q.1, WithTopology.ofTopology q.2)

theorem chartToDiscrete_chartInvDiscrete [PathConnectedSpace X] {y : X}
    (U : SmallNeighborhood y)
    (q : U.carrier × WithDiscreteTopology (FixedPathClass H y)) :
    chartToDiscrete H U (chartInvDiscrete H U q) = q := by
  rcases q with ⟨z, q⟩
  unfold chartToDiscrete chartInvDiscrete
  rw [chartTo_chartInv]

theorem chartInvDiscrete_chartToDiscrete [PathConnectedSpace X] {y : X}
    (U : SmallNeighborhood y) (q : ProjectionPreimage H U.carrier) :
    chartInvDiscrete H U (chartToDiscrete H U q) = q := by
  unfold chartInvDiscrete chartToDiscrete
  dsimp only [WithTopology.ofTopology_toTopology]
  exact chartInv_chartTo H U q

noncomputable def chartEquivDiscrete [PathConnectedSpace X] {y : X}
    (U : SmallNeighborhood y) :
    ProjectionPreimage H U.carrier ≃
      U.carrier × WithDiscreteTopology (FixedPathClass H y) where
  toFun := chartToDiscrete H U
  invFun := chartInvDiscrete H U
  left_inv := chartInvDiscrete_chartToDiscrete H U
  right_inv := chartToDiscrete_chartInvDiscrete H U

theorem continuous_chartToDiscrete [PathConnectedSpace X] {y : X}
    (U : SmallNeighborhood y) :
    @Continuous
      (ProjectionPreimage H U.carrier)
      (U.carrier × WithDiscreteTopology (FixedPathClass H y))
      (@instTopologicalSpaceSubtype
        (CoveringSubgroupPathClass x0 H)
        (fun q => CoveringSubgroupPathClass.projection H q ∈ U.carrier)
        (coveringSubgroupTopology H))
      inferInstance
      (chartToDiscrete H U) := by
  let : TopologicalSpace (CoveringSubgroupPathClass x0 H) := coveringSubgroupTopology H
  rw [continuous_def]
  intro w hw
  rw [isOpen_induced_iff]
  let s : Set (CoveringSubgroupPathClass x0 H) :=
    {q | ∃ hq : CoveringSubgroupPathClass.projection H q ∈ U.carrier,
      chartToDiscrete H U ⟨q, hq⟩ ∈ w}
  refine ⟨s, ?_, ?_⟩
  · apply TopologicalSpace.isOpen_generateFrom_of_mem
    refine ⟨y, U, w, hw, ?_⟩
    ext q
    simp only [s, Set.mem_ofPred_eq]
    rfl
  · ext q
    simp only [Set.mem_preimage, s, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hq, hqw⟩
      simpa only [Subsingleton.elim hq q.2] using hqw
    · intro hqw
      exact ⟨q.2, hqw⟩

/-- Semilocal simple connectivity and local path connectivity supply an admissible chart.-/
theorem exists_smallNeighborhood [SemilocallySimplyConnectedSpace X]
    [LocallyPathConnectedSpace X] (y : X) : Nonempty (SmallNeighborhood y) := by
  obtain ⟨U, hUopen, hyU, hloops⟩ :=
    (semilocallySimplyConnectedAt_iff_exists_open_loops y).mp
      (SemilocallySimplyConnectedSpace.semilocallySimplyConnectedAt y)
  let V : Set X := pathComponentIn U y
  have hyV : y ∈ V := mem_pathComponentIn_self hyU
  have hVopen : IsOpen V := hUopen.pathComponentIn y
  have hVpath : IsPathConnected V := isPathConnected_pathComponentIn hyU
  refine ⟨{
    carrier := V
    center_mem := hyV
    isOpen := hVopen
    isPathConnected := hVpath
    loops_trivial := ?_ }⟩
  intro q
  let iVU : C(V, U) := ContinuousMap.inclusion pathComponentIn_subset
  let iUX : C(U, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let iVX : C(V, X) := ⟨Subtype.val, continuous_subtype_val⟩
  have hcomp : iUX.comp iVU = iVX := by ext; rfl
  have hqU : FundamentalGroup.map iUX ⟨y, hyU⟩
      (FundamentalGroup.map iVU ⟨y, hyV⟩ q) = 1 :=
    hloops (FundamentalGroup.map iVU ⟨y, hyV⟩ q)
  change FundamentalGroup.map iVX ⟨y, hyV⟩ q = 1
  rw [← hcomp, fundamentalGroup_map_comp]
  exact hqU

/-- Core overlap mechanism: the discrete fiber coordinate is locally constant.-/
theorem isLocallyConstant_chartTransitionFiber
    [PathConnectedSpace X] [LocallyPathConnectedSpace X]
    {y z : X} (U : SmallNeighborhood y) (V : SmallNeighborhood z) :
    IsLocallyConstant (chartTransitionFiber H U V) := by
  let : LocallyPathConnectedSpace (BaseOverlap U V) :=
    (U.isOpen.inter V.isOpen).locallyPathConnectedSpace
  rw [IsLocallyConstant.iff_exists_open]
  intro q
  refine ⟨pathComponent q.1 ×ˢ {q.2}, ?_, ?_, ?_⟩
  · exact (IsOpen.pathComponent q.1).prod (isOpen_discrete _)
  · exact ⟨mem_pathComponent_self q.1, Set.mem_singleton q.2⟩
  · rintro ⟨rbase, rfiber⟩ ⟨hrbase, hrfiber⟩
    have hj : Joined q.1 rbase := mem_pathComponent_iff.mp hrbase
    have hfiber : rfiber = q.2 := Set.mem_singleton_iff.mp hrfiber
    subst rfiber
    exact (chartTransitionFiber_eq_of_joined H U V hj q.2).symm

/-- Transition functions between canonical product charts are continuous.-/
theorem continuous_chartTransition [PathConnectedSpace X] [LocallyPathConnectedSpace X]
    {y z : X} (U : SmallNeighborhood y) (V : SmallNeighborhood z) :
    Continuous (chartTransition H U V) := by
  exact (continuous_chartTransition_fst H U V).prodMk
    (isLocallyConstant_chartTransitionFiber H U V).continuous

theorem continuous_chartInvDiscrete [PathConnectedSpace X] [LocallyPathConnectedSpace X]
    {y : X} (U : SmallNeighborhood y) :
    @Continuous
      (U.carrier × WithDiscreteTopology (FixedPathClass H y))
      (ProjectionPreimage H U.carrier)
      inferInstance
      (@instTopologicalSpaceSubtype
        (CoveringSubgroupPathClass x0 H)
        (fun q => CoveringSubgroupPathClass.projection H q ∈ U.carrier)
        (coveringSubgroupTopology H))
      (chartInvDiscrete H U) := by
  let : TopologicalSpace (CoveringSubgroupPathClass x0 H) := coveringSubgroupTopology H
  rw [continuous_induced_rng]
  change Continuous (fun q => (chartInvDiscrete H U q).1)
  rw [continuous_generateFrom_iff]
  intro s hs
  rcases hs with ⟨z, V, w, hw, rfl⟩
  let overlap : Set
      (U.carrier × WithDiscreteTopology (FixedPathClass H y)) :=
    {q | q.1.1 ∈ V.carrier}
  have hopen_overlap : IsOpen overlap := by
    exact V.isOpen.preimage
      (continuous_subtype_val.comp (continuous_fst : Continuous (fun q :
        U.carrier × WithDiscreteTopology (FixedPathClass H y) => q.1)))
  let toOverlap : overlap → ChartOverlap H U V := fun q =>
    (⟨q.1.1.1, q.1.1.2, q.2⟩, q.1.2)
  have htoOverlap : Continuous toOverlap := by
    exact ((continuous_subtype_val.comp
      (continuous_fst.comp continuous_subtype_val)).subtype_mk _).prodMk
        (continuous_snd.comp continuous_subtype_val)
  have htransition : Continuous (fun q : overlap => chartTransition H U V (toOverlap q)) :=
    (continuous_chartTransition H U V).comp htoOverlap
  let t : Set overlap := {q | chartTransition H U V (toOverlap q) ∈ w}
  have htopen : IsOpen t := hw.preimage htransition
  have himage_open : IsOpen (Subtype.val '' t) :=
    (hopen_overlap.isOpenEmbedding_subtypeVal.isOpen_iff_image_isOpen.mp htopen)
  convert himage_open using 1
  ext q
  constructor
  · rintro ⟨hqV, hqw⟩
    have hqV' : q.1.1 ∈ V.carrier := by
      simpa [chartInvDiscrete, projection_chartInv] using hqV
    let oq : overlap := ⟨q, hqV'⟩
    refine ⟨oq, ?_, rfl⟩
    change chartTransition H U V (toOverlap oq) ∈ w
    simpa [toOverlap, chartTransition, chartInvDiscrete, chartToDiscrete] using hqw
  · rintro ⟨oq, hoqw, rfl⟩
    refine ⟨?_, ?_⟩
    · have ho : oq.1.1.1 ∈ V.carrier := oq.2
      unfold chartInvDiscrete
      rw [projection_chartInv]
      exact ho
    change chartToDiscrete H V
      ⟨(chartInvDiscrete H U oq.1).1, ?_⟩ ∈ w
    simpa [t, toOverlap, chartTransition, chartInvDiscrete, chartToDiscrete] using hoqw

/-- Each canonical set chart becomes a homeomorphism for the atlas-generated topology.-/
theorem chart_homeomorph [PathConnectedSpace X] [LocallyPathConnectedSpace X]
    {y : X} (U : SmallNeighborhood y) :
    Nonempty
      (@Homeomorph
        (ProjectionPreimage H U.carrier)
        (U.carrier × WithDiscreteTopology (FixedPathClass H y))
        (@instTopologicalSpaceSubtype
          (CoveringSubgroupPathClass x0 H)
          (fun q => CoveringSubgroupPathClass.projection H q ∈ U.carrier)
          (coveringSubgroupTopology H))
        inferInstance) := by
  let : TopologicalSpace (CoveringSubgroupPathClass x0 H) := coveringSubgroupTopology H
  exact ⟨{
    toEquiv := chartEquivDiscrete H U
    continuous_toFun := continuous_chartToDiscrete H U
    continuous_invFun := continuous_chartInvDiscrete H U }⟩

theorem isOpen_projection_preimage_smallNeighborhood [PathConnectedSpace X]
    {y : X} (U : SmallNeighborhood y) :
    @IsOpen
      (CoveringSubgroupPathClass x0 H)
      (coveringSubgroupTopology H)
      ((CoveringSubgroupPathClass.projection H) ⁻¹' U.carrier) := by
  apply TopologicalSpace.isOpen_generateFrom_of_mem
  refine ⟨y, U, Set.univ, isOpen_univ, ?_⟩
  ext q
  simp only [Set.mem_preimage, Set.mem_univ]
  constructor
  · intro hq
    exact ⟨hq, trivial⟩
  · rintro ⟨hq, -⟩
    exact hq

/-- 子群道路类商在 canonical chart topology 下的终点投影是覆盖映射。

> **Entry**: topology.covering.subgroup-canonical-chart-standard-/
theorem coveringSubgroupProjection_isCoveringMap [SemilocallySimplyConnectedSpace X]
    [PathConnectedSpace X] [LocallyPathConnectedSpace X] :
    @IsCoveringMap
      (CoveringSubgroupPathClass x0 H) X
      (coveringSubgroupTopology H) inferInstance
      (CoveringSubgroupPathClass.projection H) := by
  let : TopologicalSpace (CoveringSubgroupPathClass x0 H) := coveringSubgroupTopology H
  intro y
  obtain ⟨U⟩ := exists_smallNeighborhood y
  have hfixed : IsEvenlyCovered
      (CoveringSubgroupPathClass.projection H) y
      (WithDiscreteTopology (FixedPathClass H y)) := by
    let e : (ProjectionPreimage H U.carrier) ≃ₜ
        (U.carrier × WithDiscreteTopology (FixedPathClass H y)) := {
      toEquiv := chartEquivDiscrete H U
      continuous_toFun := continuous_chartToDiscrete H U
      continuous_invFun := continuous_chartInvDiscrete H U }
    refine ⟨inferInstance, U.carrier, U.center_mem, U.isOpen,
      isOpen_projection_preimage_smallNeighborhood H U, e, ?_⟩
    intro q
    change (chartToDiscrete H U q).1.1 =
      CoveringSubgroupPathClass.projection H q.1
    exact chartTo_fst H U q
  exact hfixed.to_isEvenlyCovered_preimage

end CoveringSubgroupCanonicalChart

end

end SandronesLibrary.Topology
