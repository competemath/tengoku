/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.VanKampenCoverSubdivision
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.PathCodRestrict
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.PathCorrectedLoop
import Tengoku.Seed.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Tengoku.Seed.GroupTheory.PushoutI

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 二开集 van Kampen 规范同态的满射层

本文件直接复用 VK1 的带标签 `Path.subpath` 细分，构造交集基本群到两个覆盖成员基本群的
`Monoid.PushoutI`、它到环境基本群的规范同态、切换顶点的基点连接道路以及有限修正环路词。

当前条目：

* `topology.fundamental-group.van-kampen-surjectivity`。

最终定理证明：当 `U`、`V`、`U ∩ V` 道路连通且 `U ∪ V = Set.univ` 时，该规范同态满射。
本文件不证明单射、推送同构或完整 Seifert--van Kampen 定理。
-/

open Set
open scoped unitInterval

noncomputable section

namespace SandronesLibrary.Topology

universe u

variable {X : Type u} [TopologicalSpace X]

/-- 公共基点在二元覆盖成员中的子类型版本。

> **Entry**: topology.fundamental-group.van-kampen-surjectivity-/
def binaryOpenCoverBasepoint {U V : Set X} {x₀ : X} (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) :
    (b : Bool) → binaryOpenCoverPiece U V b
  | false => ⟨x₀, hxU⟩
  | true => ⟨x₀, hxV⟩

abbrev binaryOpenCoverIntersectionBasepoint {U V : Set X} {x₀ : X}
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) : ↥(U ∩ V) :=
  ⟨x₀, hxU, hxV⟩

def binaryOpenCoverIntersectionToPiece (U V : Set X) :
    (b : Bool) → C(↥(U ∩ V), binaryOpenCoverPiece U V b)
  | false => ⟨fun z => ⟨z.1, z.2.1⟩, continuous_subtype_val.subtype_mk _⟩
  | true => ⟨fun z => ⟨z.1, z.2.2⟩, continuous_subtype_val.subtype_mk _⟩

def binaryOpenCoverPieceToSpace (U V : Set X) :
    (b : Bool) → C(binaryOpenCoverPiece U V b, X)
  | false => ⟨Subtype.val, continuous_subtype_val⟩
  | true => ⟨Subtype.val, continuous_subtype_val⟩

def binaryOpenCoverIntersectionToSpace (U V : Set X) : C(↥(U ∩ V), X) :=
  ⟨Subtype.val, continuous_subtype_val⟩

def binaryOpenCoverIntersectionMapToSpace (U V : Set X) {x₀ : X}
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) :
    FundamentalGroup (↥(U ∩ V)) (binaryOpenCoverIntersectionBasepoint hxU hxV) →*
      FundamentalGroup X x₀ :=
  FundamentalGroup.map (binaryOpenCoverIntersectionToSpace U V)
    (binaryOpenCoverIntersectionBasepoint hxU hxV)

def binaryOpenCoverIntersectionMaps (U V : Set X) {x₀ : X}
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) :
    (b : Bool) → FundamentalGroup (↥(U ∩ V))
      (binaryOpenCoverIntersectionBasepoint hxU hxV) →*
      FundamentalGroup (binaryOpenCoverPiece U V b)
        (binaryOpenCoverBasepoint hxU hxV b) := by
  intro b
  cases b
  · exact FundamentalGroup.map (binaryOpenCoverIntersectionToPiece U V false)
      (binaryOpenCoverIntersectionBasepoint hxU hxV)
  · exact FundamentalGroup.map (binaryOpenCoverIntersectionToPiece U V true)
      (binaryOpenCoverIntersectionBasepoint hxU hxV)

abbrev binaryVanKampenPushout (U V : Set X) {x₀ : X}
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) :=
  Monoid.PushoutI (binaryOpenCoverIntersectionMaps U V hxU hxV)

def binaryOpenCoverPieceMaps (U V : Set X) {x₀ : X}
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) :
    (b : Bool) → FundamentalGroup (binaryOpenCoverPiece U V b)
      (binaryOpenCoverBasepoint hxU hxV b) →* FundamentalGroup X x₀ := by
  intro b
  cases b
  · exact FundamentalGroup.map (binaryOpenCoverPieceToSpace U V false) ⟨x₀, hxU⟩
  · exact FundamentalGroup.map (binaryOpenCoverPieceToSpace U V true) ⟨x₀, hxV⟩

theorem binaryOpenCoverPieceMaps_compat (U V : Set X) {x₀ : X}
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) :
    ∀ b, (binaryOpenCoverPieceMaps U V hxU hxV b).comp
        (binaryOpenCoverIntersectionMaps U V hxU hxV b) =
      binaryOpenCoverIntersectionMapToSpace U V hxU hxV := by
  intro b
  cases b
  · ext g
    rcases Path.Homotopic.Quotient.mk_surjective g with ⟨p, rfl⟩
    change ((Path.Homotopic.Quotient.mk p).map
      (binaryOpenCoverIntersectionToPiece U V false)).map
        (binaryOpenCoverPieceToSpace U V false) =
      (Path.Homotopic.Quotient.mk p).map (binaryOpenCoverIntersectionToSpace U V)
    rw [← Path.Homotopic.Quotient.map_comp]
    rfl
  · ext g
    rcases Path.Homotopic.Quotient.mk_surjective g with ⟨p, rfl⟩
    change ((Path.Homotopic.Quotient.mk p).map
      (binaryOpenCoverIntersectionToPiece U V true)).map
        (binaryOpenCoverPieceToSpace U V true) =
      (Path.Homotopic.Quotient.mk p).map (binaryOpenCoverIntersectionToSpace U V)
    rw [← Path.Homotopic.Quotient.map_comp]
    rfl

def binaryVanKampenCanonicalMap (U V : Set X) {x₀ : X}
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) :
    binaryVanKampenPushout U V hxU hxV →* FundamentalGroup X x₀ :=
  Monoid.PushoutI.lift
    (binaryOpenCoverPieceMaps U V hxU hxV)
    (binaryOpenCoverIntersectionMapToSpace U V hxU hxV)
    (binaryOpenCoverPieceMaps_compat U V hxU hxV)

def basedPieceLoop {x₀ z w : X} (S : Set X)
    (hx₀ : x₀ ∈ S) (hz : z ∈ S) (hw : w ∈ S)
    (left : Path x₀ z) (segment : Path z w) (right : Path x₀ w)
    (hleft : ∀ t, left t ∈ S) (hsegment : ∀ t, segment t ∈ S)
    (hright : ∀ t, right t ∈ S) :
    FundamentalGroup S ⟨x₀, hx₀⟩ :=
  FundamentalGroup.fromPath ⟦
    (pathCodRestrict S left hx₀ hz hleft).trans
      ((pathCodRestrict S segment hz hw hsegment).trans
        (pathCodRestrict S right hx₀ hw hright).symm)⟧

theorem map_basedPieceLoop_subtypeVal {x₀ z w : X} (S : Set X)
    (hx₀ : x₀ ∈ S) (hz : z ∈ S) (hw : w ∈ S)
    (left : Path x₀ z) (segment : Path z w) (right : Path x₀ w)
    (hleft : ∀ t, left t ∈ S) (hsegment : ∀ t, segment t ∈ S)
    (hright : ∀ t, right t ∈ S) :
    FundamentalGroup.map (⟨Subtype.val, continuous_subtype_val⟩ : C(S, X)) ⟨x₀, hx₀⟩
        (basedPieceLoop S hx₀ hz hw left segment right hleft hsegment hright) =
      FundamentalGroup.fromPath ⟦left.trans (segment.trans right.symm)⟧ := by
  simp only [basedPieceLoop, FundamentalGroup.map_apply]
  apply congr_arg Path.Homotopic.Quotient.mk
  ext t
  simp [Path.trans_apply, pathCodRestrict]

namespace Path

def BinaryOpenCoverSubdivision.firstReflConnector {x₀ : X} (p : Path x₀ x₀)
    {U V : Set X} (D : BinaryOpenCoverSubdivision p U V) :
    Path x₀ (p (unitIntervalMeshPoint D.steps D.steps_pos 0)) :=
  (Path.refl x₀).cast rfl (by simp [p.source])

def BinaryOpenCoverSubdivision.lastReflConnector {x₀ : X} (p : Path x₀ x₀)
    {U V : Set X} (D : BinaryOpenCoverSubdivision p U V) :
    Path x₀ (p (unitIntervalMeshPoint D.steps D.steps_pos (Fin.last D.steps))) :=
  (Path.refl x₀).cast rfl (by simp [p.target])

structure BinaryOpenCoverSubdivision.BasedConnectors {x₀ : X} {p : Path x₀ x₀}
    {U V : Set X} (D : BinaryOpenCoverSubdivision p U V) where
  connector : (i : Fin (D.steps + 1)) →
    Path x₀ (p (unitIntervalMeshPoint D.steps D.steps_pos i))
  left_mem : ∀ i : Fin D.steps, ∀ t,
    connector i.castSucc t ∈ binaryOpenCoverPiece U V (D.label i)
  right_mem : ∀ i : Fin D.steps, ∀ t,
    connector i.succ t ∈ binaryOpenCoverPiece U V (D.label i)
  connector_zero : connector 0 = D.firstReflConnector p
  connector_last : connector (Fin.last D.steps) = D.lastReflConnector p

theorem BinaryOpenCoverSubdivision.exists_basedConnectors {x₀ : X} {p : Path x₀ x₀}
    {U V : Set X} (D : BinaryOpenCoverSubdivision p U V)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (hUV : IsPathConnected (U ∩ V)) : Nonempty D.BasedConnectors := by
  have hvertex : ∀ i : Fin (D.steps + 1), ∃ c :
      Path x₀ (p (unitIntervalMeshPoint D.steps D.steps_pos i)),
      (∀ j : Fin D.steps, j.castSucc = i → ∀ t,
        c t ∈ binaryOpenCoverPiece U V (D.label j)) ∧
      (∀ j : Fin D.steps, j.succ = i → ∀ t,
        c t ∈ binaryOpenCoverPiece U V (D.label j)) ∧
      (i = 0 → HEq c (D.firstReflConnector p)) ∧
      (i = Fin.last D.steps → HEq c (D.lastReflConnector p)) := by
    intro i
    by_cases hi0 : i = 0
    · subst i
      refine ⟨D.firstReflConnector p, ?_, ?_, fun _ => HEq.rfl, ?_⟩
      · intro j hj t
        cases h : D.label j <;>
          simp [BinaryOpenCoverSubdivision.firstReflConnector, Path.cast_coe,
            binaryOpenCoverPiece, hxU, hxV]
      · intro j hj
        exfalso
        have : j.val + 1 = 0 := congr_arg Fin.val hj
        omega
      · intro hlast
        have : 0 = D.steps := by
          simpa using congr_arg Fin.val hlast
        exact False.elim ((Nat.ne_of_gt D.steps_pos) this.symm)
    by_cases hilast : i = Fin.last D.steps
    · subst i
      refine ⟨D.lastReflConnector p, ?_, ?_, ?_, fun _ => HEq.rfl⟩
      · intro j hj
        exfalso
        have : j.val = D.steps := congr_arg Fin.val hj
        omega
      · intro j hj t
        cases h : D.label j <;>
          simp [BinaryOpenCoverSubdivision.lastReflConnector, Path.cast_coe,
            binaryOpenCoverPiece, hxU, hxV]
      · intro hzero
        exact (hi0 hzero).elim
    obtain ⟨l, hl⟩ := Fin.exists_succ_eq_of_ne_zero hi0
    obtain ⟨r, hr⟩ := Fin.eq_castSucc_of_ne_last hilast
    have hshared : l.succ = r.castSucc := hl.trans hr.symm
    by_cases hlabels : D.label l = D.label r
    · cases hb : D.label r
      · have hz : p (unitIntervalMeshPoint D.steps D.steps_pos i) ∈ U := by
          have := D.subpath_mem r 0
          simpa [Path.subpath, binaryOpenCoverPiece, hb, ← hr] using this
        let q := (hU.joinedIn x₀ hxU _ hz).somePath
        refine ⟨q, ?_, ?_, (fun h => (hi0 h).elim), (fun h => (hilast h).elim)⟩
        · intro j hj t
          have hjr : j = r := (Fin.castSucc_injective _) (hj.trans hr.symm)
          subst j
          simp only [hb, binaryOpenCoverPiece]
          change (hU.joinedIn x₀ hxU _ hz).somePath t ∈ U
          simpa only [q] using (hU.joinedIn x₀ hxU _ hz).somePath_mem t
        · intro j hj t
          have hjl : j = l := (Fin.succ_injective _) (hj.trans hl.symm)
          subst j
          have hbl : D.label l = false := hlabels.trans hb
          simp only [hbl, binaryOpenCoverPiece]
          change (hU.joinedIn x₀ hxU _ hz).somePath t ∈ U
          simpa only [q] using (hU.joinedIn x₀ hxU _ hz).somePath_mem t
      · have hz : p (unitIntervalMeshPoint D.steps D.steps_pos i) ∈ V := by
          have := D.subpath_mem r 0
          simpa [Path.subpath, binaryOpenCoverPiece, hb, ← hr] using this
        let q := (hV.joinedIn x₀ hxV _ hz).somePath
        refine ⟨q, ?_, ?_, (fun h => (hi0 h).elim), (fun h => (hilast h).elim)⟩
        · intro j hj t
          have hjr : j = r := (Fin.castSucc_injective _) (hj.trans hr.symm)
          subst j
          simp only [hb, binaryOpenCoverPiece]
          change (hV.joinedIn x₀ hxV _ hz).somePath t ∈ V
          simpa only [q] using (hV.joinedIn x₀ hxV _ hz).somePath_mem t
        · intro j hj t
          have hjl : j = l := (Fin.succ_injective _) (hj.trans hl.symm)
          subst j
          have hbl : D.label l = true := hlabels.trans hb
          simp only [hbl, binaryOpenCoverPiece]
          change (hV.joinedIn x₀ hxV _ hz).somePath t ∈ V
          simpa only [q] using (hV.joinedIn x₀ hxV _ hz).somePath_mem t
    · have hz : p (unitIntervalMeshPoint D.steps D.steps_pos i) ∈ U ∩ V := by
        rw [← hl]
        exact D.switchVertex_mem_intersection l r hshared hlabels
      let q := (hUV.joinedIn x₀ ⟨hxU, hxV⟩ _ hz).somePath
      refine ⟨q, ?_, ?_, (fun h => (hi0 h).elim), (fun h => (hilast h).elim)⟩
      · intro j hj t
        have hjr : j = r := (Fin.castSucc_injective _) (hj.trans hr.symm)
        subst j
        cases hb : D.label r
        · exact (hUV.joinedIn x₀ ⟨hxU, hxV⟩ _ hz).somePath_mem t |>.1
        · exact (hUV.joinedIn x₀ ⟨hxU, hxV⟩ _ hz).somePath_mem t |>.2
      · intro j hj t
        have hjl : j = l := (Fin.succ_injective _) (hj.trans hl.symm)
        subst j
        cases hb : D.label l
        · exact (hUV.joinedIn x₀ ⟨hxU, hxV⟩ _ hz).somePath_mem t |>.1
        · exact (hUV.joinedIn x₀ ⟨hxU, hxV⟩ _ hz).somePath_mem t |>.2
  let connector := fun i => Classical.choose (hvertex i)
  refine ⟨{
    connector := connector
    left_mem := ?_
    right_mem := ?_
    connector_zero := ?_
    connector_last := ?_ }⟩
  · intro i t
    exact (Classical.choose_spec (hvertex i.castSucc)).1 i rfl t
  · intro i t
    exact (Classical.choose_spec (hvertex i.succ)).2.1 i rfl t
  · exact eq_of_heq ((Classical.choose_spec (hvertex 0)).2.2.1 rfl)
  · exact eq_of_heq ((Classical.choose_spec (hvertex (Fin.last D.steps))).2.2.2 rfl)

def BinaryOpenCoverSubdivision.segmentPieceLoopOfLabel {x₀ : X} {p : Path x₀ x₀}
    {U V : Set X} (D : BinaryOpenCoverSubdivision p U V) (C : D.BasedConnectors)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (i : Fin D.steps)
    (b : Bool) (h : D.label i = b) :
    FundamentalGroup (binaryOpenCoverPiece U V b)
      (binaryOpenCoverBasepoint hxU hxV b) := by
  cases b
  · have hz : p (unitIntervalMeshPoint D.steps D.steps_pos i.castSucc) ∈ U := by
      simpa [Path.subpath, binaryOpenCoverPiece, h] using D.subpath_mem i 0
    have hw : p (unitIntervalMeshPoint D.steps D.steps_pos i.succ) ∈ U := by
      simpa [Path.subpath, binaryOpenCoverPiece, h] using D.subpath_mem i 1
    exact basedPieceLoop U hxU hz hw
      (C.connector i.castSucc)
      (p.subpath (unitIntervalMeshPoint D.steps D.steps_pos i.castSucc)
        (unitIntervalMeshPoint D.steps D.steps_pos i.succ))
      (C.connector i.succ)
      (by simpa [binaryOpenCoverPiece, h] using C.left_mem i)
      (by simpa [binaryOpenCoverPiece, h] using D.subpath_mem i)
      (by simpa [binaryOpenCoverPiece, h] using C.right_mem i)
  · have hz : p (unitIntervalMeshPoint D.steps D.steps_pos i.castSucc) ∈ V := by
      simpa [Path.subpath, binaryOpenCoverPiece, h] using D.subpath_mem i 0
    have hw : p (unitIntervalMeshPoint D.steps D.steps_pos i.succ) ∈ V := by
      simpa [Path.subpath, binaryOpenCoverPiece, h] using D.subpath_mem i 1
    exact basedPieceLoop V hxV hz hw
      (C.connector i.castSucc)
      (p.subpath (unitIntervalMeshPoint D.steps D.steps_pos i.castSucc)
        (unitIntervalMeshPoint D.steps D.steps_pos i.succ))
      (C.connector i.succ)
      (by simpa [binaryOpenCoverPiece, h] using C.left_mem i)
      (by simpa [binaryOpenCoverPiece, h] using D.subpath_mem i)
      (by simpa [binaryOpenCoverPiece, h] using C.right_mem i)

def BinaryOpenCoverSubdivision.segmentPieceLoop {x₀ : X} {p : Path x₀ x₀}
    {U V : Set X} (D : BinaryOpenCoverSubdivision p U V) (C : D.BasedConnectors)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (i : Fin D.steps) :
    FundamentalGroup (binaryOpenCoverPiece U V (D.label i))
      (binaryOpenCoverBasepoint hxU hxV (D.label i)) :=
  D.segmentPieceLoopOfLabel C hxU hxV i (D.label i) rfl

theorem map_reverseDfoldl {M N : Type*} [Monoid M] [Monoid N]
    (φ : M →* N) {n : ℕ} (a : Fin n → M) :
    φ (Fin.dfoldl n (fun _ => M) (fun i acc => a i * acc) 1) =
      Fin.dfoldl n (fun _ => N) (fun i acc => φ (a i) * acc) 1 := by
  induction n with
  | zero => simp [Fin.dfoldl_zero]
  | succ n ih =>
      rw [Fin.dfoldl_succ_last, Fin.dfoldl_succ_last, map_mul]
      congr 1
      change φ (Fin.dfoldl n (fun _ => M) (fun i acc => a i.castSucc * acc) 1) =
        Fin.dfoldl n (fun _ => N) (fun i acc => φ (a i.castSucc) * acc) 1
      exact ih (fun i => a i.castSucc)

def BinaryOpenCoverSubdivision.pushoutSegmentWord
    {x₀ : X} {p : Path x₀ x₀} {U V : Set X}
    (D : BinaryOpenCoverSubdivision p U V) (C : D.BasedConnectors)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) : binaryVanKampenPushout U V hxU hxV :=
  Fin.dfoldl D.steps (fun _ => binaryVanKampenPushout U V hxU hxV)
    (fun i acc => Monoid.PushoutI.of (D.label i) (D.segmentPieceLoop C hxU hxV i) * acc) 1

theorem BinaryOpenCoverSubdivision.canonicalMap_of_segmentPieceLoopOfLabel
    {x₀ : X} {p : Path x₀ x₀} {U V : Set X}
    (D : BinaryOpenCoverSubdivision p U V) (C : D.BasedConnectors)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (i : Fin D.steps)
    (b : Bool) (hb : D.label i = b) :
    binaryVanKampenCanonicalMap U V hxU hxV
        (Monoid.PushoutI.of b (D.segmentPieceLoopOfLabel C hxU hxV i b hb)) =
      FundamentalGroup.fromPath ⟦correctedLoop
        (C.connector i.castSucc)
        (p.subpath (unitIntervalMeshPoint D.steps D.steps_pos i.castSucc)
          (unitIntervalMeshPoint D.steps D.steps_pos i.succ))
        (C.connector i.succ)⟧ := by
  rw [binaryVanKampenCanonicalMap, Monoid.PushoutI.lift_of]
  cases b
  · rw [BinaryOpenCoverSubdivision.segmentPieceLoopOfLabel]
    exact map_basedPieceLoop_subtypeVal U hxU
      (by simpa [Path.subpath, binaryOpenCoverPiece, hb] using D.subpath_mem i 0)
      (by simpa [Path.subpath, binaryOpenCoverPiece, hb] using D.subpath_mem i 1)
      (C.connector i.castSucc)
      (p.subpath (unitIntervalMeshPoint D.steps D.steps_pos i.castSucc)
        (unitIntervalMeshPoint D.steps D.steps_pos i.succ))
      (C.connector i.succ)
      (by simpa [binaryOpenCoverPiece, hb] using C.left_mem i)
      (by simpa [binaryOpenCoverPiece, hb] using D.subpath_mem i)
      (by simpa [binaryOpenCoverPiece, hb] using C.right_mem i)
  · rw [BinaryOpenCoverSubdivision.segmentPieceLoopOfLabel]
    exact map_basedPieceLoop_subtypeVal V hxV
      (by simpa [Path.subpath, binaryOpenCoverPiece, hb] using D.subpath_mem i 0)
      (by simpa [Path.subpath, binaryOpenCoverPiece, hb] using D.subpath_mem i 1)
      (C.connector i.castSucc)
      (p.subpath (unitIntervalMeshPoint D.steps D.steps_pos i.castSucc)
        (unitIntervalMeshPoint D.steps D.steps_pos i.succ))
      (C.connector i.succ)
      (by simpa [binaryOpenCoverPiece, hb] using C.left_mem i)
      (by simpa [binaryOpenCoverPiece, hb] using D.subpath_mem i)
      (by simpa [binaryOpenCoverPiece, hb] using C.right_mem i)

theorem BinaryOpenCoverSubdivision.canonicalMap_of_segmentPieceLoop
    {x₀ : X} {p : Path x₀ x₀} {U V : Set X}
    (D : BinaryOpenCoverSubdivision p U V) (C : D.BasedConnectors)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) (i : Fin D.steps) :
    binaryVanKampenCanonicalMap U V hxU hxV
        (Monoid.PushoutI.of (D.label i) (D.segmentPieceLoop C hxU hxV i)) =
      FundamentalGroup.fromPath ⟦correctedLoop
        (C.connector i.castSucc)
        (p.subpath (unitIntervalMeshPoint D.steps D.steps_pos i.castSucc)
          (unitIntervalMeshPoint D.steps D.steps_pos i.succ))
        (C.connector i.succ)⟧ :=
  D.canonicalMap_of_segmentPieceLoopOfLabel C hxU hxV i (D.label i) rfl

theorem BinaryOpenCoverSubdivision.canonicalMap_pushoutSegmentWord
    {x₀ : X} {p : Path x₀ x₀} {U V : Set X}
    (D : BinaryOpenCoverSubdivision p U V) (C : D.BasedConnectors)
    (hxU : x₀ ∈ U) (hxV : x₀ ∈ V) :
    binaryVanKampenCanonicalMap U V hxU hxV (D.pushoutSegmentWord C hxU hxV) =
      correctedLoopWord
        (p ∘ unitIntervalMeshPoint D.steps D.steps_pos)
        (fun i => p.subpath
          (unitIntervalMeshPoint D.steps D.steps_pos i.castSucc)
          (unitIntervalMeshPoint D.steps D.steps_pos i.succ))
        C.connector := by
  unfold BinaryOpenCoverSubdivision.pushoutSegmentWord
  rw [map_reverseDfoldl]
  unfold correctedLoopWord
  apply congr_arg (fun a : Fin D.steps → FundamentalGroup X x₀ =>
    Fin.dfoldl D.steps (fun _ => FundamentalGroup X x₀)
      (fun i acc => a i * acc) 1)
  funext i
  exact D.canonicalMap_of_segmentPieceLoop C hxU hxV i

/-- 在道路同伦商中，transport 后的首末常连接在道路两侧抵消。-/
theorem quotient_reflCast_trans_trans_reflCast_symm
    {x z w : X} (hz : z = x) (hw : w = x)
    (q : Path.Homotopic.Quotient z w) :
    ((Path.Homotopic.Quotient.refl x).cast rfl hz).trans
        (q.trans ((Path.Homotopic.Quotient.refl x).cast rfl hw).symm) =
      q.cast hz.symm hw.symm := by
  cases hz
  cases hw
  simp only [Path.Homotopic.Quotient.cast_rfl_rfl]
  induction q using Path.Homotopic.Quotient.ind with
  | mk q =>
      apply Quotient.sound
      exact (show ((Path.refl x).trans (q.trans (Path.refl x).symm)).Homotopic
          (q.trans (Path.refl x).symm) from
        ⟨Path.Homotopy.reflTrans (q.trans (Path.refl x).symm)⟩).trans
        (by simpa using (show (q.trans (Path.refl x)).Homotopic q from
          ⟨Path.Homotopy.transRefl q⟩))

/-- 把全区间子道路 transport 回环路端点后，得到原环路的道路同伦类。-/
theorem quotient_subpath_cast_eq_loop {x : X} (p : Path x x)
    (t₀ t₁ : unitInterval) (ht₀ : t₀ = 0) (ht₁ : t₁ = 1)
    (hz : p t₀ = x) (hw : p t₁ = x) :
    (Path.Homotopic.Quotient.mk (p.subpath t₀ t₁)).cast hz.symm hw.symm =
      Path.Homotopic.Quotient.mk p := by
  subst t₀
  subst t₁
  simp [Path.subpath_zero_one]

/-- 带基点连接的有限细分所给出的修正环路词代表原环境环路。-/
theorem BinaryOpenCoverSubdivision.correctedLoopWord_eq_loop
    {x₀ : X} {p : Path x₀ x₀} {U V : Set X}
    (D : BinaryOpenCoverSubdivision p U V) (C : D.BasedConnectors) :
    correctedLoopWord
        (p ∘ unitIntervalMeshPoint D.steps D.steps_pos)
        (fun i => p.subpath
          (unitIntervalMeshPoint D.steps D.steps_pos i.castSucc)
          (unitIntervalMeshPoint D.steps D.steps_pos i.succ))
        C.connector = FundamentalGroup.fromPath ⟦p⟧ := by
  rw [correctedLoopWord_eq_concat]
  unfold correctedLoop
  rw [C.connector_zero, C.connector_last]
  change Path.Homotopic.Quotient.mk
      ((D.firstReflConnector p).trans
        ((Path.concat (p ∘ unitIntervalMeshPoint D.steps D.steps_pos)
          (fun i => p.subpath
            (unitIntervalMeshPoint D.steps D.steps_pos i.castSucc)
            (unitIntervalMeshPoint D.steps D.steps_pos i.succ))).trans
          (D.lastReflConnector p).symm)) = Path.Homotopic.Quotient.mk p
  simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm]
  have hconcat : Path.Homotopic.Quotient.mk
      (Path.concat (p ∘ unitIntervalMeshPoint D.steps D.steps_pos)
        (fun i => p.subpath
          (unitIntervalMeshPoint D.steps D.steps_pos i.castSucc)
          (unitIntervalMeshPoint D.steps D.steps_pos i.succ))) =
      Path.Homotopic.Quotient.mk
        (p.subpath (unitIntervalMeshPoint D.steps D.steps_pos 0)
          (unitIntervalMeshPoint D.steps D.steps_pos (Fin.last D.steps))) :=
    Quotient.sound D.concatSubpaths_homotopic
  rw [hconcat]
  have hz : p (unitIntervalMeshPoint D.steps D.steps_pos 0) = x₀ := by
    simp [p.source]
  have hw : p (unitIntervalMeshPoint D.steps D.steps_pos (Fin.last D.steps)) = x₀ := by
    simp [p.target]
  calc
    _ = (Path.Homotopic.Quotient.mk
          (p.subpath (unitIntervalMeshPoint D.steps D.steps_pos 0)
            (unitIntervalMeshPoint D.steps D.steps_pos (Fin.last D.steps)))).cast
          hz.symm hw.symm := by
      simpa [BinaryOpenCoverSubdivision.firstReflConnector,
        BinaryOpenCoverSubdivision.lastReflConnector] using
        quotient_reflCast_trans_trans_reflCast_symm hz hw
          (Path.Homotopic.Quotient.mk
            (p.subpath (unitIntervalMeshPoint D.steps D.steps_pos 0)
              (unitIntervalMeshPoint D.steps D.steps_pos (Fin.last D.steps))))
    _ = Path.Homotopic.Quotient.mk p :=
      quotient_subpath_cast_eq_loop p
        (unitIntervalMeshPoint D.steps D.steps_pos 0)
        (unitIntervalMeshPoint D.steps D.steps_pos (Fin.last D.steps))
        (unitIntervalMeshPoint_zero D.steps D.steps_pos)
        (unitIntervalMeshPoint_last D.steps D.steps_pos) hz hw

/-- 对道路连通的二开集覆盖，两个覆盖成员基本群沿交集基本群的 amalgamated free product 到环境
基本群的规范同态是满射。-/
theorem surjective_binaryVanKampenCanonicalMap
    {x₀ : X} (U V : Set X) (hxU : x₀ ∈ U) (hxV : x₀ ∈ V)
    (hUopen : IsOpen U) (hVopen : IsOpen V) (hcover : U ∪ V = Set.univ)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (hUV : IsPathConnected (U ∩ V)) :
    Function.Surjective (binaryVanKampenCanonicalMap U V hxU hxV) := by
  intro g
  rcases Path.Homotopic.Quotient.mk_surjective g with ⟨p, rfl⟩
  have hp : ∀ t, p t ∈ U ∨ p t ∈ V := by
    intro t
    have ht : p t ∈ U ∪ V := by rw [hcover]; exact Set.mem_univ _
    exact ht
  obtain ⟨D⟩ := Path.exists_binaryOpenCoverSubdivision p hUopen hVopen hp
  obtain ⟨C⟩ := D.exists_basedConnectors hxU hxV hU hV hUV
  refine ⟨D.pushoutSegmentWord C hxU hxV, ?_⟩
  rw [D.canonicalMap_pushoutSegmentWord C hxU hxV]
  exact D.correctedLoopWord_eq_loop C

end Path

end SandronesLibrary.Topology
