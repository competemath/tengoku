/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
module

public import Tengoku.LeanPool.LeanPool.ClassificationOfSurfaces.Moise.OpenMidpointComplex
public import Tengoku.LeanPool.LeanPool.ClassificationOfSurfaces.Moise.LocallyFiniteTriangulation

/-!
# Adaptive midpoint tiles in an open polyhedron

Select the first triangle in each midpoint-descendant chain whose complete carrier lies in an
open set.  These triangles cover the open set and form a locally finite hierarchical tiling.
Their edges need not yet form a conforming simplicial complex: a coarse edge may contain several
edges of finer adjacent tiles.  The next layer resolves precisely those hanging vertices.
-/

@[expose] public section

open scoped BigOperators

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace IntrinsicTwoComplex

variable (K : IntrinsicTwoComplex) (U : Set K.realization)

/-- A maximal face at midpoint level `n`. -/
abbrev LevelFace (n : ℕ) := (K.safeSubdivision n).refined.Face

/-- The carrier of a level face, transported back to the original realization. -/
def levelFaceCarrier {n : ℕ} (t : K.LevelFace n) : Set K.realization :=
  (K.safeSubdivision n).homeo ''
    (K.safeSubdivision n).refined.faceCarrier t.1

/--
@isnad1 id=iscompac.0h3v.s5.6c9531de2348 from=translated src=- shape=e41714bc vocab=bc11c453
-/
theorem isCompact_levelFaceCarrier {n : ℕ} (t : K.LevelFace n) :
    IsCompact (K.levelFaceCarrier t) :=
  ((K.safeSubdivision n).refined.faceCarrier_closed t.1).isCompact.image
    (K.safeSubdivision n).homeo.continuous

/-- A hereditary rule selecting sufficiently small level faces inside `U`.

The default rule is simple containment in `U`.  A stricter local rule can be installed as a
local instance, allowing the conforming adaptive fan construction to be reused for open-cover,
oscillation, separation, and boundary-control requirements. -/
class AdaptiveSafety (K : IntrinsicTwoComplex) (U : Set K.realization) where
  /-- The `safe` declaration. -/
  safe : {n : ℕ} → K.LevelFace n → Prop
  carrier_subset : ∀ {n : ℕ} {t : K.LevelFace n}, safe t →
    K.levelFaceCarrier t ⊆ U
  hereditary : ∀ {n m : ℕ} {s : K.LevelFace n} {t : K.LevelFace m},
    K.levelFaceCarrier t ⊆ K.levelFaceCarrier s → safe s → safe t

/-- The original safety rule: a face is safe exactly when its carrier lies in `U`.  Its low
priority lets a quantitative chart-control rule override it locally without changing any of the
adaptive combinatorial APIs. -/
instance (priority := 100) defaultAdaptiveSafety : AdaptiveSafety K U where
  safe t := K.levelFaceCarrier t ⊆ U
  carrier_subset ht := ht
  hereditary hts hs := hts.trans hs

/-- The active safety predicate. -/
def LevelFace.IsSafe [AdaptiveSafety K U] {n : ℕ} (t : K.LevelFace n) : Prop :=
  AdaptiveSafety.safe (K := K) (U := U) t

/--
@isnad1 id=iff.0h4v.s7.e3b8309d683a from=translated src=- shape=b3cf5300 vocab=86a802db
-/
theorem levelFace_isSafe_iff {n : ℕ} (t : K.LevelFace n) :
    @LevelFace.IsSafe K U (defaultAdaptiveSafety K U) n t ↔
      t.1 ∈ K.safeFaces U n := by
  classical
  change (K.levelFaceCarrier t ⊆ U) ↔ _
  rw [safeFaces, Finset.mem_filter]
  constructor
  · intro ht
    refine ⟨t.2, ?_⟩
    intro x hx
    exact ht ⟨x, hx, rfl⟩
  · rintro ⟨-, ht⟩
    rintro z ⟨x, hx, rfl⟩
    exact ht x hx

/-- The chosen parent one level above an iterated midpoint face. -/
noncomputable def levelParentFace (n : ℕ) (t : K.LevelFace (n + 1)) : K.LevelFace n := by
  let R := K.safeSubdivision n
  change R.refined.midpointComplex.Face at t
  exact R.refined.midpointParentFace t

/-- Local attainability hypotheses for an adaptive safety rule.  The first field guarantees
coverage.  The second says that sufficiently fine children meeting a fixed neighborhood have a
safe parent; this is exactly the condition that makes first-safe faces locally finite. -/
class AdaptiveSafety.IsAdmissible [AdaptiveSafety K U] : Prop where
  exists_safe : IsOpen U → ∀ {p : K.realization}, p ∈ U →
    ∃ (n : ℕ) (t : K.LevelFace n),
      LevelFace.IsSafe K U t ∧ p ∈ K.levelFaceCarrier t
  locally_parent_safe : IsOpen U → ∀ p : U,
    ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ,
      ∀ n : ℕ, N ≤ n → ∀ t : K.LevelFace (n + 1),
        (K.levelFaceCarrier t ∩ Metric.ball p.1 (ε / 2)).Nonempty →
          LevelFace.IsSafe K U (K.levelParentFace n t)

/--
@isnad1 id=le.0h3v.s5.cb214f4f026f from=translated src=- shape=39927e76 vocab=ccd28c6a
-/
theorem levelFaceCarrier_subset_parent (n : ℕ) (t : K.LevelFace (n + 1)) :
    K.levelFaceCarrier t ⊆ K.levelFaceCarrier (K.levelParentFace n t) := by
  let R := K.safeSubdivision n
  change R.refined.midpointComplex.Face at t
  rintro z ⟨x, hx, rfl⟩
  let p : R.refined.realization := R.refined.midpointHomeomorph x
  refine ⟨p, ?_, rfl⟩
  exact R.refined.midpointEval_mem_parentFace
    (R.refined.midpointParentFace t) (R.refined.midpointFace_mem_parent t) x hx

/-- Every point of a level face lies in a child face at the next midpoint level whose entire
transported carrier remains in the parent carrier.
@isnad1 id=ex.1h4v.s6.80765d26b078 from=translated src=- shape=031c6349 vocab=24dca4ac
-/
theorem exists_levelFace_succ_containing {n : ℕ} (t : K.LevelFace n)
    {p : K.realization} (hp : p ∈ K.levelFaceCarrier t) :
    ∃ u : K.LevelFace (n + 1),
      p ∈ K.levelFaceCarrier u ∧
        K.levelFaceCarrier u ⊆ K.levelFaceCarrier t := by
  let R := K.safeSubdivision n
  obtain ⟨x, hxt, hxp⟩ := hp
  obtain ⟨y, s, hsOver, hys, heval⟩ :=
    R.refined.exists_midpoint_preimage_in_face t x hxt
  have hsFace : s ∈ R.refined.midpointComplex.faces := by
    change s ∈ R.refined.midpointFaces
    rw [IntrinsicTwoComplex.midpointFaces]
    exact Finset.mem_biUnion.mpr ⟨t, Finset.mem_univ _, hsOver⟩
  let u : K.LevelFace (n + 1) := by
    change R.refined.midpointComplex.Face
    exact ⟨s, hsFace⟩
  refine ⟨u, ?_, ?_⟩
  · refine ⟨y, hys, ?_⟩
    change R.homeo (R.refined.midpointHomeomorph y) = p
    rw [R.refined.midpointHomeomorph_apply]
    have hxy : R.refined.midpointEval y = x := Subtype.ext heval
    rw [hxy]
    exact hxp
  · rintro q ⟨z, hzu, rfl⟩
    let w : R.refined.realization := R.refined.midpointEval z
    refine ⟨w, ?_, rfl⟩
    exact R.refined.midpointEval_mem_parentFace t hsOver z hzu

/-- Containment in an open set is an admissible adaptive safety rule.
@isnad1 id=isadmiss.0h2v.s3.6b1aef0613fc from=translated src=- shape=8616cb4c vocab=55d210af
-/
instance (priority := 100) defaultAdaptiveSafety_admissible :
    @AdaptiveSafety.IsAdmissible K U (defaultAdaptiveSafety K U) := by
  refine { exists_safe := ?_, locally_parent_safe := ?_ }
  · intro hU p hp
    classical
    obtain ⟨n, hn⟩ := K.mem_safeStageSupport_of_mem U hU hp
    obtain ⟨x, hx⟩ := hn
    rcases x.2.2 with ⟨t, ht, hxt⟩
    let q : (K.safeSubdivision n).refined.realization :=
      (K.safeSubdivision n).refined.restrictFacesInclusion
        (fun s ↦ s ∈ K.safeFaces U n) x
    have htParts := (@Finset.mem_filter _ (fun t ↦ t ∈ K.safeFaces U n)
      (K.safeFacesDecidablePred U n) _ _).mp ht
    let T : K.LevelFace n := ⟨t, htParts.1⟩
    refine ⟨n, T, ?_, q, hxt, hx⟩
    change K.levelFaceCarrier T ⊆ U
    rintro z ⟨y, hy, rfl⟩
    exact (Finset.mem_filter.mp htParts.2).2 y hy
  · intro hU p
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU p.1 p.2
    have hε2 : 0 < ε / 2 := half_pos hε
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε2
      (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨ε, hε, N, ?_⟩
    intro n hNn t hinter
    change K.levelFaceCarrier (K.levelParentFace n t) ⊆ U
    obtain ⟨z, hzFace, hzBall⟩ := hinter
    have hzParent : z ∈ K.levelFaceCarrier (K.levelParentFace n t) :=
      K.levelFaceCarrier_subset_parent n t hzFace
    have hpow : (1 / 2 : ℝ) ^ n < ε / 2 := by
      exact (pow_le_pow_of_le_one (by norm_num) (by norm_num) hNn).trans_lt hN
    intro y hy
    apply hball
    rw [Metric.mem_ball]
    calc
      dist y p.1 ≤ dist y z + dist z p.1 := dist_triangle _ _ _
      _ ≤ (1 / 2 : ℝ) ^ n + dist z p.1 := by
        gcongr
        obtain ⟨y', hy', rfl⟩ := hy
        obtain ⟨z', hz', hz'eq⟩ := hzParent
        have hz'eq' : (K.safeSubdivision n).homeo z' = z := hz'eq
        rw [← hz'eq']
        exact K.iteratedMidpointSubdivision_meshLE n
          (K.levelParentFace n t).1 (K.levelParentFace n t).2 y' hy' z' hz'
      _ < ε / 2 + ε / 2 := add_lt_add hpow hzBall
      _ = ε := by ring

variable [AdaptiveSafety K U]

/-- Iterating the preceding child-cover lemma gives a face at every later level through a
chosen point, with carrier contained in the original face.
@isnad1 id=ex.1h5v.s6.82542edea0c1 from=translated src=- shape=cf2e4ec6 vocab=24dca4ac
-/
theorem exists_levelFace_add_containing (n k : ℕ) (t : K.LevelFace n)
    {p : K.realization} (hp : p ∈ K.levelFaceCarrier t) :
    ∃ u : K.LevelFace (n + k),
      p ∈ K.levelFaceCarrier u ∧
        K.levelFaceCarrier u ⊆ K.levelFaceCarrier t := by
  induction k with
  | zero => exact ⟨t, hp, Set.Subset.rfl⟩
  | succ k ih =>
      obtain ⟨s, hps, hst⟩ := ih
      obtain ⟨u, hpu, hus⟩ := K.exists_levelFace_succ_containing s hps
      have hcarrier : K.levelFaceCarrier u ⊆ K.levelFaceCarrier t := hus.trans hst
      simpa only [Nat.add_assoc] using ⟨u, hpu, hcarrier⟩

/-- A level face is exactly the union of its faces at any prescribed later midpoint level.
The descendant condition is stated geometrically, which avoids choosing a combinatorial parent
for faces meeting an old edge.
@isnad1 id=eq.0h4v.s6.7983cc8f0fa8 from=translated src=- shape=d7af7094 vocab=29cc0a04
-/
theorem levelFaceCarrier_eq_iUnion_descendants (n k : ℕ) (t : K.LevelFace n) :
    K.levelFaceCarrier t =
      ⋃ u : K.LevelFace (n + k),
        ⋃ (_ : K.levelFaceCarrier u ⊆ K.levelFaceCarrier t),
          K.levelFaceCarrier u := by
  apply Set.Subset.antisymm
  · intro p hp
    obtain ⟨u, hpu, hut⟩ := K.exists_levelFace_add_containing n k t hp
    exact Set.mem_iUnion.mpr ⟨u, Set.mem_iUnion.mpr ⟨hut, hpu⟩⟩
  · intro p hp
    obtain ⟨u, hp⟩ := Set.mem_iUnion.mp hp
    obtain ⟨hut, hpu⟩ := Set.mem_iUnion.mp hp
    exact hut hpu

/-- Exact intersection formula for two transported faces at the same midpoint level.
@isnad1 id=eq.0h4v.s9.67232f55409a from=translated src=- shape=dac1cf08 vocab=9d8f052c
-/
theorem levelFaceCarrier_inter {n : ℕ} (s t : K.LevelFace n) :
    K.levelFaceCarrier s ∩ K.levelFaceCarrier t =
      (K.safeSubdivision n).homeo ''
        (K.safeSubdivision n).refined.faceCarrier (s.1 ∩ t.1) := by
  rw [levelFaceCarrier, levelFaceCarrier,
    ← Set.image_inter (K.safeSubdivision n).homeo.injective,
    (K.safeSubdivision n).refined.faceCarrier_inter]

/-- Distinct maximal faces at one level share at most two vertices.
@isnad1 id=le.1h4v.s7.cf52fbb40e9b from=translated src=- shape=6b9754db vocab=598bc6bf
-/
theorem card_inter_levelFace_le_two {n : ℕ} {s t : K.LevelFace n}
    (hst : s ≠ t) : (s.1 ∩ t.1).card ≤ 2 := by
  by_contra hcard
  have hthree : (s.1 ∩ t.1).card = 3 := by
    have hle : (s.1 ∩ t.1).card ≤ s.1.card := Finset.card_le_card Finset.inter_subset_left
    rw [(K.safeSubdivision n).refined.faces_card s.1 s.2] at hle
    omega
  have hstSets : s.1 = t.1 := by
    have hleft : s.1 ∩ t.1 = s.1 :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by
        rw [(K.safeSubdivision n).refined.faces_card s.1 s.2, hthree])
    have hright : s.1 ∩ t.1 = t.1 :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by
        rw [(K.safeSubdivision n).refined.faces_card t.1 t.2, hthree])
    exact hleft.symm.trans hright
  exact hst (Subtype.ext hstSets)

/-- A barycentric realization point supported on one face vertex is that face's canonical
vertex point. -/
theorem eq_facePoint_of_mem_faceCarrier_singleton (t : K.Face)
    (v : {v // v ∈ t.1}) (x : K.realization)
    (hx : x ∈ K.faceCarrier ({v.1} : Finset K.Vertex)) :
    x = K.facePoint t v := by
  have hxv : x.1 v.1 = 1 := by
    have hsum := x.2.1.2
    rw [Finset.sum_eq_single v.1] at hsum
    · exact hsum
    · intro w _ hwv
      exact hx w (by simp [hwv])
    · intro hv
      exact False.elim (hv (Finset.mem_univ v.1))
  apply Subtype.ext
  funext w
  by_cases hwv : w = v.1
  · subst w
    rw [K.facePoint_val]
    simp [hxv]
  · rw [K.facePoint_val]
    simp [hwv, hx w (by simp [hwv])]

/-- Two two-vertex subfaces of a triangle which share a nonvertex point are equal. -/
theorem eq_of_card_two_of_mem_faceCarriers_not_vertex (t : K.Face)
    {e d : Finset K.Vertex} (het : e ⊆ t.1) (_ : d ⊆ t.1)
    (hecard : e.card = 2) (hdcard : d.card = 2)
    {x : K.realization} (hxe : x ∈ K.faceCarrier e)
    (hxd : x ∈ K.faceCarrier d)
    (hxNot : ∀ v : {v // v ∈ t.1}, x ≠ K.facePoint t v) :
    e = d := by
  by_contra hed
  have hinterLe : (e ∩ d).card ≤ 1 := by
    by_contra hnot
    have hinterTwo : (e ∩ d).card = 2 := by
      have hle : (e ∩ d).card ≤ e.card :=
        Finset.card_le_card Finset.inter_subset_left
      omega
    have hinterE : e ∩ d = e :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by
        rw [hecard, hinterTwo])
    have hinterD : e ∩ d = d :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by
        rw [hdcard, hinterTwo])
    exact hed (hinterE.symm.trans hinterD)
  have hxinter : x ∈ K.faceCarrier (e ∩ d) := by
    rw [← K.faceCarrier_inter e d]
    exact ⟨hxe, hxd⟩
  have hinterNonempty : (e ∩ d).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    rw [hempty, K.faceCarrier_empty] at hxinter
    exact hxinter
  have hinterOne : (e ∩ d).card = 1 := by
    have := Finset.card_pos.mpr hinterNonempty
    omega
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hinterOne
  have hvt : v ∈ t.1 := het (Finset.inter_subset_left (by
    rw [hv]
    exact Finset.mem_singleton_self v))
  apply hxNot ⟨v, hvt⟩
  apply K.eq_facePoint_of_mem_faceCarrier_singleton t ⟨v, hvt⟩ x
  rwa [hv] at hxinter

/--
@isnad1 id=issafe.1h4v.s5.8f5af102d499 from=translated src=- shape=0539bf36 vocab=569552cc
-/
theorem LevelFace.IsSafe.child {n : ℕ} {t : K.LevelFace (n + 1)}
    (ht : LevelFace.IsSafe K U (K.levelParentFace n t)) :
    LevelFace.IsSafe K U t := by
  exact AdaptiveSafety.hereditary (K := K) (U := U)
    (K.levelFaceCarrier_subset_parent n t) ht

/-- Relative interior of a transported level face, expressed by positive barycentric
coordinates on all three face vertices. -/
def levelFaceRelInterior {n : ℕ} (t : K.LevelFace n) : Set K.realization :=
  (K.safeSubdivision n).homeo ''
    {x : (K.safeSubdivision n).refined.realization |
      x ∈ (K.safeSubdivision n).refined.faceCarrier t.1 ∧
        ∀ v ∈ t.1, 0 < x.1 v}

/--
@isnad1 id=le.0h3v.s4.5505afa0f813 from=translated src=- shape=2aafe9bb vocab=0d6152a5
-/
theorem levelFaceRelInterior_subset_carrier {n : ℕ} (t : K.LevelFace n) :
    K.levelFaceRelInterior t ⊆ K.levelFaceCarrier t := by
  rintro z ⟨x, hx, rfl⟩
  exact ⟨x, hx.1, rfl⟩

/-- Midpoint subdivision sends a child's relative interior into its parent's relative
interior.
@isnad1 id=le.0h3v.s5.dc56089921f1 from=translated src=- shape=39927e76 vocab=50d632c8
-/
theorem levelFaceRelInterior_subset_parent (n : ℕ) (t : K.LevelFace (n + 1)) :
    K.levelFaceRelInterior t ⊆
      K.levelFaceRelInterior (K.levelParentFace n t) := by
  let R := K.safeSubdivision n
  change R.refined.midpointComplex.Face at t
  rintro z ⟨x, hx, rfl⟩
  let p : R.refined.realization := R.refined.midpointHomeomorph x
  refine ⟨p, ⟨?_, ?_⟩, rfl⟩
  · exact R.refined.midpointEval_mem_parentFace
      (R.refined.midpointParentFace t) (R.refined.midpointFace_mem_parent t) x hx.1
  · intro v hv
    exact R.refined.midpointEvalAffine_pos_on_parent
      (R.refined.midpointParentFace t) (R.refined.midpointFace_mem_parent t)
      hx.1 x.2.1.1 hx.2 hv

/-- At a fixed midpoint level, the relative interior of one maximal face misses the carrier of
every distinct maximal face.
@isnad1 id=disjoint.1h4v.s6.2a24cf88b66c from=translated src=- shape=3673dad7 vocab=338b94ce
-/
theorem disjoint_levelFaceRelInterior_levelFaceCarrier {n : ℕ}
    {t u : K.LevelFace n} (htu : t ≠ u) :
    Disjoint (K.levelFaceRelInterior t) (K.levelFaceCarrier u) := by
  rw [Set.disjoint_left]
  rintro z ⟨x, hx, rfl⟩ ⟨y, hy, hyx⟩
  have hxy : x = y := (K.safeSubdivision n).homeo.injective hyx.symm
  have hnsub : ¬t.1 ⊆ u.1 := by
    intro hsub
    apply htu
    apply Subtype.ext
    exact Finset.eq_of_subset_of_card_le hsub (by
      rw [(K.safeSubdivision n).refined.faces_card t.1 t.2,
        (K.safeSubdivision n).refined.faces_card u.1 u.2])
  obtain ⟨v, hvt, hvu⟩ := Finset.not_subset.mp hnsub
  have hyzero : y.1 v = 0 := hy v hvu
  have hcoord : x.1 v = y.1 v := congrFun (congrArg Subtype.val hxy) v
  linarith [hx.2 v hvt]

/-- The ancestor at level `n` of a face at level `n + k`. -/
noncomputable def levelAncestor (n : ℕ) :
    (k : ℕ) → K.LevelFace (n + k) → K.LevelFace n
  | 0, t => t
  | k + 1, t => levelAncestor n k (K.levelParentFace (n + k) t)

/--
@isnad1 id=eq.0h3v.s4.45c3b6ebedfd from=translated src=- shape=e7a010f6 vocab=fcf2708e
-/
@[simp] theorem levelAncestor_zero (n : ℕ) (t : K.LevelFace n) :
    K.levelAncestor n 0 t = t := rfl

/--
@isnad1 id=eq.0h4v.s6.694a09b3558f from=translated src=- shape=7d848bfd vocab=a9b96c54
-/
@[simp] theorem levelAncestor_succ (n k : ℕ) (t : K.LevelFace (n + (k + 1))) :
    K.levelAncestor n (k + 1) t =
      K.levelAncestor n k (K.levelParentFace (n + k) t) := rfl

/--
@isnad1 id=le.0h4v.s5.464016345d39 from=translated src=- shape=e8df0ed4 vocab=2a8a90a3
-/
theorem levelFaceCarrier_subset_ancestor (n k : ℕ)
    (t : K.LevelFace (n + k)) :
    K.levelFaceCarrier t ⊆ K.levelFaceCarrier (K.levelAncestor n k t) := by
  induction k with
  | zero => exact Set.Subset.rfl
  | succ k ih =>
      exact (K.levelFaceCarrier_subset_parent (n + k) t).trans
        (ih (K.levelParentFace (n + k) t))

/--
@isnad1 id=le.0h4v.s5.2f705fed6501 from=translated src=- shape=e8df0ed4 vocab=4bb963e6
-/
theorem levelFaceRelInterior_subset_ancestor (n k : ℕ)
    (t : K.LevelFace (n + k)) :
    K.levelFaceRelInterior t ⊆ K.levelFaceRelInterior (K.levelAncestor n k t) := by
  induction k with
  | zero => exact Set.Subset.rfl
  | succ k ih =>
      exact (K.levelFaceRelInterior_subset_parent (n + k) t).trans
        (ih (K.levelParentFace (n + k) t))

/--
@isnad1 id=issafe.1h5v.s5.e23bfa2e7f1c from=translated src=- shape=e96cceea vocab=28c1f280
-/
theorem LevelFace.IsSafe.ancestor_child {n k : ℕ} {t : K.LevelFace (n + k)}
    (ht : LevelFace.IsSafe K U (K.levelAncestor n k t)) :
    LevelFace.IsSafe K U t := by
  exact AdaptiveSafety.hereditary (K := K) (U := U)
    (K.levelFaceCarrier_subset_ancestor n k t) ht

/-- A first-safe face is safe, but at a positive level its chosen parent is not safe. -/
def LevelFace.IsFirstSafe : {n : ℕ} → K.LevelFace n → Prop
  | 0, t => LevelFace.IsSafe K U t
  | n + 1, t => LevelFace.IsSafe K U t ∧
      ¬LevelFace.IsSafe K U (K.levelParentFace n t)

/--
@isnad1 id=issafe.1h4v.s4.44e189115c16 from=translated src=- shape=d7befe20 vocab=9a83000d
-/
theorem LevelFace.IsFirstSafe.safe {n : ℕ} {t : K.LevelFace n}
    (ht : LevelFace.IsFirstSafe K U t) : LevelFace.IsSafe K U t := by
  cases n with
  | zero => exact ht
  | succ _ => exact ht.1

/-- A later first-safe face cannot meet the relative interior of an earlier first-safe face.
If its ancestor were the earlier face, that safe ancestor would make its immediate parent safe;
otherwise the fixed-level face-to-face property separates them.
@isnad1 id=disjoint.2h6v.s7.586946559226 from=translated src=- shape=af145f78 vocab=ee904b48
-/
theorem disjoint_firstSafeRelInterior_laterCarrier {n k : ℕ}
    {t : K.LevelFace n} {u : K.LevelFace (n + (k + 1))}
    (ht : LevelFace.IsFirstSafe K U t)
    (hu : LevelFace.IsFirstSafe K U u) :
    Disjoint (K.levelFaceRelInterior t) (K.levelFaceCarrier u) := by
  let p := K.levelParentFace (n + k) u
  by_cases hancestor : K.levelAncestor n k p = t
  · have hpSafe : LevelFace.IsSafe K U p := by
      apply LevelFace.IsSafe.ancestor_child K U
      rw [hancestor]
      exact ht.safe
    exact False.elim (hu.2 hpSafe)
  · exact (K.disjoint_levelFaceRelInterior_levelFaceCarrier
      (fun h ↦ hancestor h.symm)).mono_right
      (K.levelFaceCarrier_subset_ancestor n (k + 1) u)

/-- The relative interior of a later first-safe face also misses the entire earlier carrier.
@isnad1 id=disjoint.2h6v.s7.5f1c1cde6ad4 from=translated src=- shape=6988f316 vocab=ee904b48
-/
theorem disjoint_laterFirstSafeRelInterior_firstSafeCarrier {n k : ℕ}
    {t : K.LevelFace n} {u : K.LevelFace (n + (k + 1))}
    (ht : LevelFace.IsFirstSafe K U t)
    (hu : LevelFace.IsFirstSafe K U u) :
    Disjoint (K.levelFaceRelInterior u) (K.levelFaceCarrier t) := by
  let p := K.levelParentFace (n + k) u
  by_cases hancestor : K.levelAncestor n k p = t
  · have hpSafe : LevelFace.IsSafe K U p := by
      apply LevelFace.IsSafe.ancestor_child K U
      rw [hancestor]
      exact ht.safe
    exact False.elim (hu.2 hpSafe)
  · exact (K.disjoint_levelFaceRelInterior_levelFaceCarrier hancestor).mono_left
      (K.levelFaceRelInterior_subset_ancestor n (k + 1) u)

/--
@isnad1 id=isfirsts.3h5v.s6.29a948328bc5 from=translated src=- shape=7b5a282c vocab=6c950f63
-/
theorem LevelFace.isFirstSafe_of_minimal {n : ℕ} (t : K.LevelFace n)
    {p : K.realization} (hsafe : LevelFace.IsSafe K U t)
    (hp : p ∈ K.levelFaceCarrier t)
    (hminimal : ∀ m < n, ¬∃ u : K.LevelFace m,
      LevelFace.IsSafe K U u ∧ p ∈ K.levelFaceCarrier u) :
    LevelFace.IsFirstSafe K U t := by
  cases n with
  | zero => exact hsafe
  | succ m =>
      refine ⟨hsafe, ?_⟩
      intro hparent
      apply hminimal m (Nat.lt_succ_self m)
      exact ⟨K.levelParentFace m t, hparent,
        K.levelFaceCarrier_subset_parent m t hp⟩

/-- The countable type of first-safe adaptive triangles. -/
abbrev AdaptiveFace (K : IntrinsicTwoComplex) (U : Set K.realization)
    [AdaptiveSafety K U] :=
  Σ n : ℕ, {t : K.LevelFace n // LevelFace.IsFirstSafe K U t}

/-- One common midpoint level dominating a finite family of adaptive tiles. -/
noncomputable def adaptiveFaceCommonLevel
    (F : Finset (K.AdaptiveFace U)) : ℕ :=
  F.sup fun t ↦ t.1

/--
@isnad1 id=le.1h4v.s6.d3c409e63ad2 from=translated src=- shape=13bae3e4 vocab=42ebac09
-/
theorem adaptiveFace_level_le_commonLevel
    (F : Finset (K.AdaptiveFace U)) {t : K.AdaptiveFace U} (ht : t ∈ F) :
    t.1 ≤ K.adaptiveFaceCommonLevel U F := by
  exact Finset.le_sup (f := fun u : K.AdaptiveFace U ↦ u.1) ht

/-- Carrier of one adaptive triangle in the original realization. -/
def adaptiveFaceCarrier (t : K.AdaptiveFace U) : Set K.realization :=
  K.levelFaceCarrier t.2.1

/-- Every tile in a finite adaptive family is a union of faces of the family's common midpoint
level.  This is the finite source-subcomplex reduction used in the Radó crossing weld.
@isnad1 id=eq.1h4v.s7.62d22c10ef30 from=translated src=- shape=818752fd vocab=ebb51783
-/
theorem adaptiveFaceCarrier_eq_iUnion_commonLevel_descendants
    (F : Finset (K.AdaptiveFace U)) {t : K.AdaptiveFace U} (ht : t ∈ F) :
    K.adaptiveFaceCarrier U t =
      ⋃ u : K.LevelFace (K.adaptiveFaceCommonLevel U F),
        ⋃ (_ : K.levelFaceCarrier u ⊆ K.adaptiveFaceCarrier U t),
          K.levelFaceCarrier u := by
  have hle := K.adaptiveFace_level_le_commonLevel U F ht
  have h := K.levelFaceCarrier_eq_iUnion_descendants t.1
    (K.adaptiveFaceCommonLevel U F - t.1) t.2.1
  rw [Nat.add_sub_of_le hle] at h
  exact h

/--
@isnad1 id=le.0h3v.s4.b2853e7ad313 from=translated src=- shape=1ffd1eaf vocab=44b077c3
-/
theorem adaptiveFaceCarrier_subset (t : K.AdaptiveFace U) :
    K.adaptiveFaceCarrier U t ⊆ U := by
  rcases t with ⟨(_ | n), t⟩
  · exact AdaptiveSafety.carrier_subset (K := K) (U := U) t.2
  · exact AdaptiveSafety.carrier_subset (K := K) (U := U) t.2.1

/-- Relative interior of one adaptive face. -/
def adaptiveFaceRelInterior (t : K.AdaptiveFace U) : Set K.realization :=
  K.levelFaceRelInterior t.2.1

/-- Distinct first-safe adaptive faces meet only on their relative boundaries.
@isnad1 id=disjoint.1h4v.s6.30f7f84d4087 from=translated src=- shape=b2c7811e vocab=220baed4
-/
theorem disjoint_adaptiveFaceRelInterior_carrier
    {s t : K.AdaptiveFace U} (hst : s ≠ t) :
    Disjoint (K.adaptiveFaceRelInterior U s) (K.adaptiveFaceCarrier U t) := by
  rcases s with ⟨n, s⟩
  rcases t with ⟨m, t⟩
  rcases lt_trichotomy n m with hnm | hnm | hmn
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hnm
    have hmk : m = n + (k + 1) := by omega
    subst m
    exact K.disjoint_firstSafeRelInterior_laterCarrier U s.2 t.2
  · subst m
    have hfaces : s.1 ≠ t.1 := by
      intro hfaces
      apply hst
      apply Sigma.ext
      · rfl
      · exact heq_of_eq (Subtype.ext hfaces)
    exact K.disjoint_levelFaceRelInterior_levelFaceCarrier hfaces
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hmn
    have hnk : n = m + (k + 1) := by omega
    subst n
    exact K.disjoint_laterFirstSafeRelInterior_firstSafeCarrier U t.2 s.2

variable [AdaptiveSafety.IsAdmissible (K := K) (U := U)]

/-- Some safe level face contains every point of the open set.
@isnad1 id=ex.2h3v.s6.4434809fc2c8 from=translated src=- shape=a6c07fe0 vocab=cf7426da
-/
theorem exists_safeLevelFace_containing (hU : IsOpen U)
    {p : K.realization} (hp : p ∈ U) :
    ∃ (n : ℕ) (t : K.LevelFace n),
      LevelFace.IsSafe K U t ∧ p ∈ K.levelFaceCarrier t := by
  exact AdaptiveSafety.IsAdmissible.exists_safe (K := K) (U := U) hU hp

/-- The least midpoint level at which a safe face carries `p`. -/
noncomputable def firstSafeLevel (hU : IsOpen U) (p : U) : ℕ :=
  by
    classical
    exact Nat.find (K.exists_safeLevelFace_containing U hU p.2)

/--
@isnad1 id=ex.1h3v.s7.6441d6d8cef4 from=translated src=- shape=a484de16 vocab=a96a5ba8
-/
theorem exists_firstSafeLevelFace (hU : IsOpen U) (p : U) :
    ∃ t : K.LevelFace (K.firstSafeLevel U hU p),
      LevelFace.IsSafe K U t ∧ p.1 ∈ K.levelFaceCarrier t :=
  by
    classical
    exact Nat.find_spec (K.exists_safeLevelFace_containing U hU p.2)

/-- A chosen least-level safe face through `p`. -/
noncomputable def firstSafeFace (hU : IsOpen U) (p : U) :
    K.LevelFace (K.firstSafeLevel U hU p) :=
  Classical.choose (K.exists_firstSafeLevelFace U hU p)

/--
@isnad1 id=issafe.1h3v.s6.9b4e3c286c9d from=translated src=- shape=933835d3 vocab=7d4c2862
-/
theorem firstSafeFace_isSafe (hU : IsOpen U) (p : U) :
    LevelFace.IsSafe K U (K.firstSafeFace U hU p) :=
  (Classical.choose_spec (K.exists_firstSafeLevelFace U hU p)).1

/--
@isnad1 id=mem.1h3v.s6.e1ff601c2481 from=translated src=- shape=a401cdaa vocab=558df7cf
-/
theorem mem_firstSafeFaceCarrier (hU : IsOpen U) (p : U) :
    p.1 ∈ K.levelFaceCarrier (K.firstSafeFace U hU p) :=
  (Classical.choose_spec (K.exists_firstSafeLevelFace U hU p)).2

/--
@isnad1 id=isfirsts.1h3v.s6.b1bce7228a1b from=translated src=- shape=933835d3 vocab=9dd78640
-/
theorem firstSafeFace_isFirstSafe (hU : IsOpen U) (p : U) :
    LevelFace.IsFirstSafe K U (K.firstSafeFace U hU p) := by
  classical
  have hsafe := K.firstSafeFace_isSafe U hU p
  have hpface := K.mem_firstSafeFaceCarrier U hU p
  apply LevelFace.isFirstSafe_of_minimal K U _ hsafe hpface
  intro m hm
  exact Nat.find_min (K.exists_safeLevelFace_containing U hU p.2) hm

/-- The first-safe adaptive triangles cover the whole open set.
@isnad1 id=eq.1h2v.s6.56cdf9abde8b from=translated src=- shape=0fdffca6 vocab=1a2f93cc
-/
theorem iUnion_adaptiveFaceCarrier (hU : IsOpen U) :
    (⋃ t : K.AdaptiveFace U, K.adaptiveFaceCarrier U t) = U := by
  apply Set.Subset.antisymm
  · intro p hp
    obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hp
    exact K.adaptiveFaceCarrier_subset U t ht
  · intro p hp
    let q : U := ⟨p, hp⟩
    let t : K.AdaptiveFace U :=
      ⟨K.firstSafeLevel U hU q,
        ⟨K.firstSafeFace U hU q, K.firstSafeFace_isFirstSafe U hU q⟩⟩
    exact Set.mem_iUnion.mpr ⟨t, K.mem_firstSafeFaceCarrier U hU q⟩

/-- The transported diameter of every level-`n` face is at most `2⁻ⁿ`.
@isnad1 id=le.2h5v.s7.5d0d98e5111f from=translated src=- shape=e763282b vocab=425a790f
-/
theorem dist_le_pow_of_mem_levelFaceCarrier {n : ℕ} (t : K.LevelFace n)
    {x y : K.realization} (hx : x ∈ K.levelFaceCarrier t)
    (hy : y ∈ K.levelFaceCarrier t) :
    dist x y ≤ (1 / 2 : ℝ) ^ n := by
  obtain ⟨x', hx', rfl⟩ := hx
  obtain ⟨y', hy', rfl⟩ := hy
  exact K.iteratedMidpointSubdivision_meshLE n t.1 t.2 x' hx' y' hy'

omit [AdaptiveSafety K U] in
/-- If a child face meets a half-radius ball and its parent mesh is below that half-radius,
then the parent is already safe.
@isnad1 id=issafe.4h6v.s8.2f40e4d286aa from=translated src=- shape=92339e02 vocab=fcf6ca48
-/
theorem parent_isSafe_of_inter_ball {n : ℕ} (t : K.LevelFace (n + 1))
    {p : K.realization} {ε : ℝ} (_ : 0 < ε)
    (hball : Metric.ball p ε ⊆ U)
    (hmesh : (1 / 2 : ℝ) ^ n < ε / 2)
    (hinter : (K.levelFaceCarrier t ∩ Metric.ball p (ε / 2)).Nonempty) :
    @LevelFace.IsSafe K U (defaultAdaptiveSafety K U) n
      (K.levelParentFace n t) := by
  obtain ⟨z, hzFace, hzBall⟩ := hinter
  have hzParent : z ∈ K.levelFaceCarrier (K.levelParentFace n t) :=
    K.levelFaceCarrier_subset_parent n t hzFace
  intro y hy
  apply hball
  rw [Metric.mem_ball]
  calc
    dist y p ≤ dist y z + dist z p := dist_triangle _ _ _
    _ ≤ (1 / 2 : ℝ) ^ n + dist z p :=
      add_le_add (K.dist_le_pow_of_mem_levelFaceCarrier
        (K.levelParentFace n t) hy hzParent) le_rfl
    _ < ε / 2 + ε / 2 := add_lt_add hmesh hzBall
    _ = ε := by ring

omit [AdaptiveSafety.IsAdmissible K U] in
/-- Only finitely many adaptive faces occur below a fixed midpoint level.
@isnad1 id=finite.0h3v.s5.e8cedf057855 from=translated src=- shape=025d7c7c vocab=9b6b1400
-/
theorem finite_adaptiveFace_level_lt (N : ℕ) :
    {t : K.AdaptiveFace U | t.1 < N}.Finite := by
  classical
  let encode : {t : K.AdaptiveFace U // t.1 < N} →
      Σ i : Fin N, K.LevelFace i.1 :=
    fun t ↦ ⟨⟨t.1.1, t.2⟩, t.1.2.1⟩
  have hencode : Function.Injective encode := by
    rintro ⟨⟨sn, s⟩, hs⟩ ⟨⟨tn, t⟩, ht⟩ hst
    dsimp only [encode] at hst
    have hnFin : (⟨sn, hs⟩ : Fin N) = ⟨tn, ht⟩ :=
      (Sigma.mk.inj_iff.mp hst).1
    have hn : sn = tn := congrArg (fun i : Fin N ↦ (i : ℕ)) hnFin
    subst tn
    have hface : s = t := Subtype.ext (eq_of_heq (Sigma.mk.inj_iff.mp hst).2)
    subst t
    rfl
  let : Finite {t : K.AdaptiveFace U // t.1 < N} :=
    Finite.of_injective encode hencode
  exact Set.finite_coe_iff.mp
    (show Finite {t : K.AdaptiveFace U // t.1 < N} from inferInstance)

/-- Carrier of an adaptive face in the open subspace itself. -/
def adaptiveFaceCarrierInOpen (t : K.AdaptiveFace U) : Set U :=
  Subtype.val ⁻¹' K.adaptiveFaceCarrier U t

/-- The first-safe adaptive triangle family is locally finite in the open set.
@isnad1 id=locallyf.1h2v.s7.ea9526395193 from=translated src=- shape=796a03f6 vocab=047eb0b7
-/
theorem locallyFinite_adaptiveFaceCarrierInOpen (hU : IsOpen U) :
    LocallyFinite (K.adaptiveFaceCarrierInOpen U) := by
  classical
  intro p
  obtain ⟨ε, hε, N, hparent⟩ :=
    AdaptiveSafety.IsAdmissible.locally_parent_safe (K := K) (U := U) hU p
  have hε2 : 0 < ε / 2 := half_pos hε
  let V : Set U := Subtype.val ⁻¹' Metric.ball p.1 (ε / 2)
  refine ⟨V, ?_, ?_⟩
  · exact (Metric.isOpen_ball.preimage continuous_subtype_val).mem_nhds
      (Metric.mem_ball_self hε2)
  · apply (K.finite_adaptiveFace_level_lt U (N + 1)).subset
    intro t ht
    simp only [Set.mem_ofPred_eq]
    by_contra hlevel
    have hNlevel : N + 1 ≤ t.1 := Nat.le_of_not_gt hlevel
    rcases t with ⟨(_ | n), t⟩
    · change N + 1 ≤ 0 at hNlevel
      omega
    · change N + 1 ≤ n + 1 at hNlevel
      have hNn : N ≤ n := by omega
      obtain ⟨q, hqFace, hqV⟩ := ht
      have hinter :
          (K.levelFaceCarrier t.1 ∩ Metric.ball p.1 (ε / 2)).Nonempty :=
        ⟨q.1, hqFace, hqV⟩
      exact t.2.2 (hparent n hNn t.1 hinter)

/-! ## Finite boundary data on each adaptive tile -/

/-- The geometric point represented by one vertex of a level face. -/
noncomputable def levelFaceVertexPoint {n : ℕ} (t : K.LevelFace n)
    (v : {v // v ∈ t.1}) : K.realization :=
  (K.safeSubdivision n).homeo
    ((K.safeSubdivision n).refined.facePoint t v)

/--
@isnad1 id=mem.0h4v.s7.70022aa329f5 from=translated src=- shape=107f67a2 vocab=2cac26c2
-/
theorem levelFaceVertexPoint_mem_carrier {n : ℕ} (t : K.LevelFace n)
    (v : {v // v ∈ t.1}) :
    K.levelFaceVertexPoint t v ∈ K.levelFaceCarrier t :=
  ⟨(K.safeSubdivision n).refined.facePoint t v,
    (K.safeSubdivision n).refined.facePoint_mem_faceCarrier t v, rfl⟩

/-- A vertex occurrence on an adaptive tile.  Geometrically equal occurrences on adjacent
tiles are deliberately not quotiented here; `boundaryVertices` takes their finite image as
actual points. -/
abbrev AdaptiveVertexOccurrence (t : K.AdaptiveFace U) :=
  {v // v ∈ t.2.1.1}

/-- The `adaptiveVertexPoint` declaration. -/
noncomputable def adaptiveVertexPoint (t : K.AdaptiveFace U)
    (v : K.AdaptiveVertexOccurrence U t) : K.realization :=
  K.levelFaceVertexPoint t.2.1 v

omit [AdaptiveSafety.IsAdmissible K U] in
/--
@isnad1 id=mem.0h4v.s5.b92460aed80f from=translated src=- shape=81dfe8c0 vocab=e324f2a3
-/
theorem adaptiveVertexPoint_mem_carrier (t : K.AdaptiveFace U)
    (v : K.AdaptiveVertexOccurrence U t) :
    K.adaptiveVertexPoint U t v ∈ K.adaptiveFaceCarrier U t :=
  K.levelFaceVertexPoint_mem_carrier t.2.1 v

omit [AdaptiveSafety.IsAdmissible K U] in
/--
@isnad1 id=iscompac.0h3v.s6.6c70e7e17dcd from=translated src=- shape=e5ef9738 vocab=c34d45d5
-/
theorem isCompact_adaptiveFaceCarrierInOpen (t : K.AdaptiveFace U) :
    IsCompact (K.adaptiveFaceCarrierInOpen U t) := by
  let e : {x // x ∈ K.adaptiveFaceCarrier U t} → U :=
    fun x ↦ ⟨x.1, K.adaptiveFaceCarrier_subset U t x.2⟩
  have he : Continuous e := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  have hrange : Set.range e = K.adaptiveFaceCarrierInOpen U t := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x.1, hx⟩, Subtype.ext rfl⟩
  rw [← hrange]
  let : CompactSpace {x // x ∈ K.adaptiveFaceCarrier U t} :=
    isCompact_iff_compactSpace.mp (K.isCompact_levelFaceCarrier t.2.1)
  exact isCompact_range he

/-- Adaptive tiles touching a fixed tile. -/
def TouchingFace (t : K.AdaptiveFace U) :=
  {u : K.AdaptiveFace U //
    (K.adaptiveFaceCarrierInOpen U u ∩ K.adaptiveFaceCarrierInOpen U t).Nonempty}

/--
@isnad1 id=finite.1h3v.s6.c347e0656e6e from=translated src=- shape=672f23aa vocab=2c7459c2
-/
theorem finite_touchingFace (hU : IsOpen U) (t : K.AdaptiveFace U) :
    Finite (K.TouchingFace U t) := by
  exact Set.finite_coe_iff.mpr
    ((K.locallyFinite_adaptiveFaceCarrierInOpen U hU).finite_nonempty_inter_compact
      (K.isCompact_adaptiveFaceCarrierInOpen U t))

/-- Every tile touches itself. -/
noncomputable def selfTouchingFace (t : K.AdaptiveFace U) : K.TouchingFace U t := by
  refine ⟨t, ?_⟩
  obtain ⟨v, hv⟩ : t.2.1.1.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have := (K.safeSubdivision t.1).refined.faces_card t.2.1.1 t.2.1.2
    rw [hempty] at this
    simp at this
  let p := K.adaptiveVertexPoint U t ⟨v, hv⟩
  have hp : p ∈ K.adaptiveFaceCarrier U t :=
    K.adaptiveVertexPoint_mem_carrier U t ⟨v, hv⟩
  exact ⟨⟨p, K.adaptiveFaceCarrier_subset U t hp⟩, hp, hp⟩

/-- All vertex occurrences belonging to tiles which touch `t`. -/
abbrev TouchingVertexOccurrence (t : K.AdaptiveFace U) :=
  Σ u : K.TouchingFace U t, K.AdaptiveVertexOccurrence U u.1

/-- The finite set of all touching-tile vertices which lie in `t`.  It contains the original
three corners of `t` and every hanging midpoint introduced by a finer neighboring tile. -/
noncomputable def boundaryVertices (hU : IsOpen U) (t : K.AdaptiveFace U) :
    Finset K.realization := by
  classical
  letI : Finite (K.TouchingFace U t) := K.finite_touchingFace U hU t
  letI : Fintype (K.TouchingFace U t) := Fintype.ofFinite _
  let point : K.TouchingVertexOccurrence U t → K.realization :=
    fun v ↦ K.adaptiveVertexPoint U v.1.1 v.2
  exact (Finset.univ.image point).filter fun p ↦ p ∈ K.adaptiveFaceCarrier U t

/--
@isnad1 id=iff.1h4v.s8.f059cca95e03 from=translated src=- shape=3048f62c vocab=aae49245
-/
theorem mem_boundaryVertices_iff (hU : IsOpen U) (t : K.AdaptiveFace U)
    (p : K.realization) :
    p ∈ K.boundaryVertices U hU t ↔
      p ∈ K.adaptiveFaceCarrier U t ∧
        ∃ (u : K.TouchingFace U t) (v : K.AdaptiveVertexOccurrence U u.1),
          K.adaptiveVertexPoint U u.1 v = p := by
  classical
  let : Finite (K.TouchingFace U t) := K.finite_touchingFace U hU t
  let : Fintype (K.TouchingFace U t) := Fintype.ofFinite _
  simp only [boundaryVertices, Finset.mem_filter, Finset.mem_image, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨⟨v, rfl⟩, hp⟩
    exact ⟨hp, v.1, v.2, rfl⟩
  · rintro ⟨hp, u, v, rfl⟩
    exact ⟨⟨⟨u, v⟩, rfl⟩, hp⟩

/-- On the overlap of two adaptive tiles, their finite sets of collected boundary marks agree
pointwise.  Indeed a vertex occurrence whose tile touches one of the two tiles at the shared
point also touches the other there.
@isnad1 id=iff.3h5v.s7.31b139b077f4 from=translated src=- shape=575dd26d vocab=e8196979
-/
theorem mem_boundaryVertices_iff_of_mem_adaptiveFaceCarrier_inter
    (hU : IsOpen U) (s t : K.AdaptiveFace U) {p : K.realization}
    (hps : p ∈ K.adaptiveFaceCarrier U s)
    (hpt : p ∈ K.adaptiveFaceCarrier U t) :
    p ∈ K.boundaryVertices U hU s ↔
      p ∈ K.boundaryVertices U hU t := by
  constructor
  · intro hp
    obtain ⟨-, u, v, huv⟩ := (K.mem_boundaryVertices_iff U hU s p).mp hp
    rw [K.mem_boundaryVertices_iff U hU t p]
    refine ⟨hpt, ⟨u.1, ?_⟩, v, huv⟩
    let q : U := ⟨p, K.adaptiveFaceCarrier_subset U t hpt⟩
    refine ⟨q, ?_, hpt⟩
    change p ∈ K.adaptiveFaceCarrier U u.1
    rw [← huv]
    exact K.adaptiveVertexPoint_mem_carrier U u.1 v
  · intro hp
    obtain ⟨-, u, v, huv⟩ := (K.mem_boundaryVertices_iff U hU t p).mp hp
    rw [K.mem_boundaryVertices_iff U hU s p]
    refine ⟨hps, ⟨u.1, ?_⟩, v, huv⟩
    let q : U := ⟨p, K.adaptiveFaceCarrier_subset U s hps⟩
    refine ⟨q, ?_, hps⟩
    change p ∈ K.adaptiveFaceCarrier U u.1
    rw [← huv]
    exact K.adaptiveVertexPoint_mem_carrier U u.1 v

omit [AdaptiveSafety.IsAdmissible K U] in
/-- Distinct first-safe tiles meet only in the relative boundary of each tile.
@isnad1 id=le.1h4v.s6.80856bdff7c4 from=translated src=- shape=0fa53720 vocab=900d1347
-/
theorem adaptiveFaceCarrier_inter_subset_relativeBoundaries
    {s t : K.AdaptiveFace U} (hst : s ≠ t) :
    K.adaptiveFaceCarrier U s ∩ K.adaptiveFaceCarrier U t ⊆
      (K.adaptiveFaceCarrier U s \ K.adaptiveFaceRelInterior U s) ∩
        (K.adaptiveFaceCarrier U t \ K.adaptiveFaceRelInterior U t) := by
  rintro p ⟨hps, hpt⟩
  refine ⟨⟨hps, ?_⟩, hpt, ?_⟩
  · exact fun hpInt ↦ Set.disjoint_left.mp
      (K.disjoint_adaptiveFaceRelInterior_carrier U hst) hpInt hpt
  · exact fun hpInt ↦ Set.disjoint_left.mp
      (K.disjoint_adaptiveFaceRelInterior_carrier U (fun h ↦ hst h.symm)) hpInt hps

/--
@isnad1 id=not.0h4v.s7.022b22c29835 from=translated src=- shape=6b23f22d vocab=df1c7ba8
-/
theorem levelFaceVertexPoint_not_mem_relInterior {n : ℕ} (t : K.LevelFace n)
    (v : {v // v ∈ t.1}) :
    K.levelFaceVertexPoint t v ∉ K.levelFaceRelInterior t := by
  intro hvInt
  obtain ⟨x, hx, heq⟩ := hvInt
  have hsource : (K.safeSubdivision n).refined.facePoint t v = x :=
    (K.safeSubdivision n).homeo.injective heq.symm
  have hone : 1 < t.1.card := by
    rw [(K.safeSubdivision n).refined.faces_card t.1 t.2]
    omega
  obtain ⟨w, hwt, hwv⟩ := Finset.exists_mem_ne hone v.1
  have hzero : ((K.safeSubdivision n).refined.facePoint t v).1 w = 0 := by
    rw [(K.safeSubdivision n).refined.facePoint_val t v]
    simp [hwv]
  have hcoord := congrFun (congrArg Subtype.val hsource) w
  linarith [hx.2 w hwt]

omit [AdaptiveSafety.IsAdmissible K U] in
/--
@isnad1 id=not.0h4v.s5.70c9b3e98f85 from=translated src=- shape=4d6f706e vocab=a36a8cbc
-/
theorem adaptiveVertexPoint_not_mem_relInterior (t : K.AdaptiveFace U)
    (v : K.AdaptiveVertexOccurrence U t) :
    K.adaptiveVertexPoint U t v ∉ K.adaptiveFaceRelInterior U t :=
  K.levelFaceVertexPoint_not_mem_relInterior t.2.1 v

/-- Every collected touching vertex lies on the relative boundary of the fixed tile.
@isnad1 id=not.2h4v.s6.6c0d081bb8ed from=translated src=- shape=b3171330 vocab=8e5def6f
-/
theorem boundaryVertices_not_mem_relInterior (hU : IsOpen U)
    (t : K.AdaptiveFace U) {p : K.realization}
    (hp : p ∈ K.boundaryVertices U hU t) :
    p ∉ K.adaptiveFaceRelInterior U t := by
  obtain ⟨-, u, v, huv⟩ := (K.mem_boundaryVertices_iff U hU t p).mp hp
  by_cases hut : u.1 = t
  · have hvNot := K.adaptiveVertexPoint_not_mem_relInterior U u.1 v
    intro hpInt
    apply hvNot
    have hsets : K.adaptiveFaceRelInterior U u.1 =
        K.adaptiveFaceRelInterior U t := congrArg (K.adaptiveFaceRelInterior U) hut
    have hpIntU : p ∈ K.adaptiveFaceRelInterior U u.1 := by
      rw [hsets]
      exact hpInt
    rw [huv]
    exact hpIntU
  · have hdisjoint := K.disjoint_adaptiveFaceRelInterior_carrier U
      (s := t) (t := u.1) (fun h ↦ hut h.symm)
    intro hpInt
    exact Set.disjoint_left.mp hdisjoint hpInt
      (huv ▸ K.adaptiveVertexPoint_mem_carrier U u.1 v)

/-- All three original corners of a tile occur in its resolved boundary vertex set.
@isnad1 id=mem.1h4v.s6.3cd24fa1ac6c from=translated src=- shape=bad28a26 vocab=de680d1e
-/
theorem adaptiveVertexPoint_mem_boundaryVertices (hU : IsOpen U)
    (t : K.AdaptiveFace U) (v : K.AdaptiveVertexOccurrence U t) :
    K.adaptiveVertexPoint U t v ∈ K.boundaryVertices U hU t := by
  rw [K.mem_boundaryVertices_iff U hU t]
  refine ⟨K.adaptiveVertexPoint_mem_carrier U t v,
    K.selfTouchingFace U t, ?_⟩
  exact ⟨v, rfl⟩

/-- Carrier of one cyclic edge of a level face. -/
def levelFaceEdgeCarrier {n : ℕ} (t : K.LevelFace n) (i : ZMod 3) :
    Set K.realization :=
  (K.safeSubdivision n).homeo ''
    (K.safeSubdivision n).refined.faceCarrier
      ((K.safeSubdivision n).refined.faceEdge t i).1

/--
@isnad1 id=le.0h4v.s4.2b4c0792a83a from=translated src=- shape=cde1e06d vocab=41e25d42
-/
theorem levelFaceEdgeCarrier_subset {n : ℕ} (t : K.LevelFace n) (i : ZMod 3) :
    K.levelFaceEdgeCarrier t i ⊆ K.levelFaceCarrier t := by
  rintro p ⟨x, hx, rfl⟩
  refine ⟨x, ?_, rfl⟩
  intro v hvt
  exact hx v (fun hve ↦ hvt
    ((K.safeSubdivision n).refined.faceEdge_subset_face t i hve))

/-- Every point of a closed level face outside its relative interior lies on a cyclic edge.
@isnad1 id=ex.2h4v.s6.636262eb57b6 from=translated src=- shape=3e55d680 vocab=7623e7eb
-/
theorem exists_levelFaceEdge_of_mem_not_relInterior {n : ℕ} (t : K.LevelFace n)
    {p : K.realization} (hp : p ∈ K.levelFaceCarrier t)
    (hpInt : p ∉ K.levelFaceRelInterior t) :
    ∃ i : ZMod 3, p ∈ K.levelFaceEdgeCarrier t i := by
  classical
  obtain ⟨x, hxt, rfl⟩ := hp
  have hzero : ∃ v ∈ t.1, x.1 v = 0 := by
    by_contra h
    have hpos : ∀ v ∈ t.1, 0 < x.1 v := by
      intro v hv
      exact lt_of_le_of_ne (x.2.1.1 v) (fun hz ↦ h ⟨v, hv, hz.symm⟩)
    exact hpInt ⟨x, ⟨hxt, hpos⟩, rfl⟩
  obtain ⟨v, hvt, hxv⟩ := hzero
  let e0 : Finset (K.safeSubdivision n).refined.Vertex := t.1.erase v
  have heCard : e0.card = 2 := by
    dsimp only [e0]
    rw [Finset.card_erase_of_mem hvt,
      (K.safeSubdivision n).refined.faces_card t.1 t.2]
  have heMem : e0 ∈ (K.safeSubdivision n).refined.edges := by
    change e0 ∈ (K.safeSubdivision n).refined.faces.biUnion
      (fun s ↦ s.powersetCard 2)
    exact Finset.mem_biUnion.mpr
      ⟨t.1, t.2, Finset.mem_powersetCard.mpr ⟨Finset.erase_subset _ _, heCard⟩⟩
  let e : (K.safeSubdivision n).refined.Edge := ⟨e0, heMem⟩
  obtain ⟨i, hi⟩ := (K.safeSubdivision n).refined.exists_faceEdge_eq_of_subset
    t e (Finset.erase_subset _ _)
  refine ⟨i, x, ?_, rfl⟩
  rw [hi]
  intro w hw
  by_cases hwt : w ∈ t.1
  · have hwv : w = v := by
      by_contra hne
      exact hw (Finset.mem_erase.mpr ⟨hne, hwt⟩)
    simpa only [hwv] using hxv
  · exact hxt w hwt

/-- Resolved boundary vertices lying on one cyclic edge. -/
noncomputable def boundaryEdgeVertices (hU : IsOpen U) (t : K.AdaptiveFace U)
    (i : ZMod 3) : Finset K.realization := by
  classical
  exact (K.boundaryVertices U hU t).filter fun p ↦
    p ∈ K.levelFaceEdgeCarrier t.2.1 i

/--
@isnad1 id=iff.1h5v.s7.6f6742d7199a from=translated src=- shape=eaf0f6ab vocab=7ecdde51
-/
theorem mem_boundaryEdgeVertices_iff (hU : IsOpen U) (t : K.AdaptiveFace U)
    (i : ZMod 3) (p : K.realization) :
    p ∈ K.boundaryEdgeVertices U hU t i ↔
      p ∈ K.boundaryVertices U hU t ∧
        p ∈ K.levelFaceEdgeCarrier t.2.1 i := by
  classical
  exact Finset.mem_filter

/-- Barycentric parameter along a cyclic level-face edge, from vertex `i` to vertex `i+1`. -/
noncomputable def levelFaceEdgeParameter {n : ℕ} (t : K.LevelFace n)
    (i : ZMod 3) (p : K.realization) : ℝ :=
  ((K.safeSubdivision n).homeo.symm p).1
    ((K.safeSubdivision n).refined.faceVertex t (i + 1))

/--
@isnad1 id=injon.0h4v.s4.d69f2ab2be6d from=translated src=- shape=474e0f27 vocab=e34c4171
-/
theorem levelFaceEdgeParameter_injOn {n : ℕ} (t : K.LevelFace n) (i : ZMod 3) :
    Set.InjOn (K.levelFaceEdgeParameter t i) (K.levelFaceEdgeCarrier t i) := by
  intro p hp q hq hpq
  obtain ⟨x, hx, hxp⟩ := hp
  obtain ⟨y, hy, hyq⟩ := hq
  have hxEq : (K.safeSubdivision n).homeo.symm p = x := by
    rw [← hxp]
    exact (K.safeSubdivision n).homeo.symm_apply_apply x
  have hyEq : (K.safeSubdivision n).homeo.symm q = y := by
    rw [← hyq]
    exact (K.safeSubdivision n).homeo.symm_apply_apply y
  have hsecond : x.1 ((K.safeSubdivision n).refined.faceVertex t (i + 1)) =
      y.1 ((K.safeSubdivision n).refined.faceVertex t (i + 1)) := by
    simpa only [levelFaceEdgeParameter, hxEq, hyEq] using hpq
  have hfirst : x.1 ((K.safeSubdivision n).refined.faceVertex t i) =
      y.1 ((K.safeSubdivision n).refined.faceVertex t i) := by
    have hxsum : (∑ v ∈ ((K.safeSubdivision n).refined.faceEdge t i).1, x.1 v) = 1 := by
      calc
        _ = ∑ v, x.1 v := by
          apply Finset.sum_subset (Finset.subset_univ _)
          intro v _ hv
          exact hx v hv
        _ = 1 := x.2.1.2
    have hysum : (∑ v ∈ ((K.safeSubdivision n).refined.faceEdge t i).1, y.1 v) = 1 := by
      calc
        _ = ∑ v, y.1 v := by
          apply Finset.sum_subset (Finset.subset_univ _)
          intro v _ hv
          exact hy v hv
        _ = 1 := y.2.1.2
    simp only [(K.safeSubdivision n).refined.faceEdge_val,
      Finset.sum_insert,
      Finset.mem_singleton,
      (K.safeSubdivision n).refined.faceVertex_ne_next t i,
      not_false_eq_true,
      Finset.sum_singleton] at hxsum hysum
    linarith
  have hxy : x = y := by
    apply Subtype.ext
    funext v
    by_cases hvi : v = (K.safeSubdivision n).refined.faceVertex t i
    · simpa only [hvi] using hfirst
    by_cases hvj : v = (K.safeSubdivision n).refined.faceVertex t (i + 1)
    · simpa only [hvj] using hsecond
    have hvEdge : v ∉ ((K.safeSubdivision n).refined.faceEdge t i).1 := by
      simp only [(K.safeSubdivision n).refined.faceEdge_val, Finset.mem_insert,
        Finset.mem_singleton]
      exact fun h ↦ h.elim hvi hvj
    rw [hx v hvEdge, hy v hvEdge]
  apply (K.safeSubdivision n).homeo.symm.injective
  calc
    (K.safeSubdivision n).homeo.symm p = x := hxEq
    _ = y := hxy
    _ = (K.safeSubdivision n).homeo.symm q := hyEq.symm

/-- A resolved vertex on one adaptive edge. -/
abbrev BoundaryEdgeVertex (hU : IsOpen U) (t : K.AdaptiveFace U) (i : ZMod 3) :=
  {p // p ∈ K.boundaryEdgeVertices U hU t i}

/--
@isnad1 id=injectiv.1h4v.s7.09abdbc62b9e from=translated src=- shape=9b977276 vocab=9b128ead
-/
theorem boundaryEdgeParameter_injective (hU : IsOpen U) (t : K.AdaptiveFace U)
    (i : ZMod 3) : Function.Injective
      (fun p : K.BoundaryEdgeVertex U hU t i ↦
        K.levelFaceEdgeParameter t.2.1 i p.1) := by
  intro p q hpq
  apply Subtype.ext
  apply K.levelFaceEdgeParameter_injOn t.2.1 i
  · exact (K.mem_boundaryEdgeVertices_iff U hU t i p.1).mp p.2 |>.2
  · exact (K.mem_boundaryEdgeVertices_iff U hU t i q.1).mp q.2 |>.2
  · exact hpq

/-- The parameter order on the finite set of vertices of one resolved edge. -/
def boundaryEdgeVertexLE (hU : IsOpen U) (t : K.AdaptiveFace U) (i : ZMod 3)
    (p q : K.BoundaryEdgeVertex U hU t i) : Prop :=
  K.levelFaceEdgeParameter t.2.1 i p.1 ≤
    K.levelFaceEdgeParameter t.2.1 i q.1

noncomputable instance boundaryEdgeVertexLEDecidable (hU : IsOpen U)
    (t : K.AdaptiveFace U) (i : ZMod 3) :
    DecidableRel (K.boundaryEdgeVertexLE U hU t i) :=
  fun p q ↦ inferInstanceAs (Decidable
    (K.levelFaceEdgeParameter t.2.1 i p.1 ≤
      K.levelFaceEdgeParameter t.2.1 i q.1))

/--
@isnad1 id=total.1h4v.s6.a1d3656b57ef from=translated src=- shape=636508f4 vocab=1b002384
-/
instance boundaryEdgeVertexLE_total (hU : IsOpen U)
    (t : K.AdaptiveFace U) (i : ZMod 3) :
    Std.Total (K.boundaryEdgeVertexLE U hU t i) :=
  ⟨fun p q ↦ le_total
    (K.levelFaceEdgeParameter t.2.1 i p.1)
    (K.levelFaceEdgeParameter t.2.1 i q.1)⟩

/--
@isnad1 id=antisymm.1h4v.s6.82eef2da643f from=translated src=- shape=636508f4 vocab=14904832
-/
instance boundaryEdgeVertexLE_antisymm (hU : IsOpen U)
    (t : K.AdaptiveFace U) (i : ZMod 3) :
    Std.Antisymm (K.boundaryEdgeVertexLE U hU t i) :=
  ⟨fun _ _ hpq hqp ↦ K.boundaryEdgeParameter_injective U hU t i
    (le_antisymm hpq hqp)⟩

/--
@isnad1 id=istrans.1h4v.s6.44ae44e1ddb0 from=translated src=- shape=636508f4 vocab=4c6510de
-/
instance boundaryEdgeVertexLE_isTrans (hU : IsOpen U)
    (t : K.AdaptiveFace U) (i : ZMod 3) :
    IsTrans (K.BoundaryEdgeVertex U hU t i)
      (K.boundaryEdgeVertexLE U hU t i) :=
  ⟨fun _ _ _ hpq hqr ↦ hpq.trans hqr⟩

/-- Canonically ordered vertices on one resolved adaptive edge. -/
noncomputable def boundaryEdgeVertexList (hU : IsOpen U) (t : K.AdaptiveFace U)
    (i : ZMod 3) : List K.realization := by
  classical
  exact ((K.boundaryEdgeVertices U hU t i).attach.sort
    (K.boundaryEdgeVertexLE U hU t i)).map Subtype.val

/--
@isnad1 id=iff.1h5v.s6.adbe01744fc1 from=translated src=- shape=d1883326 vocab=bf79186a
-/
theorem mem_boundaryEdgeVertexList_iff (hU : IsOpen U) (t : K.AdaptiveFace U)
    (i : ZMod 3) (p : K.realization) :
    p ∈ K.boundaryEdgeVertexList U hU t i ↔
      p ∈ K.boundaryEdgeVertices U hU t i := by
  classical
  simp only [boundaryEdgeVertexList, List.mem_map, Finset.mem_sort,
    Finset.mem_attach]
  constructor
  · rintro ⟨q, -, rfl⟩
    exact q.2
  · intro hp
    exact ⟨⟨p, hp⟩, trivial, rfl⟩

/--
@isnad1 id=nodup.1h4v.s6.d06fae5a4df0 from=translated src=- shape=9589a08a vocab=e730f084
-/
theorem boundaryEdgeVertexList_nodup (hU : IsOpen U) (t : K.AdaptiveFace U)
    (i : ZMod 3) : (K.boundaryEdgeVertexList U hU t i).Nodup := by
  classical
  unfold boundaryEdgeVertexList
  exact (Finset.sort_nodup _ (K.boundaryEdgeVertexLE U hU t i)).map
    Subtype.val_injective

/--
@isnad1 id=pairwise.1h4v.s8.3adf73e0c160 from=translated src=- shape=d2628fb6 vocab=71163382
-/
theorem boundaryEdgeVertexList_pairwise_parameter_le (hU : IsOpen U)
    (t : K.AdaptiveFace U) (i : ZMod 3) :
    (K.boundaryEdgeVertexList U hU t i).Pairwise
      (fun p q ↦ K.levelFaceEdgeParameter t.2.1 i p ≤
        K.levelFaceEdgeParameter t.2.1 i q) := by
  classical
  unfold boundaryEdgeVertexList
  simp only [List.pairwise_map]
  apply (Finset.pairwise_sort
    (K.boundaryEdgeVertices U hU t i).attach
    (K.boundaryEdgeVertexLE U hU t i)).imp
  intro p q hpq
  exact hpq

/-- A monotone finite list with at least two entries covers every parameter between its
endpoints by one of its consecutive intervals.
@isnad1 id=ex.4h4v.s7.11b5bc4fade5 from=translated src=- shape=89387ba9 vocab=df3247b0
-/
theorem exists_adjacent_get_of_pairwise_le {α : Type*} (L : List α) (f : α → ℝ)
    (hlength : 2 ≤ L.length)
    (hpair : L.Pairwise fun a b ↦ f a ≤ f b) {r : ℝ}
    (hfirst : f (L.get ⟨0, by omega⟩) ≤ r)
    (hlast : r ≤ f (L.get ⟨L.length - 1, by omega⟩)) :
    ∃ j : Fin (L.length - 1),
      f (L.get ⟨j.1, by omega⟩) ≤ r ∧
        r ≤ f (L.get ⟨j.1 + 1, by omega⟩) := by
  classical
  let A : Finset (Fin L.length) :=
    Finset.univ.filter fun k ↦ f (L.get k) ≤ r
  have hA : A.Nonempty := by
    refine ⟨⟨0, by omega⟩, ?_⟩
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hfirst
  let k : Fin L.length := A.max' hA
  have hkA : k ∈ A := Finset.max'_mem A hA
  have hkLower : f (L.get k) ≤ r := by
    simpa only [A, Finset.mem_filter, Finset.mem_univ, true_and] using hkA
  by_cases hkLast : k.1 = L.length - 1
  · let prev : Fin L.length := ⟨L.length - 2, by omega⟩
    let last : Fin L.length := ⟨L.length - 1, by omega⟩
    have hklastFin : k = last := Fin.ext hkLast
    rw [hklastFin] at hkLower
    let j : Fin (L.length - 1) := ⟨L.length - 2, by omega⟩
    refine ⟨j, ?_, ?_⟩
    · have hprev : f (L.get prev) ≤ f (L.get last) := by
        apply hpair.rel_get_of_lt
        exact Fin.mk_lt_mk.mpr (by omega)
      simpa only [j, prev, last] using hprev.trans hkLower
    · have hjNext : (⟨j.1 + 1, by omega⟩ : Fin L.length) = last := by
        apply Fin.ext
        dsimp only [j, last]
        omega
      rw [hjNext]
      simpa only [last] using hlast
  · have hkBeforeLast : k.1 < L.length - 1 := by omega
    let j : Fin (L.length - 1) := ⟨k.1, hkBeforeLast⟩
    let kNext : Fin L.length := ⟨k.1 + 1, by omega⟩
    have hkNextUpper : r ≤ f (L.get kNext) := by
      apply le_of_not_ge
      intro hkNextLower
      have hkNextA : kNext ∈ A := by
        simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hkNextLower
      have hle : kNext ≤ k := Finset.le_max' A kNext hkNextA
      change k.1 + 1 ≤ k.1 at hle
      omega
    refine ⟨j, ?_, ?_⟩
    · simpa only [j] using hkLower
    · simpa only [j, kNext] using hkNextUpper

/-- The first corner of a cyclic adaptive edge. -/
noncomputable def adaptiveEdgeFirstCorner (t : K.AdaptiveFace U) (i : ZMod 3) :
    K.realization :=
  K.levelFaceVertexPoint t.2.1
    ⟨(K.safeSubdivision t.1).refined.faceVertex t.2.1 i,
      (K.safeSubdivision t.1).refined.faceVertex_mem t.2.1 i⟩

/-- The second corner of a cyclic adaptive edge. -/
noncomputable def adaptiveEdgeSecondCorner (t : K.AdaptiveFace U) (i : ZMod 3) :
    K.realization :=
  K.levelFaceVertexPoint t.2.1
    ⟨(K.safeSubdivision t.1).refined.faceVertex t.2.1 (i + 1),
      (K.safeSubdivision t.1).refined.faceVertex_mem t.2.1 (i + 1)⟩

/--
@isnad1 id=mem.1h4v.s6.3844849d5374 from=translated src=- shape=455c85f2 vocab=d1691319
-/
theorem adaptiveEdgeFirstCorner_mem_boundaryEdgeVertices (hU : IsOpen U)
    (t : K.AdaptiveFace U) (i : ZMod 3) :
    K.adaptiveEdgeFirstCorner U t i ∈ K.boundaryEdgeVertices U hU t i := by
  rw [K.mem_boundaryEdgeVertices_iff U hU t i]
  constructor
  · exact K.adaptiveVertexPoint_mem_boundaryVertices U hU t
      ⟨(K.safeSubdivision t.1).refined.faceVertex t.2.1 i,
        (K.safeSubdivision t.1).refined.faceVertex_mem t.2.1 i⟩
  · refine ⟨(K.safeSubdivision t.1).refined.facePoint t.2.1
      ⟨(K.safeSubdivision t.1).refined.faceVertex t.2.1 i,
        (K.safeSubdivision t.1).refined.faceVertex_mem t.2.1 i⟩, ?_, rfl⟩
    exact ((K.safeSubdivision t.1).refined.vertexPoint_mem_faceCarrier_iff
      ⟨(K.safeSubdivision t.1).refined.faceVertex t.2.1 i,
        t.2.1.1, t.2.1.2,
        (K.safeSubdivision t.1).refined.faceVertex_mem t.2.1 i⟩
      ((K.safeSubdivision t.1).refined.faceEdge t.2.1 i).1).mpr (by
      rw [(K.safeSubdivision t.1).refined.faceEdge_val]
      simp)

/--
@isnad1 id=mem.1h4v.s6.256be254599f from=translated src=- shape=455c85f2 vocab=e39c398e
-/
theorem adaptiveEdgeSecondCorner_mem_boundaryEdgeVertices (hU : IsOpen U)
    (t : K.AdaptiveFace U) (i : ZMod 3) :
    K.adaptiveEdgeSecondCorner U t i ∈ K.boundaryEdgeVertices U hU t i := by
  rw [K.mem_boundaryEdgeVertices_iff U hU t i]
  constructor
  · exact K.adaptiveVertexPoint_mem_boundaryVertices U hU t
      ⟨(K.safeSubdivision t.1).refined.faceVertex t.2.1 (i + 1),
        (K.safeSubdivision t.1).refined.faceVertex_mem t.2.1 (i + 1)⟩
  · refine ⟨(K.safeSubdivision t.1).refined.facePoint t.2.1
      ⟨(K.safeSubdivision t.1).refined.faceVertex t.2.1 (i + 1),
        (K.safeSubdivision t.1).refined.faceVertex_mem t.2.1 (i + 1)⟩, ?_, rfl⟩
    exact ((K.safeSubdivision t.1).refined.vertexPoint_mem_faceCarrier_iff
      ⟨(K.safeSubdivision t.1).refined.faceVertex t.2.1 (i + 1),
        t.2.1.1, t.2.1.2,
        (K.safeSubdivision t.1).refined.faceVertex_mem t.2.1 (i + 1)⟩
      ((K.safeSubdivision t.1).refined.faceEdge t.2.1 i).1).mpr (by
      rw [(K.safeSubdivision t.1).refined.faceEdge_val]
      simp)

omit [AdaptiveSafety.IsAdmissible K U] in
/--
@isnad1 id=ne.0h4v.s5.06dfbe3f2e39 from=translated src=- shape=6db41346 vocab=df1f0bc3
-/
theorem adaptiveEdgeFirstCorner_ne_second (t : K.AdaptiveFace U) (i : ZMod 3) :
    K.adaptiveEdgeFirstCorner U t i ≠ K.adaptiveEdgeSecondCorner U t i := by
  intro h
  have hvne := (K.safeSubdivision t.1).refined.faceVertex_ne_next t.2.1 i
  have hsource := (K.safeSubdivision t.1).homeo.injective h
  have hcoord := congrArg (fun x : (K.safeSubdivision t.1).refined.realization ↦
    x.1 ((K.safeSubdivision t.1).refined.faceVertex t.2.1 i)) hsource
  simp only [(K.safeSubdivision t.1).refined.facePoint_val,
    Pi.single_apply, ite_eq_right hvne] at hcoord
  norm_num at hcoord

/--
@isnad1 id=le.1h4v.s6.6f1764a4b79b from=translated src=- shape=a607ecf2 vocab=f32e52dd
-/
theorem two_le_boundaryEdgeVertices_card (hU : IsOpen U)
    (t : K.AdaptiveFace U) (i : ZMod 3) :
    2 ≤ (K.boundaryEdgeVertices U hU t i).card := by
  rw [Nat.succ_le_iff]
  apply Finset.one_lt_card.mpr
  exact ⟨K.adaptiveEdgeFirstCorner U t i,
    K.adaptiveEdgeFirstCorner_mem_boundaryEdgeVertices U hU t i,
    K.adaptiveEdgeSecondCorner U t i,
    K.adaptiveEdgeSecondCorner_mem_boundaryEdgeVertices U hU t i,
    K.adaptiveEdgeFirstCorner_ne_second U t i⟩

/--
@isnad1 id=le.1h4v.s6.c78221daf399 from=translated src=- shape=a607ecf2 vocab=2a7533eb
-/
theorem two_le_boundaryEdgeVertexList_length (hU : IsOpen U)
    (t : K.AdaptiveFace U) (i : ZMod 3) :
    2 ≤ (K.boundaryEdgeVertexList U hU t i).length := by
  rw [← List.toFinset_card_of_nodup
    (K.boundaryEdgeVertexList_nodup U hU t i)]
  rw [show (K.boundaryEdgeVertexList U hU t i).toFinset =
      K.boundaryEdgeVertices U hU t i by
    ext p
    simp only [List.mem_toFinset, K.mem_boundaryEdgeVertexList_iff U hU t i]]
  exact K.two_le_boundaryEdgeVertices_card U hU t i

omit [AdaptiveSafety.IsAdmissible K U] in
/--
@isnad1 id=eq.0h4v.s7.fc849d8455bc from=translated src=- shape=9296135d vocab=14f251fd
-/
@[simp] theorem levelFaceEdgeParameter_adaptiveEdgeFirstCorner
    (t : K.AdaptiveFace U) (i : ZMod 3) :
    K.levelFaceEdgeParameter t.2.1 i
      (K.adaptiveEdgeFirstCorner U t i) = 0 := by
  simp [levelFaceEdgeParameter, adaptiveEdgeFirstCorner, levelFaceVertexPoint,
    (K.safeSubdivision t.1).refined.faceVertex_ne_next t.2.1 i]

omit [AdaptiveSafety.IsAdmissible K U] in
/--
@isnad1 id=eq.0h4v.s7.24eb2c834180 from=translated src=- shape=9296135d vocab=73cf7a22
-/
@[simp] theorem levelFaceEdgeParameter_adaptiveEdgeSecondCorner
    (t : K.AdaptiveFace U) (i : ZMod 3) :
    K.levelFaceEdgeParameter t.2.1 i
      (K.adaptiveEdgeSecondCorner U t i) = 1 := by
  simp [levelFaceEdgeParameter, adaptiveEdgeSecondCorner, levelFaceVertexPoint]

/--
@isnad1 id=mem.1h5v.s5.c5b8e29b7845 from=translated src=- shape=b85c080b vocab=91175536
-/
theorem levelFaceEdgeParameter_mem_Icc {n : ℕ} (t : K.LevelFace n)
    (i : ZMod 3) {p : K.realization}
    (hp : p ∈ K.levelFaceEdgeCarrier t i) :
    K.levelFaceEdgeParameter t i p ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨x, hx, rfl⟩ := hp
  rw [levelFaceEdgeParameter, (K.safeSubdivision n).homeo.symm_apply_apply]
  exact mem_Icc_of_mem_stdSimplex x.2.1 _

/--
@isnad1 id=eq.1h4v.s7.2b20f06af377 from=translated src=- shape=4d1fb390 vocab=e237c12e
-/
theorem boundaryEdgeVertexList_first_parameter (hU : IsOpen U)
    (t : K.AdaptiveFace U) (i : ZMod 3) :
    K.levelFaceEdgeParameter t.2.1 i
      ((K.boundaryEdgeVertexList U hU t i).get ⟨0, by
        have := K.two_le_boundaryEdgeVertexList_length U hU t i
        omega⟩) = 0 := by
  let L := K.boundaryEdgeVertexList U hU t i
  let first : Fin L.length := ⟨0, by
    dsimp only [L]
    have := K.two_le_boundaryEdgeVertexList_length U hU t i
    omega⟩
  have hfirstEdge : L.get first ∈ K.levelFaceEdgeCarrier t.2.1 i :=
    ((K.mem_boundaryEdgeVertices_iff U hU t i _).mp
      ((K.mem_boundaryEdgeVertexList_iff U hU t i _).mp
        (List.get_mem L first))).2
  have hnonneg := (K.levelFaceEdgeParameter_mem_Icc t.2.1 i hfirstEdge).1
  have hcornerL : K.adaptiveEdgeFirstCorner U t i ∈ L :=
    (K.mem_boundaryEdgeVertexList_iff U hU t i _).mpr
      (K.adaptiveEdgeFirstCorner_mem_boundaryEdgeVertices U hU t i)
  obtain ⟨k, hk⟩ := List.get_of_mem hcornerL
  have hle : K.levelFaceEdgeParameter t.2.1 i (L.get first) ≤ 0 := by
    by_cases hkfirst : k = first
    · subst k
      simpa only [L, first, hk] using
        K.levelFaceEdgeParameter_adaptiveEdgeFirstCorner U t i |>.le
    · have hlt : first < k := by
        have hk0 : k.1 ≠ 0 := by
          intro hk0
          apply hkfirst
          apply Fin.ext
          simpa only [first] using hk0
        change 0 < k.1
        omega
      have hpair := K.boundaryEdgeVertexList_pairwise_parameter_le U hU t i
      have := hpair.rel_get_of_lt hlt
      rw [hk, K.levelFaceEdgeParameter_adaptiveEdgeFirstCorner U t i] at this
      exact this
  apply le_antisymm hle hnonneg

/--
@isnad1 id=eq.1h4v.s7.d6c682c7668a from=translated src=- shape=391eb405 vocab=c8cc86c3
-/
theorem boundaryEdgeVertexList_last_parameter (hU : IsOpen U)
    (t : K.AdaptiveFace U) (i : ZMod 3) :
    K.levelFaceEdgeParameter t.2.1 i
      ((K.boundaryEdgeVertexList U hU t i).get
        ⟨(K.boundaryEdgeVertexList U hU t i).length - 1, by
          have := K.two_le_boundaryEdgeVertexList_length U hU t i
          omega⟩) = 1 := by
  let L := K.boundaryEdgeVertexList U hU t i
  let last : Fin L.length := ⟨L.length - 1, by
    dsimp only [L]
    have := K.two_le_boundaryEdgeVertexList_length U hU t i
    omega⟩
  have hlastEdge : L.get last ∈ K.levelFaceEdgeCarrier t.2.1 i :=
    ((K.mem_boundaryEdgeVertices_iff U hU t i _).mp
      ((K.mem_boundaryEdgeVertexList_iff U hU t i _).mp
        (List.get_mem L last))).2
  have hupper := (K.levelFaceEdgeParameter_mem_Icc t.2.1 i hlastEdge).2
  have hcornerL : K.adaptiveEdgeSecondCorner U t i ∈ L :=
    (K.mem_boundaryEdgeVertexList_iff U hU t i _).mpr
      (K.adaptiveEdgeSecondCorner_mem_boundaryEdgeVertices U hU t i)
  obtain ⟨k, hk⟩ := List.get_of_mem hcornerL
  have hle : 1 ≤ K.levelFaceEdgeParameter t.2.1 i (L.get last) := by
    by_cases hklast : k = last
    · subst k
      simpa only [L, last, hk] using
        K.levelFaceEdgeParameter_adaptiveEdgeSecondCorner U t i |>.ge
    · have hlt : k < last := by
        have hkne : k.1 ≠ L.length - 1 := by
          intro hkne
          apply hklast
          apply Fin.ext
          simpa only [last] using hkne
        change k.1 < L.length - 1
        omega
      have hpair := K.boundaryEdgeVertexList_pairwise_parameter_le U hU t i
      have := hpair.rel_get_of_lt hlt
      rw [hk, K.levelFaceEdgeParameter_adaptiveEdgeSecondCorner U t i] at this
      exact this
  apply le_antisymm hupper hle

/-- The equal-weight point of the standard simplex on an intrinsic face. -/
noncomputable def faceCenterSimplex (t : K.Face) :
    stdSimplex ℝ {v // v ∈ t.1} := by
  let x : {v // v ∈ t.1} → ℝ := fun _ ↦ 1 / 3
  refine ⟨x, ?_, ?_⟩
  · intro v
    dsimp only [x]
    norm_num
  · change ∑ _ : {v // v ∈ t.1}, (1 / 3 : ℝ) = 1
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe,
      K.faces_card t.1 t.2]
    norm_num

/--
@isnad1 id=eq.0h3v.s8.612542bde4ba from=translated src=- shape=e191b0b5 vocab=531f3e1f
-/
@[simp] theorem faceCenterSimplex_apply (t : K.Face) (v : {v // v ∈ t.1}) :
    K.faceCenterSimplex t v = 1 / 3 := rfl

/-- The barycentric center of an arbitrary level face, transported to the original
realization. -/
noncomputable def levelFaceCenter {n : ℕ} (t : K.LevelFace n) : K.realization :=
  (K.safeSubdivision n).homeo
    ((K.safeSubdivision n).refined.faceStandardMap t
      ((K.safeSubdivision n).refined.faceCenterSimplex t))

/--
@isnad1 id=mem.0h3v.s4.368d8f379662 from=translated src=- shape=4f917f65 vocab=5a826694
-/
theorem levelFaceCenter_mem_relInterior {n : ℕ} (t : K.LevelFace n) :
    K.levelFaceCenter t ∈ K.levelFaceRelInterior t := by
  refine ⟨(K.safeSubdivision n).refined.faceStandardMap t
      ((K.safeSubdivision n).refined.faceCenterSimplex t), ?_, rfl⟩
  constructor
  · intro v hv
    rw [(K.safeSubdivision n).refined.faceStandardMap_val]
    exact extendFaceCoordinates_of_notMem t.1 _ hv
  · intro v hv
    rw [(K.safeSubdivision n).refined.faceStandardMap_val,
      extendFaceCoordinates_of_mem t.1 _ hv]
    norm_num

/--
@isnad1 id=mem.0h3v.s4.e57fee186ffe from=translated src=- shape=4f917f65 vocab=6d14e86e
-/
theorem levelFaceCenter_mem_carrier {n : ℕ} (t : K.LevelFace n) :
    K.levelFaceCenter t ∈ K.levelFaceCarrier t :=
  K.levelFaceRelInterior_subset_carrier t
    (K.levelFaceCenter_mem_relInterior t)

/-- If a later-level edge meets an earlier face at a point which is not a later-level vertex,
and the two face interiors are disjoint, then the whole later edge lies in the earlier face.
This is the no-crossing fact for nested midpoint subdivisions.
@isnad1 id=le.4h7v.s8.7d602ae86416 from=translated src=- shape=6348ee83 vocab=e9eab580
-/
theorem levelFaceEdgeCarrier_subset_of_common_not_vertex (n k : ℕ)
    (s : K.LevelFace n) (t : K.LevelFace (n + k)) (i : ZMod 3)
    {p : K.realization}
    (hdisjoint : Disjoint (K.levelFaceRelInterior t) (K.levelFaceCarrier s))
    (hps : p ∈ K.levelFaceCarrier s)
    (hpt : p ∈ K.levelFaceEdgeCarrier t i)
    (hpNot : ∀ v : {v // v ∈ t.1},
      p ≠ K.levelFaceVertexPoint t v) :
    K.levelFaceEdgeCarrier t i ⊆ K.levelFaceCarrier s := by
  obtain ⟨r, hpr, hrs⟩ := K.exists_levelFace_add_containing n k s hps
  have hrt : r ≠ t := by
    intro hrt
    subst r
    exact Set.disjoint_left.mp hdisjoint
      (K.levelFaceCenter_mem_relInterior t)
      (hrs (K.levelFaceCenter_mem_carrier t))
  have hptCarrier : p ∈ K.levelFaceCarrier t :=
    K.levelFaceEdgeCarrier_subset t i hpt
  have hpBoth : p ∈ K.levelFaceCarrier r ∩ K.levelFaceCarrier t :=
    ⟨hpr, hptCarrier⟩
  rw [K.levelFaceCarrier_inter r t] at hpBoth
  obtain ⟨q, hqe, hqp⟩ := hpBoth
  let R := K.safeSubdivision (n + k)
  let e : Finset R.refined.Vertex := r.1 ∩ t.1
  let d : Finset R.refined.Vertex := (R.refined.faceEdge t i).1
  have hecardLe : e.card ≤ 2 := K.card_inter_levelFace_le_two hrt
  have heNonempty : e.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    have : q ∈ R.refined.faceCarrier (∅ : Finset R.refined.Vertex) := by
      simpa only [e, he] using hqe
    rw [R.refined.faceCarrier_empty] at this
    exact this
  have hecard : e.card = 2 := by
    have hepos : 0 < e.card := Finset.card_pos.mpr heNonempty
    have hcases : e.card = 1 ∨ e.card = 2 := by omega
    rcases hcases with hone | htwo
    · obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hone
      have hvt : v ∈ t.1 := Finset.inter_subset_right (by
        change v ∈ e
        rw [hv]
        exact Finset.mem_singleton_self v)
      have hqSingle : q ∈ R.refined.faceCarrier ({v} : Finset R.refined.Vertex) := by
        simpa only [e, hv] using hqe
      have hqv := R.refined.eq_facePoint_of_mem_faceCarrier_singleton t ⟨v, hvt⟩ q hqSingle
      exact False.elim (hpNot ⟨v, hvt⟩ (by
        calc
          p = R.homeo q := hqp.symm
          _ = R.homeo (R.refined.facePoint t ⟨v, hvt⟩) := congrArg R.homeo hqv
          _ = K.levelFaceVertexPoint t ⟨v, hvt⟩ := rfl))
    · exact htwo
  obtain ⟨y, hyd, hyp⟩ := hpt
  have hqy : q = y := R.homeo.injective (hqp.trans hyp.symm)
  have hqd : q ∈ R.refined.faceCarrier d := by
    simpa only [d, hqy] using hyd
  have hdcard : d.card = 2 := R.refined.card_of_mem_edges (R.refined.faceEdge t i).2
  have hed : e = d := by
    apply R.refined.eq_of_card_two_of_mem_faceCarriers_not_vertex t
      Finset.inter_subset_right (R.refined.faceEdge_subset_face t i)
      hecard hdcard hqe hqd
    intro v hqv
    apply hpNot v
    calc
      p = R.homeo q := hqp.symm
      _ = R.homeo (R.refined.facePoint t v) := congrArg R.homeo hqv
      _ = K.levelFaceVertexPoint t v := rfl
  rintro z ⟨x, hxd, rfl⟩
  apply hrs
  refine ⟨x, ?_, rfl⟩
  have hxe : x ∈ R.refined.faceCarrier e := by
    rw [hed]
    exact hxd
  intro v hvr
  exact hxe v (fun hve ↦ hvr (Finset.inter_subset_left hve))

/-- Adaptive-tile specialization of nested-edge no crossing.  At a common point which is not a
resolved vertex of the later tile, the later edge is contained in the earlier tile.
@isnad1 id=le.6h6v.s8.5f65e1afa5f7 from=translated src=- shape=64bf62d0 vocab=0fdc61c7
-/
theorem adaptiveFace_edgeCarrier_subset_of_level_le_of_common_not_boundaryVertex
    (hU : IsOpen U) {s t : K.AdaptiveFace U} (hst : s ≠ t)
    (hlevel : s.1 ≤ t.1) (i : ZMod 3) {p : K.realization}
    (hps : p ∈ K.adaptiveFaceCarrier U s)
    (hpt : p ∈ K.levelFaceEdgeCarrier t.2.1 i)
    (hpNot : p ∉ K.boundaryVertices U hU t) :
    K.levelFaceEdgeCarrier t.2.1 i ⊆ K.adaptiveFaceCarrier U s := by
  rcases s with ⟨n, s⟩
  rcases t with ⟨m, t⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hlevel
  apply K.levelFaceEdgeCarrier_subset_of_common_not_vertex n k s.1 t.1 i
  · exact K.disjoint_adaptiveFaceRelInterior_carrier U
      (s := ⟨n + k, t⟩) (t := ⟨n, s⟩) (fun h ↦ hst h.symm)
  · exact hps
  · exact hpt
  · intro v hpv
    apply hpNot
    rw [hpv]
    exact K.adaptiveVertexPoint_mem_boundaryVertices U hU ⟨n + k, t⟩ v

/-- The barycentric center of one adaptive tile, transported to the original realization. -/
noncomputable def adaptiveFaceCenter (t : K.AdaptiveFace U) : K.realization :=
  (K.safeSubdivision t.1).homeo
    ((K.safeSubdivision t.1).refined.faceStandardMap t.2.1
      ((K.safeSubdivision t.1).refined.faceCenterSimplex t.2.1))

omit [AdaptiveSafety.IsAdmissible K U] in
/--
@isnad1 id=mem.0h3v.s5.8b9f87f68682 from=translated src=- shape=7a420818 vocab=87b7e73a
-/
theorem adaptiveFaceCenter_mem_relInterior (t : K.AdaptiveFace U) :
    K.adaptiveFaceCenter U t ∈ K.adaptiveFaceRelInterior U t := by
  refine ⟨(K.safeSubdivision t.1).refined.faceStandardMap t.2.1
      ((K.safeSubdivision t.1).refined.faceCenterSimplex t.2.1), ?_, rfl⟩
  constructor
  · intro v hv
    rw [(K.safeSubdivision t.1).refined.faceStandardMap_val]
    exact extendFaceCoordinates_of_notMem t.2.1.1 _ hv
  · intro v hv
    rw [(K.safeSubdivision t.1).refined.faceStandardMap_val,
      extendFaceCoordinates_of_mem t.2.1.1 _ hv]
    norm_num

omit [AdaptiveSafety.IsAdmissible K U] in
/--
@isnad1 id=mem.0h3v.s5.0265b1bad2b7 from=translated src=- shape=7a420818 vocab=546f7947
-/
theorem adaptiveFaceCenter_mem_carrier (t : K.AdaptiveFace U) :
    K.adaptiveFaceCenter U t ∈ K.adaptiveFaceCarrier U t :=
  K.levelFaceRelInterior_subset_carrier t.2.1
    (K.adaptiveFaceCenter_mem_relInterior U t)

/--
@isnad1 id=ne.2h4v.s6.b6fa09947a7a from=translated src=- shape=1afdca51 vocab=5628c4b1
-/
theorem adaptiveFaceCenter_ne_boundaryVertex (hU : IsOpen U)
    (t : K.AdaptiveFace U) {p : K.realization}
    (hp : p ∈ K.boundaryVertices U hU t) :
    K.adaptiveFaceCenter U t ≠ p := by
  intro h
  exact K.boundaryVertices_not_mem_relInterior U hU t hp
    (h ▸ K.adaptiveFaceCenter_mem_relInterior U t)

/-- One of the consecutive intervals in the ordered subdivision of an adaptive edge. -/
abbrev AdaptiveEdgeInterval (hU : IsOpen U) (t : K.AdaptiveFace U) (i : ZMod 3) :=
  Fin ((K.boundaryEdgeVertexList U hU t i).length - 1)

/-- First endpoint of a resolved adaptive-edge interval. -/
noncomputable def adaptiveEdgeIntervalFirst (hU : IsOpen U)
    (t : K.AdaptiveFace U) (i : ZMod 3)
    (j : K.AdaptiveEdgeInterval U hU t i) : K.realization :=
  (K.boundaryEdgeVertexList U hU t i).get
    ⟨j.1, by
      have hj := j.2
      omega⟩

/-- Second endpoint of a resolved adaptive-edge interval. -/
noncomputable def adaptiveEdgeIntervalSecond (hU : IsOpen U)
    (t : K.AdaptiveFace U) (i : ZMod 3)
    (j : K.AdaptiveEdgeInterval U hU t i) : K.realization :=
  (K.boundaryEdgeVertexList U hU t i).get
    ⟨j.1 + 1, by
      have hj := j.2
      omega⟩

/--
@isnad1 id=mem.1h5v.s6.4bef6446da8d from=translated src=- shape=1377442d vocab=b1b611a7
-/
theorem adaptiveEdgeIntervalFirst_mem_boundaryEdgeVertices (hU : IsOpen U)
    (t : K.AdaptiveFace U) (i : ZMod 3)
    (j : K.AdaptiveEdgeInterval U hU t i) :
    K.adaptiveEdgeIntervalFirst U hU t i j ∈
      K.boundaryEdgeVertices U hU t i := by
  rw [← K.mem_boundaryEdgeVertexList_iff U hU t i]
  exact List.get_mem _ _

/--
@isnad1 id=mem.1h5v.s6.88143d0c9f35 from=translated src=- shape=1377442d vocab=dc63e7f1
-/
theorem adaptiveEdgeIntervalSecond_mem_boundaryEdgeVertices (hU : IsOpen U)
    (t : K.AdaptiveFace U) (i : ZMod 3)
    (j : K.AdaptiveEdgeInterval U hU t i) :
    K.adaptiveEdgeIntervalSecond U hU t i j ∈
      K.boundaryEdgeVertices U hU t i := by
  rw [← K.mem_boundaryEdgeVertexList_iff U hU t i]
  exact List.get_mem _ _

/--
@isnad1 id=ne.1h5v.s6.921cf717dd71 from=translated src=- shape=b4b25198 vocab=7b8b0fe1
-/
theorem adaptiveEdgeIntervalFirst_ne_second (hU : IsOpen U)
    (t : K.AdaptiveFace U) (i : ZMod 3)
    (j : K.AdaptiveEdgeInterval U hU t i) :
    K.adaptiveEdgeIntervalFirst U hU t i j ≠
      K.adaptiveEdgeIntervalSecond U hU t i j := by
  intro h
  have hn := K.boundaryEdgeVertexList_nodup U hU t i
  have hij := hn.injective_get h
  have hval := congrArg Fin.val hij
  simp only at hval
  omega

/-- Consecutive vertices in the resolved edge order have strictly increasing edge parameter.
@isnad1 id=lt.1h5v.s8.726c82a864f9 from=translated src=- shape=9c49373a vocab=1ae79f12
-/
theorem adaptiveEdgeInterval_parameter_lt (hU : IsOpen U)
    (t : K.AdaptiveFace U) (i : ZMod 3)
    (j : K.AdaptiveEdgeInterval U hU t i) :
    K.levelFaceEdgeParameter t.2.1 i
        (K.adaptiveEdgeIntervalFirst U hU t i j) <
      K.levelFaceEdgeParameter t.2.1 i
        (K.adaptiveEdgeIntervalSecond U hU t i j) := by
  let a : Fin (K.boundaryEdgeVertexList U hU t i).length :=
    ⟨j.1, by
      have hj := j.2
      omega⟩
  let b : Fin (K.boundaryEdgeVertexList U hU t i).length :=
    ⟨j.1 + 1, by
      have hj := j.2
      omega⟩
  have hab : a < b := by
    exact Nat.lt_succ_self j.1
  have hle := (K.boundaryEdgeVertexList_pairwise_parameter_le U hU t i).rel_get_of_lt hab
  have hne : K.levelFaceEdgeParameter t.2.1 i
        (K.adaptiveEdgeIntervalFirst U hU t i j) ≠
      K.levelFaceEdgeParameter t.2.1 i
        (K.adaptiveEdgeIntervalSecond U hU t i j) := by
    intro heq
    exact K.adaptiveEdgeIntervalFirst_ne_second U hU t i j
      (K.levelFaceEdgeParameter_injOn t.2.1 i
        ((K.mem_boundaryEdgeVertices_iff U hU t i _).mp
          (K.adaptiveEdgeIntervalFirst_mem_boundaryEdgeVertices U hU t i j)).2
        ((K.mem_boundaryEdgeVertices_iff U hU t i _).mp
          (K.adaptiveEdgeIntervalSecond_mem_boundaryEdgeVertices U hU t i j)).2
        heq)
  exact lt_of_le_of_ne hle hne

/-- Every parameter on an adaptive edge lies between the parameters of two consecutive
resolved boundary vertices.
@isnad1 id=ex.2h5v.s8.84804230c955 from=translated src=- shape=b9aa8d41 vocab=fe7fbf1c
-/
theorem exists_adaptiveEdgeInterval_parameter_mem_Icc (hU : IsOpen U)
    (t : K.AdaptiveFace U) (i : ZMod 3) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    ∃ j : K.AdaptiveEdgeInterval U hU t i,
      r ∈ Set.Icc
        (K.levelFaceEdgeParameter t.2.1 i
          (K.adaptiveEdgeIntervalFirst U hU t i j))
        (K.levelFaceEdgeParameter t.2.1 i
          (K.adaptiveEdgeIntervalSecond U hU t i j)) := by
  let L := K.boundaryEdgeVertexList U hU t i
  have hlength : 2 ≤ L.length :=
    K.two_le_boundaryEdgeVertexList_length U hU t i
  have hfirst : K.levelFaceEdgeParameter t.2.1 i
      (L.get ⟨0, by omega⟩) ≤ r := by
    change K.levelFaceEdgeParameter t.2.1 i
      ((K.boundaryEdgeVertexList U hU t i).get ⟨0, by
        have := K.two_le_boundaryEdgeVertexList_length U hU t i
        omega⟩) ≤ r
    rw [K.boundaryEdgeVertexList_first_parameter U hU t i]
    exact hr.1
  have hlast : r ≤ K.levelFaceEdgeParameter t.2.1 i
      (L.get ⟨L.length - 1, by omega⟩) := by
    change r ≤ K.levelFaceEdgeParameter t.2.1 i
      ((K.boundaryEdgeVertexList U hU t i).get
        ⟨(K.boundaryEdgeVertexList U hU t i).length - 1, by
          have := K.two_le_boundaryEdgeVertexList_length U hU t i
          omega⟩)
    rw [K.boundaryEdgeVertexList_last_parameter U hU t i]
    exact hr.2
  obtain ⟨j, hj⟩ := exists_adjacent_get_of_pairwise_le (r := r) L
    (K.levelFaceEdgeParameter t.2.1 i)
    hlength
    (K.boundaryEdgeVertexList_pairwise_parameter_le U hU t i)
    hfirst hlast
  refine ⟨j, ?_⟩
  have hjlt : j.1 < (K.boundaryEdgeVertexList U hU t i).length - 1 := by
    simpa only [L] using j.2
  change K.levelFaceEdgeParameter t.2.1 i
      ((K.boundaryEdgeVertexList U hU t i).get ⟨j.1, by
        omega⟩) ≤ r ∧
    r ≤ K.levelFaceEdgeParameter t.2.1 i
      ((K.boundaryEdgeVertexList U hU t i).get ⟨j.1 + 1, by
        omega⟩)
  exact hj

/-- No resolved boundary mark lies strictly between the two consecutive marks of an adaptive
edge interval.
@isnad1 id=not.2h6v.s8.1e0f6e8c13bd from=translated src=- shape=44b62f36 vocab=cc0414f9
-/
theorem not_parameter_mem_Ioo_adaptiveEdgeInterval (hU : IsOpen U)
    (t : K.AdaptiveFace U) (i : ZMod 3)
    (j : K.AdaptiveEdgeInterval U hU t i)
    {p : K.realization} (hp : p ∈ K.boundaryEdgeVertices U hU t i) :
    K.levelFaceEdgeParameter t.2.1 i p ∉ Set.Ioo
      (K.levelFaceEdgeParameter t.2.1 i
        (K.adaptiveEdgeIntervalFirst U hU t i j))
      (K.levelFaceEdgeParameter t.2.1 i
        (K.adaptiveEdgeIntervalSecond U hU t i j)) := by
  let L := K.boundaryEdgeVertexList U hU t i
  let a : Fin L.length := ⟨j.1, by
    have hj := j.2
    dsimp only [L]
    omega⟩
  let b : Fin L.length := ⟨j.1 + 1, by
    have hj := j.2
    dsimp only [L]
    omega⟩
  have hab : a < b := by
    exact Nat.lt_succ_self j.1
  have hpL : p ∈ L :=
    (K.mem_boundaryEdgeVertexList_iff U hU t i p).mpr hp
  obtain ⟨k, hk⟩ := List.get_of_mem hpL
  have hpair := K.boundaryEdgeVertexList_pairwise_parameter_le U hU t i
  intro hpBetween
  by_cases hka : k ≤ a
  · have hle : K.levelFaceEdgeParameter t.2.1 i (L.get k) ≤
        K.levelFaceEdgeParameter t.2.1 i (L.get a) := by
      rcases hka.eq_or_lt with hka | hka
      · rw [hka]
      · exact hpair.rel_get_of_lt hka
    have hpa : K.levelFaceEdgeParameter t.2.1 i p ≤
        K.levelFaceEdgeParameter t.2.1 i
          (K.adaptiveEdgeIntervalFirst U hU t i j) := by
      simpa only [hk, adaptiveEdgeIntervalFirst, L, a] using hle
    exact (not_lt_of_ge hpa) hpBetween.1
  · have hbk : b ≤ k := by
      have : a.1 < k.1 := Nat.lt_of_not_ge hka
      change j.1 < k.1 at this
      change j.1 + 1 ≤ k.1
      omega
    have hle : K.levelFaceEdgeParameter t.2.1 i (L.get b) ≤
        K.levelFaceEdgeParameter t.2.1 i (L.get k) := by
      rcases hbk.eq_or_lt with hbk | hbk
      · rw [hbk]
      · exact hpair.rel_get_of_lt hbk
    have hbp : K.levelFaceEdgeParameter t.2.1 i
          (K.adaptiveEdgeIntervalSecond U hU t i j) ≤
        K.levelFaceEdgeParameter t.2.1 i p := by
      simpa only [hk, adaptiveEdgeIntervalSecond, L, b] using hle
    exact (not_lt_of_ge hbp) hpBetween.2

/-- The countable family of fan triangles before identifying their shared geometric edges. -/
abbrev AdaptiveFanFace (hU : IsOpen U) :=
  Σ t : K.AdaptiveFace U, Σ i : ZMod 3, K.AdaptiveEdgeInterval U hU t i

/-- The finite family of all resolved fan triangles over one adaptive tile. -/
noncomputable def adaptiveFanFacesOver (hU : IsOpen U)
    (t : K.AdaptiveFace U) : Finset (K.AdaptiveFanFace U hU) :=
  ((Finset.univ : Finset (ZMod 3)).sigma fun i ↦
      (Finset.univ : Finset (K.AdaptiveEdgeInterval U hU t i))).map
    ⟨fun p ↦ ⟨t, p⟩, by
      intro p q hpq
      exact eq_of_heq (Sigma.mk.inj_iff.mp hpq).2⟩

/--
@isnad1 id=iff.1h4v.s7.70902d835005 from=translated src=- shape=adb292fa vocab=d773bcd3
-/
theorem mem_adaptiveFanFacesOver_iff (hU : IsOpen U)
    (t : K.AdaptiveFace U) (f : K.AdaptiveFanFace U hU) :
    f ∈ K.adaptiveFanFacesOver U hU t ↔ f.1 = t := by
  classical
  constructor
  · intro hf
    obtain ⟨p, -, hp⟩ := Finset.mem_map.mp hf
    exact (congrArg Sigma.fst hp).symm
  · intro hft
    subst t
    apply Finset.mem_map.mpr
    exact ⟨f.2, by simp, rfl⟩

/-- The `adaptiveFanFaceVertices` declaration. -/
noncomputable def adaptiveFanFaceVertices (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU) : Finset K.realization :=
  {K.adaptiveFaceCenter U f.1,
    K.adaptiveEdgeIntervalFirst U hU f.1 f.2.1 f.2.2,
    K.adaptiveEdgeIntervalSecond U hU f.1 f.2.1 f.2.2}

/--
@isnad1 id=eq.1h3v.s6.04f897c36067 from=translated src=- shape=b2700cb2 vocab=fd6f740a
-/
theorem adaptiveFanFaceVertices_card (hU : IsOpen U)
    (f : K.AdaptiveFanFace U hU) :
    (K.adaptiveFanFaceVertices U hU f).card = 3 := by
  have hp := K.adaptiveEdgeIntervalFirst_mem_boundaryEdgeVertices U hU
    f.1 f.2.1 f.2.2
  have hq := K.adaptiveEdgeIntervalSecond_mem_boundaryEdgeVertices U hU
    f.1 f.2.1 f.2.2
  have hcp : K.adaptiveFaceCenter U f.1 ≠
      K.adaptiveEdgeIntervalFirst U hU f.1 f.2.1 f.2.2 :=
    K.adaptiveFaceCenter_ne_boundaryVertex U hU f.1
      ((K.mem_boundaryEdgeVertices_iff U hU f.1 f.2.1 _).mp hp).1
  have hcq : K.adaptiveFaceCenter U f.1 ≠
      K.adaptiveEdgeIntervalSecond U hU f.1 f.2.1 f.2.2 :=
    K.adaptiveFaceCenter_ne_boundaryVertex U hU f.1
      ((K.mem_boundaryEdgeVertices_iff U hU f.1 f.2.1 _).mp hq).1
  have hpq := K.adaptiveEdgeIntervalFirst_ne_second U hU
    f.1 f.2.1 f.2.2
  simp [adaptiveFanFaceVertices, hcp, hcq, hpq]

end IntrinsicTwoComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
