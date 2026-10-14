/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
module

public import Tengoku.LeanPool.LeanPool.ClassificationOfSurfaces.Moise.IntrinsicFineSubdivision

/-!
# Nested safe midpoint stages of an open polyhedron

For an open subset `U` of a finite intrinsic complex, retain at level `n` every midpoint
triangle whose whole carrier is contained in `U`.  These finite stages are nested and exhaust
`U`.  They are the finite layers used in Moise Chapter 8, Theorem 2 before adjacent frontier
subdivisions are reconciled by coning.
-/

@[expose] public section

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

namespace IntrinsicTwoComplex

variable (K : IntrinsicTwoComplex) (U : Set K.realization)

/-- The `n`-fold midpoint subdivision used at one safe stage. -/
noncomputable abbrev safeSubdivision (n : ℕ) : K.Subdivision :=
  K.iteratedMidpointSubdivision n

/-- Refined triangles whose complete transported carriers lie in the prescribed open set. -/
noncomputable def safeFaces (n : ℕ) :
    Finset (Finset (K.safeSubdivision n).refined.Vertex) := by
  classical
  exact (K.safeSubdivision n).refined.faces.filter fun t ↦
    ∀ x ∈ (K.safeSubdivision n).refined.faceCarrier t,
      (K.safeSubdivision n).homeo x ∈ U

noncomputable instance safeFacesDecidablePred (n : ℕ) :
    DecidablePred (fun t ↦ t ∈ K.safeFaces U n) :=
  fun t ↦ Finset.decidableMem t (K.safeFaces U n)

/-- The finite intrinsic subcomplex retained at level `n`. -/
noncomputable abbrev safeStage (n : ℕ) : IntrinsicTwoComplex :=
  (K.safeSubdivision n).refined.restrictFaces
    (fun t ↦ t ∈ K.safeFaces U n)

/-- Include a safe stage into the original finite realization. -/
noncomputable def safeStageInclusion (n : ℕ) :
    (K.safeStage U n).realization → K.realization :=
  (K.safeSubdivision n).homeo ∘
    (K.safeSubdivision n).refined.restrictFacesInclusion
      (fun t ↦ t ∈ K.safeFaces U n)

/--
@isnad1 id=isembedd.0h3v.s7.411b01d71bd3 from=translated src=- shape=0bfb0fb2 vocab=a63a88a7
-/
theorem isEmbedding_safeStageInclusion (n : ℕ) :
    _root_.Topology.IsEmbedding (K.safeStageInclusion U n) :=
  (K.safeSubdivision n).homeo.isEmbedding.comp
    ((K.safeSubdivision n).refined.isEmbedding_restrictFacesInclusion
      (fun t ↦ t ∈ K.safeFaces U n))

/-- Carrier of one finite safe stage in the original realization. -/
noncomputable def safeStageSupport (n : ℕ) : Set K.realization :=
  Set.range (K.safeStageInclusion U n)

/--
@isnad1 id=iscompac.0h3v.s5.329ea02135ee from=translated src=- shape=6fcc2557 vocab=1f90ed3e
-/
theorem isCompact_safeStageSupport (n : ℕ) :
    IsCompact (K.safeStageSupport U n) :=
  isCompact_range (K.isEmbedding_safeStageInclusion U n).continuous

/--
@isnad1 id=le.0h3v.s4.07f16b78ecf9 from=translated src=- shape=db5f5255 vocab=66dd4d17
-/
theorem safeStageSupport_subset (n : ℕ) : K.safeStageSupport U n ⊆ U := by
  classical
  rintro z ⟨x, rfl⟩
  rcases x.2.2 with ⟨t, ht, hxt⟩
  have htParts := (@Finset.mem_filter _ (fun t ↦ t ∈ K.safeFaces U n)
    (K.safeFacesDecidablePred U n) _ _).mp ht
  have hsafe := (Finset.mem_filter.mp htParts.2).2
  exact hsafe
    ((K.safeSubdivision n).refined.restrictFacesInclusion
      (fun s ↦ s ∈ K.safeFaces U n) x) hxt

/-- Every point of a retained old triangle is carried by a retained child at the next midpoint
level.
@isnad1 id=le.0h3v.s5.35d399c3ee55 from=translated src=- shape=32cb6f65 vocab=d154fba1
-/
theorem safeStageSupport_mono (n : ℕ) :
    K.safeStageSupport U n ⊆ K.safeStageSupport U (n + 1) := by
  classical
  rintro z ⟨x, rfl⟩
  let R := K.safeSubdivision n
  let q : R.refined.realization :=
    R.refined.restrictFacesInclusion (fun t ↦ t ∈ K.safeFaces U n) x
  rcases x.2.2 with ⟨t, ht, hqt⟩
  have htParts := (@Finset.mem_filter _ (fun t ↦ t ∈ K.safeFaces U n)
    (K.safeFacesDecidablePred U n) _ _).mp ht
  have htSafeMem : t ∈ K.safeFaces U n := htParts.2
  have htSafe := (Finset.mem_filter.mp htSafeMem).2
  let T : R.refined.Face := ⟨t, htParts.1⟩
  obtain ⟨y, s, hsOver, hys, heval⟩ :=
    R.refined.exists_midpoint_preimage_in_face T q hqt
  have hsFace : s ∈ R.refined.midpointComplex.faces := by
    change s ∈ R.refined.midpointFaces
    rw [midpointFaces]
    exact Finset.mem_biUnion.mpr ⟨T, by simp, hsOver⟩
  have hsSafe : ∀ w ∈ R.refined.midpointComplex.faceCarrier s,
      R.homeo (R.refined.midpointHomeomorph w) ∈ U := by
    intro w hw
    apply htSafe
    exact R.refined.midpointEval_mem_parentFace T hsOver w hw
  have hsMem : s ∈ K.safeFaces U (n + 1) := by
    change s ∈ R.refined.midpointComplex.faces.filter fun t ↦
      ∀ x ∈ R.refined.midpointComplex.faceCarrier t,
        R.homeo (R.refined.midpointHomeomorph x) ∈ U
    exact Finset.mem_filter.mpr ⟨hsFace, hsSafe⟩
  let y' : (K.safeStage U (n + 1)).realization :=
    ⟨y.1, y.2.1, ⟨s, (@Finset.mem_filter _
      (fun t ↦ t ∈ K.safeFaces U (n + 1)) (K.safeFacesDecidablePred U (n + 1)) _ _).mpr
        ⟨hsFace, hsMem⟩, hys⟩⟩
  refine ⟨y', ?_⟩
  apply Subtype.ext
  simp only [safeStageInclusion, Function.comp_apply]
  change (R.homeo (R.refined.midpointHomeomorph y)).1 =
    (R.homeo (R.refined.restrictFacesInclusion
      (fun t ↦ t ∈ K.safeFaces U n) x)).1
  have harg : R.refined.midpointHomeomorph y =
      R.refined.restrictFacesInclusion (fun t ↦ t ∈ K.safeFaces U n) x := by
    apply Subtype.ext
    simpa only [R.refined.midpointHomeomorph_apply,
      R.refined.midpointEval_val] using heval
  exact congrArg (fun w : K.realization ↦ w.1) (congrArg R.homeo harg)

/-- Safe-stage supports are monotone in the subdivision level.
@isnad1 id=le.1h4v.s4.495684a8b01a from=translated src=- shape=20fb505c vocab=66dd4d17
-/
theorem safeStageSupport_mono_of_le {n m : ℕ} (hnm : n ≤ m) :
    K.safeStageSupport U n ⊆ K.safeStageSupport U m := by
  induction m, hnm using Nat.le_induction with
  | base => exact Set.Subset.rfl
  | succ m _ ih => exact ih.trans (K.safeStageSupport_mono U m)

/-- A point of an open set is eventually carried by a safe midpoint triangle.
@isnad1 id=ex.2h3v.s6.b248f420ce3b from=translated src=- shape=0b18a959 vocab=0bc0b308
-/
theorem mem_safeStageSupport_of_mem (hU : IsOpen U) {p : K.realization} (hp : p ∈ U) :
    ∃ n : ℕ, p ∈ K.safeStageSupport U n := by
  classical
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU p hp
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε
    (by norm_num : (1 / 2 : ℝ) < 1)
  let R := K.safeSubdivision n
  let q : R.refined.realization := R.homeo.symm p
  rcases q.2.2 with ⟨t, ht, hqt⟩
  have htSafe : ∀ x ∈ R.refined.faceCarrier t, R.homeo x ∈ U := by
    intro x hxt
    apply hball
    rw [Metric.mem_ball]
    have hmesh := K.iteratedMidpointSubdivision_meshLE n t ht x hxt q hqt
    calc
      dist (R.homeo x) p = dist (R.homeo x) (R.homeo q) := by
        rw [R.homeo.apply_symm_apply p]
      _ ≤ (1 / 2 : ℝ) ^ n := hmesh
      _ < ε := hn
  have htMem : t ∈ K.safeFaces U n :=
    Finset.mem_filter.mpr ⟨ht, htSafe⟩
  let x : (K.safeStage U n).realization :=
    ⟨q.1, q.2.1, ⟨t, (@Finset.mem_filter _ (fun t ↦ t ∈ K.safeFaces U n)
      (K.safeFacesDecidablePred U n) _ _).mpr ⟨ht, htMem⟩, hqt⟩⟩
  refine ⟨n, x, ?_⟩
  exact R.homeo.apply_symm_apply p

/-- Every point of an open set eventually lies in the ambient interior of a finite safe stage.
This is stronger than mere exhaustion and is the compact-control input for the locally finite
shell construction.
@isnad1 id=ex.2h3v.s7.21a6ec8677cd from=translated src=- shape=73da6bce vocab=ff5469ee
-/
theorem mem_interior_safeStageSupport_of_mem (hU : IsOpen U)
    {p : K.realization} (hp : p ∈ U) :
    ∃ n : ℕ, p ∈ interior (K.safeStageSupport U n) := by
  classical
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU p hp
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε2
    (by norm_num : (1 / 2 : ℝ) < 1)
  let R := K.safeSubdivision n
  have hballSafe : Metric.ball p (ε / 2) ⊆ K.safeStageSupport U n := by
    intro z hz
    let q : R.refined.realization := R.homeo.symm z
    rcases q.2.2 with ⟨t, ht, hqt⟩
    have htSafe : ∀ x ∈ R.refined.faceCarrier t, R.homeo x ∈ U := by
      intro x hxt
      apply hball
      rw [Metric.mem_ball]
      have hmesh := K.iteratedMidpointSubdivision_meshLE n t ht x hxt q hqt
      calc
        dist (R.homeo x) p ≤ dist (R.homeo x) z + dist z p := dist_triangle _ _ _
        _ = dist (R.homeo x) (R.homeo q) + dist z p := by
          rw [R.homeo.apply_symm_apply z]
        _ ≤ (1 / 2 : ℝ) ^ n + dist z p := add_le_add hmesh le_rfl
        _ < ε / 2 + ε / 2 := add_lt_add hn hz
        _ = ε := by ring
    have htMem : t ∈ K.safeFaces U n :=
      Finset.mem_filter.mpr ⟨ht, htSafe⟩
    let x : (K.safeStage U n).realization :=
      ⟨q.1, q.2.1, ⟨t, (@Finset.mem_filter _ (fun t ↦ t ∈ K.safeFaces U n)
        (K.safeFacesDecidablePred U n) _ _).mpr ⟨ht, htMem⟩, hqt⟩⟩
    refine ⟨x, ?_⟩
    exact R.homeo.apply_symm_apply z
  refine ⟨n, interior_maximal hballSafe Metric.isOpen_ball ?_⟩
  exact Metric.mem_ball_self hε2

/-- A compact subset of an open polyhedron is eventually contained in the interior of one
finite safe stage.
@isnad1 id=ex.3h3v.s7.c611b9d7200c from=translated src=- shape=59f7ed30 vocab=c219c6ff
-/
theorem exists_safeStageSupport_interior_of_compact
    {C : Set K.realization} (hC : IsCompact C) (hU : IsOpen U) (hCU : C ⊆ U) :
    ∃ n : ℕ, C ⊆ interior (K.safeStageSupport U n) := by
  classical
  have hcover : C ⊆ ⋃ n : ℕ, interior (K.safeStageSupport U n) := by
    intro p hp
    obtain ⟨n, hn⟩ := K.mem_interior_safeStageSupport_of_mem U hU (hCU hp)
    exact Set.mem_iUnion.mpr ⟨n, hn⟩
  obtain ⟨stages, hstages⟩ := hC.elim_finite_subcover
    (fun n : ℕ ↦ interior (K.safeStageSupport U n))
    (fun _ ↦ isOpen_interior) hcover
  let N := stages.sup id
  refine ⟨N, ?_⟩
  intro p hp
  obtain ⟨n, hnStages, hpn⟩ := Set.mem_iUnion₂.mp (hstages hp)
  exact interior_mono
    (K.safeStageSupport_mono_of_le U (Finset.le_sup (f := id) hnStages)) hpn

section SafeExhaustion

variable (hU : IsOpen U)

/-- A later midpoint level whose safe support contains the given safe support in its interior.
The maximum with `n + 1` makes the selected levels strictly increase. -/
noncomputable def nextSafeStage (n : ℕ) : ℕ :=
  max (Classical.choose (K.exists_safeStageSupport_interior_of_compact U
    (K.isCompact_safeStageSupport U n) hU (K.safeStageSupport_subset U n))) (n + 1)

/--
@isnad1 id=lt.1h3v.s6.bcd307ca5e54 from=translated src=- shape=f15eba4f vocab=e617759f
-/
theorem lt_nextSafeStage (n : ℕ) : n < K.nextSafeStage U hU n := by
  exact lt_of_lt_of_le (Nat.lt_succ_self n) (Nat.le_max_right _ _)

/--
@isnad1 id=le.1h3v.s7.0e847f7b2d4d from=translated src=- shape=b228fa76 vocab=3c4c9caa
-/
theorem safeStageSupport_subset_interior_next (n : ℕ) :
    K.safeStageSupport U n ⊆ interior (K.safeStageSupport U (K.nextSafeStage U hU n)) := by
  let m := Classical.choose (K.exists_safeStageSupport_interior_of_compact U
    (K.isCompact_safeStageSupport U n) hU (K.safeStageSupport_subset U n))
  have hm : K.safeStageSupport U n ⊆ interior (K.safeStageSupport U m) :=
    Classical.choose_spec (K.exists_safeStageSupport_interior_of_compact U
      (K.isCompact_safeStageSupport U n) hU (K.safeStageSupport_subset U n))
  exact hm.trans (interior_mono (K.safeStageSupport_mono_of_le U (Nat.le_max_left _ _)))

/-- Cofinal levels selected so that consecutive finite supports are nested through interiors. -/
noncomputable def safeExhaustionIndex : ℕ → ℕ
  | 0 => 0
  | n + 1 => K.nextSafeStage U hU (safeExhaustionIndex n)

/--
@isnad1 id=eq.1h2v.s6.c215b1208552 from=translated src=- shape=92ea3707 vocab=a24b1a74
-/
@[simp] theorem safeExhaustionIndex_zero : K.safeExhaustionIndex U hU 0 = 0 := rfl

/--
@isnad1 id=eq.1h3v.s6.889c43e69b69 from=translated src=- shape=b7e62cee vocab=9db3d19a
-/
@[simp] theorem safeExhaustionIndex_succ (n : ℕ) :
    K.safeExhaustionIndex U hU (n + 1) =
      K.nextSafeStage U hU (K.safeExhaustionIndex U hU n) := rfl

/--
@isnad1 id=lt.1h3v.s6.ffc164e3fe89 from=translated src=- shape=cc369953 vocab=6e4f784c
-/
theorem safeExhaustionIndex_lt_succ (n : ℕ) :
    K.safeExhaustionIndex U hU n < K.safeExhaustionIndex U hU (n + 1) := by
  rw [K.safeExhaustionIndex_succ U hU n]
  exact K.lt_nextSafeStage U hU _

/--
@isnad1 id=le.1h3v.s6.b9894a1a64bf from=translated src=- shape=f15eba4f vocab=9b21c995
-/
theorem id_le_safeExhaustionIndex (n : ℕ) : n ≤ K.safeExhaustionIndex U hU n := by
  induction n with
  | zero => simp
  | succ n ih =>
      exact Nat.succ_le_of_lt (ih.trans_lt (K.safeExhaustionIndex_lt_succ U hU n))

/--
@isnad1 id=le.2h4v.s6.491ecb064b49 from=translated src=- shape=9fd1c2d5 vocab=9b21c995
-/
theorem safeExhaustionIndex_mono {n m : ℕ} (hnm : n ≤ m) :
    K.safeExhaustionIndex U hU n ≤ K.safeExhaustionIndex U hU m := by
  induction m, hnm using Nat.le_induction with
  | base => exact le_rfl
  | succ m _ ih => exact ih.trans (K.safeExhaustionIndex_lt_succ U hU m).le

/-- The selected compact exhaustion stage. -/
noncomputable def safeExhaustion (n : ℕ) : Set K.realization :=
  K.safeStageSupport U (K.safeExhaustionIndex U hU n)

/--
@isnad1 id=iscompac.1h3v.s6.4fb45fcab1e7 from=translated src=- shape=4ca0b5ab vocab=e43e886b
-/
theorem isCompact_safeExhaustion (n : ℕ) : IsCompact (K.safeExhaustion U hU n) :=
  K.isCompact_safeStageSupport U _

/--
@isnad1 id=le.1h3v.s6.d489860ef8af from=translated src=- shape=dc120e49 vocab=124114aa
-/
theorem safeExhaustion_subset (n : ℕ) : K.safeExhaustion U hU n ⊆ U :=
  K.safeStageSupport_subset U _

/--
@isnad1 id=le.1h3v.s7.fa1dbebfa4ea from=translated src=- shape=1c719272 vocab=366267b0
-/
theorem safeExhaustion_subset_interior_succ (n : ℕ) :
    K.safeExhaustion U hU n ⊆ interior (K.safeExhaustion U hU (n + 1)) := by
  exact K.safeStageSupport_subset_interior_next U hU _

/--
@isnad1 id=le.1h3v.s6.a3c49c2a34ba from=translated src=- shape=929ae211 vocab=8bf55435
-/
theorem safeExhaustion_mono (n : ℕ) :
    K.safeExhaustion U hU n ⊆ K.safeExhaustion U hU (n + 1) :=
  (K.safeExhaustion_subset_interior_succ U hU n).trans interior_subset

/--
@isnad1 id=le.2h4v.s6.85b0f92054ee from=translated src=- shape=a7e0122a vocab=124114aa
-/
theorem safeExhaustion_mono_of_le {n m : ℕ} (hnm : n ≤ m) :
    K.safeExhaustion U hU n ⊆ K.safeExhaustion U hU m := by
  exact K.safeStageSupport_mono_of_le U
    (K.safeExhaustionIndex_mono U hU hnm)

/--
@isnad1 id=eq.1h2v.s6.605af61d2157 from=translated src=- shape=1226c96d vocab=190b5168
-/
theorem iUnion_safeExhaustion : (⋃ n : ℕ, K.safeExhaustion U hU n) = U := by
  apply Set.Subset.antisymm
  · intro p hp
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hp
    exact K.safeExhaustion_subset U hU n hn
  · intro p hp
    obtain ⟨n, hn⟩ := K.mem_safeStageSupport_of_mem U hU hp
    apply Set.mem_iUnion.mpr
    refine ⟨n, K.safeStageSupport_mono_of_le U (K.id_le_safeExhaustionIndex U hU n) hn⟩

/--
@isnad1 id=eq.1h2v.s6.54572a73857d from=translated src=- shape=5183c1f0 vocab=2aa3c997
-/
theorem iUnion_interior_safeExhaustion :
    (⋃ n : ℕ, interior (K.safeExhaustion U hU n)) = U := by
  apply Set.Subset.antisymm
  · intro p hp
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hp
    exact K.safeExhaustion_subset U hU n (interior_subset hn)
  · intro p hp
    obtain ⟨n, hn⟩ := K.mem_interior_safeStageSupport_of_mem U hU hp
    apply Set.mem_iUnion.mpr
    refine ⟨n, interior_mono ?_ hn⟩
    exact K.safeStageSupport_mono_of_le U (K.id_le_safeExhaustionIndex U hU n)

/-- The compact shells of the selected exhaustion, regarded in the open subspace.  Shell zero
is the first compact stage; shell `n + 1` is the next stage with the interior of stage `n`
removed. -/
noncomputable def safeShell : ℕ → Set U
  | 0 => Subtype.val ⁻¹' K.safeExhaustion U hU 0
  | n + 1 => Subtype.val ⁻¹'
      (K.safeExhaustion U hU (n + 1) \ interior (K.safeExhaustion U hU n))

/-- The exhaustion shells are locally finite in `U`.  They may accumulate at the frontier in
the original compact realization, which is precisely why the ambient space here is the open
subspace.
@isnad1 id=locallyf.1h2v.s7.564e528e5ae2 from=translated src=- shape=a33a624d vocab=e32e99bd
-/
theorem locallyFinite_safeShell : LocallyFinite (K.safeShell U hU) := by
  intro x
  have hxUnion : x.1 ∈ ⋃ n : ℕ, interior (K.safeExhaustion U hU n) := by
    rw [K.iUnion_interior_safeExhaustion U hU]
    exact x.2
  obtain ⟨k, hxk⟩ := Set.mem_iUnion.mp hxUnion
  let V : Set U := Subtype.val ⁻¹' interior (K.safeExhaustion U hU k)
  refine ⟨V, ?_, ?_⟩
  · exact (isOpen_interior.preimage continuous_subtype_val).mem_nhds hxk
  · apply (Finset.finite_toSet (Finset.range (k + 1))).subset
    intro n hn
    rw [Finset.mem_coe, Finset.mem_range]
    by_contra hnlt
    have hkn : k + 1 ≤ n := Nat.le_of_not_gt hnlt
    rcases n with _ | n
    · omega
    · obtain ⟨y, hyShell, hyV⟩ := hn
      have hky : y.1 ∈ interior (K.safeExhaustion U hU n) := by
        exact interior_mono (K.safeExhaustion_mono_of_le U hU (by omega)) hyV
      exact hyShell.2 hky

end SafeExhaustion

/-- The nested finite safe stages cover exactly the prescribed open set.
@isnad1 id=eq.1h2v.s6.ea079d590b97 from=translated src=- shape=bfc22c2b vocab=84667b12
-/
theorem iUnion_safeStageSupport (hU : IsOpen U) :
    (⋃ n : ℕ, K.safeStageSupport U n) = U := by
  apply Set.Subset.antisymm
  · intro p hp
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hp
    exact K.safeStageSupport_subset U n hn
  · intro p hp
    obtain ⟨n, hn⟩ := K.mem_safeStageSupport_of_mem U hU hp
    exact Set.mem_iUnion.mpr ⟨n, hn⟩

end IntrinsicTwoComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
