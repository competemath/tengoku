/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.Geometry

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Rådström support-function embedding

Nonempty compact convex subsets of a finite-dimensional real inner-product
space embed isometrically into the Banach space of continuous real functions
on the closed unit ball.  The embedding sends a set to its support function.

Besides the isometry theorem, this file records the two algebraic properties
used throughout random-set limit theory: Minkowski addition becomes pointwise
addition and nonnegative dilation becomes scalar multiplication.  Thus the
Hausdorff geometry of compact convex random sets is represented faithfully by
the uniform norm of their support functions.
-/

open Set Metric TopologicalSpace
open scoped InnerProductSpace Pointwise NNReal

noncomputable section

namespace RandomSetTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The type of nonempty compact convex subsets of `E`.-/
def CompactConvexSet (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] :=
  {K : NonemptyCompacts E // Convex ℝ (K : Set E)}

namespace CompactConvexSet

instance : Coe (CompactConvexSet E) (Set E) :=
  ⟨fun K ↦ (K.1 : Set E)⟩

instance : MetricSpace (CompactConvexSet E) :=
  inferInstanceAs
    (MetricSpace {K : NonemptyCompacts E // Convex ℝ (K : Set E)})

/--
@isnad1 id=eq.1h3v.s8.6cff0c1cbde5 from=translated src=- shape=ff602ac1 vocab=bd28bf12
-/
@[ext]
theorem ext {K L : CompactConvexSet E}
    (h : (K : Set E) = (L : Set E)) : K = L := by
  apply Subtype.ext
  exact NonemptyCompacts.ext h

/--
@isnad1 id=iscompac.0h2v.s7.6d54bc826203 from=translated src=- shape=b46bc638 vocab=cf41ec19
-/
protected theorem isCompact (K : CompactConvexSet E) :
    IsCompact (K : Set E) :=
  K.1.isCompact

/--
@isnad1 id=nonempty.0h2v.s7.744791a03caa from=translated src=- shape=b46bc638 vocab=5eb7c0bc
-/
protected theorem nonempty (K : CompactConvexSet E) :
    (K : Set E).Nonempty :=
  K.1.nonempty

/--
@isnad1 id=convex.0h2v.s7.cfc9c725764b from=translated src=- shape=e1c685fe vocab=4501cbf0
-/
protected theorem convex (K : CompactConvexSet E) :
    Convex ℝ (K : Set E) :=
  K.2

/-- Bundle a nonempty compact convex set.-/
def ofSet (K : Set E) (hcompact : IsCompact K) (hne : K.Nonempty)
    (hconv : Convex ℝ K) : CompactConvexSet E :=
  ⟨⟨⟨K, hcompact⟩, hne⟩, hconv⟩

/--
@isnad1 id=eq.3h2v.s8.f9dcd9fe53ae from=translated src=- shape=aef2a7fc vocab=2bbbb676
-/
@[simp]
theorem coe_ofSet (K : Set E) (hcompact : IsCompact K) (hne : K.Nonempty)
    (hconv : Convex ℝ K) :
    (ofSet K hcompact hne hconv : Set E) = K :=
  rfl

/-- Minkowski addition on nonempty compact convex sets.-/
def minkowskiAdd (K L : CompactConvexSet E) : CompactConvexSet E :=
  ofSet ((K : Set E) + (L : Set E))
    (K.isCompact.add L.isCompact) (K.nonempty.add L.nonempty)
    (K.convex.add L.convex)

/--
@isnad1 id=eq.0h3v.s9.93aeaefcfe8b from=translated src=- shape=21a0258b vocab=860cd067
-/
@[simp]
theorem coe_minkowskiAdd (K L : CompactConvexSet E) :
    (minkowskiAdd K L : Set E) = (K : Set E) + (L : Set E) :=
  rfl

/-- Nonnegative scalar dilation on nonempty compact convex sets.-/
def nnsmul (c : ℝ≥0) (K : CompactConvexSet E) : CompactConvexSet E :=
  ofSet ((c : ℝ) • (K : Set E))
    (K.isCompact.smul (c : ℝ)) K.nonempty.smul_set
    (K.convex.smul (c : ℝ))

/--
@isnad1 id=eq.0h3v.s8.8ac469760560 from=translated src=- shape=da7b7359 vocab=c365aaa8
-/
@[simp]
theorem coe_nnsmul (c : ℝ≥0) (K : CompactConvexSet E) :
    (nnsmul c K : Set E) = (c : ℝ) • (K : Set E) :=
  rfl

/-- The singleton compact convex set.-/
def singleton (x : E) : CompactConvexSet E :=
  ofSet {x} (isCompact_singleton) (Set.singleton_nonempty x)
    (convex_singleton x)

/--
@isnad1 id=eq.0h2v.s7.a4db133b7a02 from=translated src=- shape=5725aa7d vocab=3717278e
-/
@[simp]
theorem coe_singleton (x : E) :
    (singleton x : Set E) = {x} :=
  rfl

end CompactConvexSet

section Completeness

variable [FiniteDimensional ℝ E]

/-- Closed convexification, bundled as a nonempty compact set.-/
def closedConvexHullNonemptyCompacts (K : NonemptyCompacts E) :
    NonemptyCompacts E :=
  ⟨⟨closedConvexHull ℝ (K : Set E),
    closedConvexHull_compact K.isCompact⟩,
    K.nonempty.mono subset_closedConvexHull⟩

/--
@isnad1 id=eq.0h2v.s7.bca739ad1369 from=translated src=- shape=58636511 vocab=6fd2d32c
-/
@[simp]
theorem coe_closedConvexHullNonemptyCompacts (K : NonemptyCompacts E) :
    (closedConvexHullNonemptyCompacts K : Set E) =
      closedConvexHull ℝ (K : Set E) :=
  rfl

/-- Closed convexification is a `1`-Lipschitz self-map of the Hausdorff
space of nonempty compact sets.
@isnad1 id=lipschit.0h1v.s6.dfd23468bab0 from=translated src=- shape=36b7aac6 vocab=15cb3dca
-/
theorem lipschitzWith_closedConvexHullNonemptyCompacts :
    LipschitzWith 1
      (closedConvexHullNonemptyCompacts : NonemptyCompacts E →
        NonemptyCompacts E) := by
  apply LipschitzWith.of_dist_le_mul
  intro K L
  simp only [NonemptyCompacts.dist_eq,
    coe_closedConvexHullNonemptyCompacts, NNReal.coe_one, one_mul]
  exact hausdorffDist_closedConvexHull_le
    K.isCompact L.isCompact K.nonempty L.nonempty

/-- The fixed points of bundled closed convexification are exactly the
compact convex sets.
@isnad1 id=iff.0h2v.s7.ba82a4844b69 from=translated src=- shape=0a5ae3bc vocab=c95ad40e
-/
theorem closedConvexHullNonemptyCompacts_eq_iff_convex
    (K : NonemptyCompacts E) :
    closedConvexHullNonemptyCompacts K = K ↔ Convex ℝ (K : Set E) := by
  constructor
  · intro h
    have hset : closedConvexHull ℝ (K : Set E) = (K : Set E) := by
      exact congrArg (fun L : NonemptyCompacts E ↦ (L : Set E)) h
    rw [← hset]
    exact convex_closedConvexHull
  · intro hconv
    apply NonemptyCompacts.ext
    apply Set.Subset.antisymm
    · exact closedConvexHull_min Subset.rfl hconv K.isCompact.isClosed
    · exact subset_closedConvexHull

/-- Compact convex sets form a closed subset of the Hausdorff space of
nonempty compact sets.
@isnad1 id=isclosed.0h1v.s7.b0356a6305dd from=translated src=- shape=f421249a vocab=f22e04c2
-/
theorem isClosed_compactConvexSet :
    IsClosed {K : NonemptyCompacts E | Convex ℝ (K : Set E)} := by
  have hfix : IsClosed {K : NonemptyCompacts E |
      closedConvexHullNonemptyCompacts K = K} :=
    isClosed_eq
      lipschitzWith_closedConvexHullNonemptyCompacts.continuous continuous_id
  have heq : {K : NonemptyCompacts E |
      closedConvexHullNonemptyCompacts K = K} =
      {K : NonemptyCompacts E | Convex ℝ (K : Set E)} := by
    ext K
    exact closedConvexHullNonemptyCompacts_eq_iff_convex K
  rw [← heq]
  exact hfix

/-- In finite dimension, nonempty compact convex sets are complete for the
Hausdorff metric.-/
noncomputable instance : CompleteSpace (CompactConvexSet E) :=
  isClosed_compactConvexSet.completeSpace_coe

end Completeness

section Embedding

/-- The Rådström embedding: restrict the support function to the closed unit
ball and bundle it as a continuous function.-/
def radstromEmbedding (K : CompactConvexSet E) :
    C(Metric.closedBall (0 : E) 1, ℝ) where
  toFun u := supportFunction (K : Set E) u
  continuous_toFun := by
    obtain ⟨R, hR⟩ := K.isCompact.isBounded.exists_norm_le
    have hR0 : 0 ≤ R := by
      obtain ⟨x, hx⟩ := K.nonempty
      exact (norm_nonneg x).trans (hR x hx)
    let C : NNReal := ⟨R, hR0⟩
    have hC : (C : ℝ) = R := rfl
    have hlip : LipschitzWith C (supportFunction (K : Set E)) := by
      apply LipschitzWith.of_dist_le_mul
      intro u v
      rw [hC]
      simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs] using
        (abs_supportFunction_sub_le K.isCompact K.nonempty hR u v)
    exact hlip.continuous.comp continuous_subtype_val

/--
@isnad1 id=eq.0h3v.s8.47fbfd238106 from=translated src=- shape=8d9259bf vocab=f0452692
-/
@[simp]
theorem radstromEmbedding_apply (K : CompactConvexSet E)
    (u : Metric.closedBall (0 : E) 1) :
    radstromEmbedding K u = supportFunction (K : Set E) u :=
  rfl

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- The uniform norm of the difference of two embedded support functions is
exactly their Hausdorff distance.
@isnad1 id=eq.0h3v.s9.3209808ebe6a from=translated src=- shape=18b33d35 vocab=72114e5b
-/
theorem norm_radstromEmbedding_sub_eq_hausdorffDist
    (K L : CompactConvexSet E) :
    ‖radstromEmbedding K - radstromEmbedding L‖ =
      hausdorffDist (K : Set E) (L : Set E) := by
  apply le_antisymm
  · rw [ContinuousMap.norm_le _ hausdorffDist_nonneg]
    intro u
    simp only [ContinuousMap.sub_apply, radstromEmbedding_apply,
      Real.norm_eq_abs]
    have hu : ‖(u : E)‖ ≤ 1 := by
      have hu' := u.property
      change dist (u : E) 0 ≤ 1 at hu'
      simpa only [dist_zero_right] using hu'
    calc
      |supportFunction (K : Set E) u - supportFunction (L : Set E) u| ≤
          ‖(u : E)‖ * hausdorffDist (K : Set E) (L : Set E) :=
        abs_supportFunction_sub_le_hausdorffDist
          K.isCompact L.isCompact K.nonempty L.nonempty u
      _ ≤ 1 * hausdorffDist (K : Set E) (L : Set E) :=
        mul_le_mul_of_nonneg_right hu hausdorffDist_nonneg
      _ = hausdorffDist (K : Set E) (L : Set E) := one_mul _
  · apply hausdorffDist_le_of_unitBall_supportFunction_sub_le
      K.isCompact L.isCompact K.nonempty L.nonempty K.convex L.convex
      (norm_nonneg _)
    intro u hu
    let us : Metric.closedBall (0 : E) 1 :=
      ⟨u, by simpa [Metric.mem_closedBall, dist_zero_right] using hu⟩
    have hnorm := ContinuousMap.norm_coe_le_norm
      (radstromEmbedding K - radstromEmbedding L) us
    simpa only [ContinuousMap.sub_apply, radstromEmbedding_apply,
      Real.norm_eq_abs] using hnorm

/-- The support-function representation is an isometry from compact convex
sets with Hausdorff distance into the uniform function space.
@isnad1 id=isometry.0h1v.s8.c196da7a487a from=translated src=- shape=b60bbe07 vocab=6c301e68
-/
theorem isometry_radstromEmbedding :
    Isometry (radstromEmbedding : CompactConvexSet E →
      C(Metric.closedBall (0 : E) 1, ℝ)) := by
  apply Isometry.of_dist_eq
  intro K L
  rw [dist_eq_norm]
  change ‖radstromEmbedding K - radstromEmbedding L‖ =
    hausdorffDist (K : Set E) (L : Set E)
  exact norm_radstromEmbedding_sub_eq_hausdorffDist K L

/-- In particular, a compact convex set is uniquely determined by its support
function on the unit ball.
@isnad1 id=injectiv.0h1v.s7.f8f7dfc190ea from=translated src=- shape=b60bbe07 vocab=2b38db71
-/
theorem radstromEmbedding_injective :
    Function.Injective (radstromEmbedding : CompactConvexSet E →
      C(Metric.closedBall (0 : E) 1, ℝ)) :=
  (isometry_radstromEmbedding (E := E)).injective

/-- The cone of support functions representing nonempty compact convex sets
is closed in the ambient uniform function space.
@isnad1 id=isclosed.0h1v.s8.fd949aa49b6a from=translated src=- shape=05ce3316 vocab=f0cd136f
-/
theorem isClosed_range_radstromEmbedding :
    IsClosed (Set.range (radstromEmbedding : CompactConvexSet E →
      C(Metric.closedBall (0 : E) 1, ℝ))) :=
  (isometry_radstromEmbedding (E := E)).isClosedEmbedding.isClosed_range

/-- Metric form of the Rådström identity.
@isnad1 id=eq.0h3v.s9.448c0f1c4690 from=translated src=- shape=72baf204 vocab=5f9c6398
-/
theorem dist_radstromEmbedding_eq_hausdorffDist
    (K L : CompactConvexSet E) :
    dist (radstromEmbedding K) (radstromEmbedding L) =
      hausdorffDist (K : Set E) (L : Set E) := by
  rw [(isometry_radstromEmbedding (E := E)).dist_eq]
  rfl

/-- Hausdorff convergence of compact convex sets is equivalent to uniform
convergence of their support functions.
@isnad1 id=iff.0h5v.s8.785fbe9e10d0 from=translated src=- shape=7b90aaf5 vocab=e19b1a68
-/
theorem tendsto_radstromEmbedding_iff
    {I : Type*} {l : Filter I} {K : I → CompactConvexSet E}
    {L : CompactConvexSet E} :
    Filter.Tendsto K l (nhds L) ↔
      Filter.Tendsto (fun i ↦ radstromEmbedding (K i)) l
        (nhds (radstromEmbedding L)) := by
  simpa only [Function.comp_def] using
    (isometry_radstromEmbedding (E := E)).tendsto_nhds_iff

end FiniteDimensional

/-- Rådström turns Minkowski addition into pointwise addition.
@isnad1 id=eq.0h3v.s9.23db9a0b3c22 from=translated src=- shape=988d6086 vocab=b9505f57
-/
theorem radstromEmbedding_minkowskiAdd (K L : CompactConvexSet E) :
    radstromEmbedding (CompactConvexSet.minkowskiAdd K L) =
      radstromEmbedding K + radstromEmbedding L := by
  ext u
  simp only [radstromEmbedding_apply, CompactConvexSet.coe_minkowskiAdd,
    ContinuousMap.add_apply]
  exact supportFunction_add K.isCompact L.isCompact K.nonempty L.nonempty u

/-- Rådström turns a nonnegative dilation into scalar multiplication.
@isnad1 id=eq.0h3v.s8.f12d9e9f47ca from=translated src=- shape=b8c062cc vocab=0074a002
-/
theorem radstromEmbedding_nnsmul (c : ℝ≥0) (K : CompactConvexSet E) :
    radstromEmbedding (CompactConvexSet.nnsmul c K) =
      (c : ℝ) • radstromEmbedding K := by
  ext u
  simp only [radstromEmbedding_apply, CompactConvexSet.coe_nnsmul,
    ContinuousMap.smul_apply, smul_eq_mul]
  exact supportFunction_smul_set K.isCompact K.nonempty c.coe_nonneg u

/-- Singletons are embedded as the restrictions of continuous linear
functionals `u ↦ ⟪u,x⟩`.
@isnad1 id=eq.0h3v.s8.736e5c1ec74f from=translated src=- shape=f460f3b2 vocab=9faaddc7
-/
@[simp]
theorem radstromEmbedding_singleton (x : E)
    (u : Metric.closedBall (0 : E) 1) :
    radstromEmbedding (CompactConvexSet.singleton x) u = inner ℝ (u : E) x := by
  simp only [radstromEmbedding_apply, CompactConvexSet.coe_singleton,
    supportFunction_singleton]

/-- The singleton at the origin represents the zero support function.
@isnad1 id=eq.0h1v.s8.fa702949378f from=translated src=- shape=0dc5c926 vocab=7243eee0
-/
@[simp]
theorem radstromEmbedding_singleton_zero :
    radstromEmbedding (CompactConvexSet.singleton (0 : E)) = 0 := by
  ext u
  simp

/-- The image of the Rådström embedding contains the origin.
@isnad1 id=mem.0h1v.s9.4b946a254175 from=translated src=- shape=4a22573d vocab=f069217e
-/
theorem zero_mem_range_radstromEmbedding :
    (0 : C(Metric.closedBall (0 : E) 1, ℝ)) ∈
      Set.range (radstromEmbedding : CompactConvexSet E →
        C(Metric.closedBall (0 : E) 1, ℝ)) := by
  exact ⟨CompactConvexSet.singleton 0, radstromEmbedding_singleton_zero⟩

/-- The image of the Rådström embedding is stable under addition.
@isnad1 id=mem.2h3v.s10.f8e1a0181fde from=translated src=- shape=5f257cc5 vocab=ac3515b9
-/
theorem add_mem_range_radstromEmbedding
    {f g : C(Metric.closedBall (0 : E) 1, ℝ)}
    (hf : f ∈ Set.range (radstromEmbedding : CompactConvexSet E →
      C(Metric.closedBall (0 : E) 1, ℝ)))
    (hg : g ∈ Set.range (radstromEmbedding : CompactConvexSet E →
      C(Metric.closedBall (0 : E) 1, ℝ))) :
    f + g ∈ Set.range (radstromEmbedding : CompactConvexSet E →
      C(Metric.closedBall (0 : E) 1, ℝ)) := by
  obtain ⟨K, rfl⟩ := hf
  obtain ⟨L, rfl⟩ := hg
  exact ⟨CompactConvexSet.minkowskiAdd K L,
    radstromEmbedding_minkowskiAdd K L⟩

/-- The image of the Rådström embedding is stable under nonnegative
scalar multiplication.
@isnad1 id=mem.1h3v.s10.019e395aeef3 from=translated src=- shape=a9fc801c vocab=0236a351
-/
theorem nnreal_smul_mem_range_radstromEmbedding
    (c : ℝ≥0) {f : C(Metric.closedBall (0 : E) 1, ℝ)}
    (hf : f ∈ Set.range (radstromEmbedding : CompactConvexSet E →
      C(Metric.closedBall (0 : E) 1, ℝ))) :
    (c : ℝ) • f ∈ Set.range (radstromEmbedding : CompactConvexSet E →
      C(Metric.closedBall (0 : E) 1, ℝ)) := by
  obtain ⟨K, rfl⟩ := hf
  exact ⟨CompactConvexSet.nnsmul c K, radstromEmbedding_nnsmul c K⟩

/-- The cone of support functions of nonempty compact convex sets is a
convex subset of the ambient function space.
@isnad1 id=convex.0h1v.s8.2dbfc5a80227 from=translated src=- shape=29ba0a70 vocab=d0275644
-/
theorem convex_range_radstromEmbedding :
    Convex ℝ (Set.range (radstromEmbedding : CompactConvexSet E →
      C(Metric.closedBall (0 : E) 1, ℝ))) := by
  rintro _ ⟨K, rfl⟩ _ ⟨L, rfl⟩ a b ha hb _hab
  let ca : ℝ≥0 := ⟨a, ha⟩
  let cb : ℝ≥0 := ⟨b, hb⟩
  refine ⟨CompactConvexSet.minkowskiAdd
      (CompactConvexSet.nnsmul ca K) (CompactConvexSet.nnsmul cb L), ?_⟩
  rw [radstromEmbedding_minkowskiAdd, radstromEmbedding_nnsmul,
    radstromEmbedding_nnsmul]
  rfl

/-- In finite dimension the Rådström image is a closed convex cone in the
uniform function space.
@isnad1 id=and.0h1v.s9.6e07989fa665 from=translated src=- shape=0982ad42 vocab=2a673f93
-/
theorem isClosed_convex_range_radstromEmbedding [FiniteDimensional ℝ E] :
    IsClosed (Set.range (radstromEmbedding : CompactConvexSet E →
      C(Metric.closedBall (0 : E) 1, ℝ))) ∧
    Convex ℝ (Set.range (radstromEmbedding : CompactConvexSet E →
      C(Metric.closedBall (0 : E) 1, ℝ))) :=
  ⟨isClosed_range_radstromEmbedding, convex_range_radstromEmbedding⟩

end Embedding

end RandomSetTheory
