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

@[ext]
theorem ext {K L : CompactConvexSet E}
    (h : (K : Set E) = (L : Set E)) : K = L := by
  apply Subtype.ext
  exact NonemptyCompacts.ext h

protected theorem isCompact (K : CompactConvexSet E) :
    IsCompact (K : Set E) :=
  K.1.isCompact

protected theorem nonempty (K : CompactConvexSet E) :
    (K : Set E).Nonempty :=
  K.1.nonempty

protected theorem convex (K : CompactConvexSet E) :
    Convex ℝ (K : Set E) :=
  K.2

/-- Bundle a nonempty compact convex set.-/
def ofSet (K : Set E) (hcompact : IsCompact K) (hne : K.Nonempty)
    (hconv : Convex ℝ K) : CompactConvexSet E :=
  ⟨⟨⟨K, hcompact⟩, hne⟩, hconv⟩

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

@[simp]
theorem coe_minkowskiAdd (K L : CompactConvexSet E) :
    (minkowskiAdd K L : Set E) = (K : Set E) + (L : Set E) :=
  rfl

/-- Nonnegative scalar dilation on nonempty compact convex sets.-/
def nnsmul (c : ℝ≥0) (K : CompactConvexSet E) : CompactConvexSet E :=
  ofSet ((c : ℝ) • (K : Set E))
    (K.isCompact.smul (c : ℝ)) K.nonempty.smul_set
    (K.convex.smul (c : ℝ))

@[simp]
theorem coe_nnsmul (c : ℝ≥0) (K : CompactConvexSet E) :
    (nnsmul c K : Set E) = (c : ℝ) • (K : Set E) :=
  rfl

/-- The singleton compact convex set.-/
def singleton (x : E) : CompactConvexSet E :=
  ofSet {x} (isCompact_singleton) (Set.singleton_nonempty x)
    (convex_singleton x)

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

@[simp]
theorem coe_closedConvexHullNonemptyCompacts (K : NonemptyCompacts E) :
    (closedConvexHullNonemptyCompacts K : Set E) =
      closedConvexHull ℝ (K : Set E) :=
  rfl

/-- Closed convexification is a `1`-Lipschitz self-map of the Hausdorff
space of nonempty compact sets.-/
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
compact convex sets.-/
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
nonempty compact sets.-/
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

@[simp]
theorem radstromEmbedding_apply (K : CompactConvexSet E)
    (u : Metric.closedBall (0 : E) 1) :
    radstromEmbedding K u = supportFunction (K : Set E) u :=
  rfl

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- The uniform norm of the difference of two embedded support functions is
exactly their Hausdorff distance.-/
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
sets with Hausdorff distance into the uniform function space.-/
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
function on the unit ball.-/
theorem radstromEmbedding_injective :
    Function.Injective (radstromEmbedding : CompactConvexSet E →
      C(Metric.closedBall (0 : E) 1, ℝ)) :=
  (isometry_radstromEmbedding (E := E)).injective

/-- The cone of support functions representing nonempty compact convex sets
is closed in the ambient uniform function space.-/
theorem isClosed_range_radstromEmbedding :
    IsClosed (Set.range (radstromEmbedding : CompactConvexSet E →
      C(Metric.closedBall (0 : E) 1, ℝ))) :=
  (isometry_radstromEmbedding (E := E)).isClosedEmbedding.isClosed_range

/-- Metric form of the Rådström identity.-/
theorem dist_radstromEmbedding_eq_hausdorffDist
    (K L : CompactConvexSet E) :
    dist (radstromEmbedding K) (radstromEmbedding L) =
      hausdorffDist (K : Set E) (L : Set E) := by
  rw [(isometry_radstromEmbedding (E := E)).dist_eq]
  rfl

/-- Hausdorff convergence of compact convex sets is equivalent to uniform
convergence of their support functions.-/
theorem tendsto_radstromEmbedding_iff
    {I : Type*} {l : Filter I} {K : I → CompactConvexSet E}
    {L : CompactConvexSet E} :
    Filter.Tendsto K l (nhds L) ↔
      Filter.Tendsto (fun i ↦ radstromEmbedding (K i)) l
        (nhds (radstromEmbedding L)) := by
  simpa only [Function.comp_def] using
    (isometry_radstromEmbedding (E := E)).tendsto_nhds_iff

end FiniteDimensional

/-- Rådström turns Minkowski addition into pointwise addition.-/
theorem radstromEmbedding_minkowskiAdd (K L : CompactConvexSet E) :
    radstromEmbedding (CompactConvexSet.minkowskiAdd K L) =
      radstromEmbedding K + radstromEmbedding L := by
  ext u
  simp only [radstromEmbedding_apply, CompactConvexSet.coe_minkowskiAdd,
    ContinuousMap.add_apply]
  exact supportFunction_add K.isCompact L.isCompact K.nonempty L.nonempty u

/-- Rådström turns a nonnegative dilation into scalar multiplication.-/
theorem radstromEmbedding_nnsmul (c : ℝ≥0) (K : CompactConvexSet E) :
    radstromEmbedding (CompactConvexSet.nnsmul c K) =
      (c : ℝ) • radstromEmbedding K := by
  ext u
  simp only [radstromEmbedding_apply, CompactConvexSet.coe_nnsmul,
    ContinuousMap.smul_apply, smul_eq_mul]
  exact supportFunction_smul_set K.isCompact K.nonempty c.coe_nonneg u

/-- Singletons are embedded as the restrictions of continuous linear
functionals `u ↦ ⟪u,x⟩`.-/
@[simp]
theorem radstromEmbedding_singleton (x : E)
    (u : Metric.closedBall (0 : E) 1) :
    radstromEmbedding (CompactConvexSet.singleton x) u = inner ℝ (u : E) x := by
  simp only [radstromEmbedding_apply, CompactConvexSet.coe_singleton,
    supportFunction_singleton]

/-- The singleton at the origin represents the zero support function.-/
@[simp]
theorem radstromEmbedding_singleton_zero :
    radstromEmbedding (CompactConvexSet.singleton (0 : E)) = 0 := by
  ext u
  simp

/-- The image of the Rådström embedding contains the origin.-/
theorem zero_mem_range_radstromEmbedding :
    (0 : C(Metric.closedBall (0 : E) 1, ℝ)) ∈
      Set.range (radstromEmbedding : CompactConvexSet E →
        C(Metric.closedBall (0 : E) 1, ℝ)) := by
  exact ⟨CompactConvexSet.singleton 0, radstromEmbedding_singleton_zero⟩

/-- The image of the Rådström embedding is stable under addition.-/
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
scalar multiplication.-/
theorem nnreal_smul_mem_range_radstromEmbedding
    (c : ℝ≥0) {f : C(Metric.closedBall (0 : E) 1, ℝ)}
    (hf : f ∈ Set.range (radstromEmbedding : CompactConvexSet E →
      C(Metric.closedBall (0 : E) 1, ℝ))) :
    (c : ℝ) • f ∈ Set.range (radstromEmbedding : CompactConvexSet E →
      C(Metric.closedBall (0 : E) 1, ℝ)) := by
  obtain ⟨K, rfl⟩ := hf
  exact ⟨CompactConvexSet.nnsmul c K, radstromEmbedding_nnsmul c K⟩

/-- The cone of support functions of nonempty compact convex sets is a
convex subset of the ambient function space.-/
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
uniform function space.-/
theorem isClosed_convex_range_radstromEmbedding [FiniteDimensional ℝ E] :
    IsClosed (Set.range (radstromEmbedding : CompactConvexSet E →
      C(Metric.closedBall (0 : E) 1, ℝ))) ∧
    Convex ℝ (Set.range (radstromEmbedding : CompactConvexSet E →
      C(Metric.closedBall (0 : E) 1, ℝ))) :=
  ⟨isClosed_range_radstromEmbedding, convex_range_radstromEmbedding⟩

end Embedding

end RandomSetTheory
