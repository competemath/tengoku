/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import Tengoku.AclGeom.AclGeom.Geometry.FiniteRank
import Tengoku.AclGeom.AclGeom.Closure.Ambient
import Tengoku.Seed.Logic.Equiv.Set

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Transport between the point and lattice presentations

A closure-preserving equivalence of point geometries induces a unique order
isomorphism of closed intermediate-field lattices, and restricting it to atoms
recovers the original equivalence. Conversely, an order isomorphism transports
independent point tuples, finite geometric ranks, and arbitrary independent
families of field representatives. Exact finite geometric rank agrees with
transcendence degree, which is invariant with universe lifts when necessary.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin reconstruction
theorem; the source of truth is `sources/blueprint.tex`.

These are the presentation and dimension interfaces used by the lattice form
of M5 transfer and the rank-five reconstruction variants (issues #7, #9, #24).

**Status:** the presentation transport and transcendence-degree invariant are
proved; the other foundational carryovers are tracked in issue #24.
-/
namespace AclGeom
noncomputable section

universe u v
variable {k K l L : Type*} [Field k] [Field K] [Algebra k K]
  [Field l] [Field L] [Algebra l L]

section PointPresentation

end PointPresentation

section FiniteRankTransport

/-- An order isomorphism preserves independence of a finite point tuple.
This is the rank-transport step used by the lattice form of reconstruction.
@isnad1 id=iff.0h7v.s7.ea4c2f81e313 from=translated src=- shape=38ac9c84 vocab=457dffef
-/
theorem pointIndep_map_iff (e : ClosedIF k K ≃o ClosedIF l L)
    {n : ℕ} (f : Fin n → Point k K) :
    PointIndep l L (Point.map e ∘ f) ↔ PointIndep k K f := by
  unfold PointIndep
  apply forall_congr'
  intro i
  have himage : (Point.map e ∘ f) '' {j | j ≠ i} =
      Point.map e '' (f '' {j | j ≠ i}) :=
    (Set.image_image (Point.map e) f _).symm
  rw [himage]
  exact not_congr (pointCl_map_iff e)

/-- An order isomorphism carries the join of a tuple of points to the join
of the transported tuple.
@isnad1 id=eq.0h7v.s9.c2cf68d7cdae from=translated src=- shape=217b265a vocab=8049dada
-/
theorem point_map_iSup (e : ClosedIF k K ≃o ClosedIF l L)
    {n : ℕ} (f : Fin n → Point k K) :
    (⨆ i, (Point.map e (f i)).1) = e (⨆ i, (f i).1) := by
  simp only [Point.map_coe, e.map_iSup]

/-- Order isomorphisms preserve finite geometric rank bounds.
@isnad1 id=iff.0h7v.s8.de7e2b7e1724 from=translated src=- shape=17f9b381 vocab=14d197bc
-/
theorem rankLE_map_iff (e : ClosedIF k K ≃o ClosedIF l L)
    (n : ℕ) (E : ClosedIF k K) : RankLE n (e E) ↔ RankLE n E := by
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨Point.map e.symm ∘ f, ?_⟩
    change E ≤ ⨆ i, (Point.map e.symm (f i)).1
    rw [point_map_iSup]
    simpa only [e.symm_apply_apply] using e.symm.monotone hf
  · rintro ⟨f, hf⟩
    refine ⟨Point.map e ∘ f, ?_⟩
    change e E ≤ ⨆ i, (Point.map e (f i)).1
    rw [point_map_iSup]
    exact e.monotone hf

/-- Order isomorphisms preserve exact finite geometric rank.
@isnad1 id=iff.0h7v.s8.47cdf3c616b2 from=translated src=- shape=17f9b381 vocab=c7069fd1
-/
theorem rankEq_map_iff (e : ClosedIF k K ≃o ClosedIF l L)
    (n : ℕ) (E : ClosedIF k K) : RankEq n (e E) ↔ RankEq n E := by
  constructor
  · rintro ⟨f, hf, hE⟩
    refine ⟨Point.map e.symm ∘ f, (pointIndep_map_iff e.symm f).2 hf, ?_⟩
    change E = ⨆ i, (Point.map e.symm (f i)).1
    rw [point_map_iSup]
    simpa only [e.symm_apply_apply] using congrArg e.symm hE
  · rintro ⟨f, hf, hE⟩
    refine ⟨Point.map e ∘ f, (pointIndep_map_iff e f).2 hf, ?_⟩
    change e E = ⨆ i, (Point.map e (f i)).1
    rw [point_map_iSup]
    exact congrArg e hE

end FiniteRankTransport

section IndependentFamilies

/-- A lattice isomorphism transports an arbitrary independent family of
point generators to independent representatives of the image points.
The named consumer is transcendence-degree preservation.
@isnad1 id=algebrai.1h7v.s8.92184f7b401e from=translated src=- shape=132d7489 vocab=6fb2073a
-/
theorem algebraicIndependent_pointMap_rep {ι : Type*} {v : ι → K}
    (hv : AlgebraicIndependent k v) (e : ClosedIF k K ≃o ClosedIF l L) :
    AlgebraicIndependent l (fun i ↦
      (Point.map e (Point.mk' k (v i)
        (fun hi ↦ hv.transcendental i (ClosedIF.mem_bot_iff.1 hi)))).rep) := by
  classical
  let f : ι → Point k K := fun i ↦ Point.mk' k (v i)
    (fun hi ↦ hv.transcendental i (ClosedIF.mem_bot_iff.1 hi))
  change AlgebraicIndependent l (fun i ↦ (Point.map e (f i)).rep)
  rw [algebraicIndependent_iff_forall_notMem_racl]
  intro i hi
  have hp : Point.map e (f i) ∈ pointCl (Point.map e '' (f '' {i}ᶜ)) := by
    apply mem_pointCl_iff_rep_mem.2
    simpa only [Set.image_image, Function.comp_apply] using hi
  have hpi : f i ∈ pointCl (f '' {i}ᶜ) := (pointCl_map_iff e).1 hp
  have hvspan : v i ∈ sSup (Subtype.val '' (f '' {i}ᶜ)) :=
    ClosedIF.point_le_iff.1 (mem_pointCl_iff.1 hpi)
  have himage : Subtype.val '' (f '' {i}ᶜ) =
      (fun x ↦ ClosedIF.point k x) '' (v '' {i}ᶜ) := by
    exact (Set.image_image (Subtype.val : Point k K → ClosedIF k K) f {i}ᶜ).trans
      (Set.image_image (fun x ↦ ClosedIF.point k x) v {i}ᶜ).symm
  rw [himage] at hvspan
  change v i ∈ (sSup ((fun x ↦ ClosedIF.point k x) '' (v '' {i}ᶜ))).1 at hvspan
  rw [sSup_point_image] at hvspan
  exact (algebraicIndependent_iff_forall_notMem_racl.1 hv i) hvspan

section TranscendenceDegree
variable {k₁ : Type*} {K₁ : Type u} {k₂ : Type*} {K₂ : Type v}
  [Field k₁] [Field K₁] [Algebra k₁ K₁]
  [Field k₂] [Field K₂] [Algebra k₂ K₂]

/-- An order isomorphism transports a transcendence basis to an independent
family of the same cardinality, so transcendence degree cannot decrease.
@isnad1 id=le.0h5v.s7.a8bf0fa327fd from=translated src=- shape=3d88907e vocab=3d8dcb67
-/
theorem lift_trdeg_le_of_orderIso (e : ClosedIF k₁ K₁ ≃o ClosedIF k₂ K₂) :
    Cardinal.lift.{v} (Algebra.trdeg k₁ K₁) ≤
      Cardinal.lift.{u} (Algebra.trdeg k₂ K₂) := by
  classical
  obtain ⟨S, hS⟩ := exists_isTranscendenceBasis k₁ K₁
  have hi := algebraicIndependent_pointMap_rep hS.1 e
  have hcard := hi.lift_cardinalMk_le_trdeg
  simpa only [hS.cardinalMk_eq_trdeg] using hcard

end TranscendenceDegree

end IndependentFamilies

section NumericalRank
open IntermediateField

/-- An independent family is a transcendence basis exactly when its relative
algebraic closure is the whole field. Used by the finite-rank bridge.
@isnad1 id=iff.1h4v.s7.ab575228ba13 from=translated src=- shape=e5e85e7e vocab=70a17b17
-/
theorem isTranscendenceBasis_iff_racl_range_eq_top {ι : Type*} {v : ι → K}
    (hv : AlgebraicIndependent k v) :
    IsTranscendenceBasis k v ↔ racl k (Set.range v) = ⊤ := by
  rw [hv.isTranscendenceBasis_iff_isAlgebraic]
  constructor
  · intro h
    have := h
    apply top_unique
    intro z _
    exact (mem_racl_iff_isAlgebraic_adjoin k).2
      (Algebra.IsAlgebraic.isAlgebraic z)
  · intro h
    refine ⟨fun z ↦ (mem_racl_iff_isAlgebraic_adjoin k).1 ?_⟩
    exact h ▸ (show z ∈ (⊤ : IntermediateField k K) from mem_top)

/-- The finite geometric rank of a closed field equals its transcendence
degree. This is the numerical rank interface in blueprint Foundation II.
@isnad1 id=eq.1h4v.s7.38ae019c0b93 from=translated src=- shape=2e85d1ca vocab=f2f6157f
-/
theorem RankEq.trdeg_eq {n : ℕ} {E : ClosedIF k K} (h : RankEq n E) :
    Algebra.trdeg k (↥E.1) = n := by
  classical
  obtain ⟨f, hf, hspan⟩ := h
  have hrep : ∀ i, (f i).rep ∈ E := by
    intro i
    rw [hspan]
    exact (le_iSup (fun j ↦ (f j).1) i) (f i).mem_rep
  let v : Fin n → E.1 := fun i ↦ ⟨(f i).rep, hrep i⟩
  have hv : AlgebraicIndependent k v :=
    AlgebraicIndependent.of_comp E.1.val (algebraicIndependent_rep_of_pointIndep hf)
  have hclosure : racl k (Set.range v) = ⊤ := by
    apply top_unique
    intro z _
    apply (algHom_mem_racl_image_iff E.1.val).1
    have himage : E.1.val '' Set.range v = Set.range fun i ↦ (f i).rep := by
      ext x
      simp [v]
    rw [himage]
    have hE : E.1 = racl k (Set.range fun i ↦ (f i).rep) := by
      rw [hspan, iSup_point_val]
    exact hE ▸ z.2
  have hb : IsTranscendenceBasis k v :=
    (isTranscendenceBasis_iff_racl_range_eq_top hv).2 hclosure
  simpa using hb.lift_cardinalMk_eq_trdeg.symm

end NumericalRank

end
end AclGeom
