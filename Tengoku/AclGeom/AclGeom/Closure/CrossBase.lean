/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.AclGeom.AclGeom.Geometry.Points

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Relative closure across different base fields

Let `σ : K ≃+* L` be a field isomorphism carrying the image of `k` in `K` onto the image of `l`
in `L`.  Then `σ` restricts to the compatible scalar isomorphism `k ≃+* l`, carries `k(S)` onto
`l(σ S)` and the relative algebraic closure `racl k S` onto `racl l (σ S)`, and therefore induces
an order isomorphism of closed lattices `ClosedIF k K ≃o ClosedIF l L` (blueprint §Foundation I and
the transport (20.5) of §functorial formulation).  The same-base statement is `racl_map`.

**Status:** compatible scalar, closure and closed-lattice transport are proved (#24);
the functorial packaging is proved in `Functorial.Literal`, `Functorial.FrobeniusQuotient`
and `Functorial.ChoiceIndependence`, with the stated rank and characteristic restrictions (#10).

This module is part of the formalization of the Evans–Hrushovski–Gismatullin reconstruction
theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

open IntermediateField

variable {k K l L : Type*} [Field k] [Field K] [Algebra k K] [Field l] [Field L] [Algebra l L]

namespace CrossBase

/-- A field isomorphism is compatible with the bases when it carries the image of `k` onto the
image of `l`.-/
def Compatible (σ : K ≃+* L) : Prop :=
  (algebraMap k K).fieldRange.map σ.toRingHom = (algebraMap l L).fieldRange

variable {σ : K ≃+* L}

/-- Compatibility as an equality of images of the base fields.-/
theorem Compatible.image_range (hσ : Compatible (k := k) (l := l) σ) :
    σ '' Set.range (algebraMap k K) = Set.range (algebraMap l L) := by
  have h := congrArg (fun F : Subfield L ↦ (F : Set L)) hσ
  simpa only [Subfield.coe_map, RingHom.coe_fieldRange, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom] using h

/-- The inverse of a compatible isomorphism is compatible.-/
theorem Compatible.symm (hσ : Compatible (k := k) (l := l) σ) :
    Compatible (k := l) (l := k) σ.symm := by
  unfold Compatible
  apply SetLike.coe_injective
  rw [Subfield.coe_map, ← hσ, Subfield.coe_map, Set.image_image]
  simp

/-- The identity is compatible with equal bases.-/
theorem compatible_refl : Compatible (k := k) (l := k) (RingEquiv.refl K) := by
  unfold Compatible
  apply SetLike.coe_injective
  simp [Subfield.coe_map]

/-- Composites of compatible isomorphisms are compatible.-/
theorem Compatible.trans {m M : Type*} [Field m] [Field M] [Algebra m M] {τ : L ≃+* M}
    (hσ : Compatible (k := k) (l := l) σ) (hτ : Compatible (k := l) (l := m) τ) :
    Compatible (k := k) (l := m) (σ.trans τ) := by
  unfold Compatible at *
  rw [← hτ, ← hσ, Subfield.map_map]
  rfl

/-- A compatible isomorphism sends base scalars to base scalars.-/
theorem Compatible.map_algebraMap_mem (hσ : Compatible (k := k) (l := l) σ) (c : k) :
    σ (algebraMap k K c) ∈ (algebraMap l L).fieldRange := by
  rw [← hσ]
  exact ⟨algebraMap k K c, ⟨c, rfl⟩, rfl⟩

/-- The scalar map `k →+* l` induced by a compatible field isomorphism.-/
noncomputable def baseRingHom (σ : K ≃+* L) (hσ : Compatible (k := k) (l := l) σ) : k →+* l :=
  (algebraMap l L).rangeRestrictFieldEquiv.symm.toRingHom.comp
    ((σ.toRingHom.comp (algebraMap k K)).codRestrict _ hσ.map_algebraMap_mem)

/-- The induced scalar map is compatible with `σ`.-/
theorem algebraMap_baseRingHom (hσ : Compatible (k := k) (l := l) σ) (c : k) :
    algebraMap l L (baseRingHom σ hσ c) = σ (algebraMap k K c) := by
  simp [baseRingHom]

/-- The compatible scalar isomorphism `k ≃+* l` induced by `σ`.-/
noncomputable def baseRingEquiv (σ : K ≃+* L) (hσ : Compatible (k := k) (l := l) σ) : k ≃+* l :=
  RingEquiv.ofBijective (baseRingHom σ hσ) ⟨(baseRingHom σ hσ).injective, fun d ↦ by
    have hd : algebraMap l L d ∈ (algebraMap k K).fieldRange.map σ.toRingHom := by
      rw [hσ]; exact ⟨d, rfl⟩
    obtain ⟨_, ⟨c, rfl⟩, hc⟩ := hd
    refine ⟨c, (algebraMap l L).injective ?_⟩
    rw [algebraMap_baseRingHom]
    exact hc⟩

/-- The scalar isomorphism is compatible with `σ` (blueprint §Foundation I: the induced
compatible scalar map).-/
@[simp] theorem algebraMap_baseRingEquiv (hσ : Compatible (k := k) (l := l) σ) (c : k) :
    algebraMap l L (baseRingEquiv σ hσ c) = σ (algebraMap k K c) :=
  algebraMap_baseRingHom hσ c

/-- `σ` carries `k(S)` onto `l(σ S)`.-/
theorem adjoin_map (hσ : Compatible (k := k) (l := l) σ) (S : Set K) :
    (adjoin k S).toSubfield.map σ.toRingHom = (adjoin l (σ '' S)).toSubfield := by
  rw [adjoin_toSubfield, adjoin_toSubfield, RingHom.map_field_closure, Set.image_union]
  congr 2
  simpa only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] using hσ.image_range

/-- Membership form of `adjoin_map`.-/
theorem map_mem_adjoin (hσ : Compatible (k := k) (l := l) σ) {S : Set K} {x : K}
    (hx : x ∈ adjoin k S) : σ x ∈ adjoin l (σ '' S) := by
  have h : σ x ∈ (adjoin k S).toSubfield.map σ.toRingHom := ⟨x, hx, rfl⟩
  rwa [adjoin_map hσ] at h

/-- Cross-base equivariance of the relative closure, membership form.-/
theorem map_mem_racl (hσ : Compatible (k := k) (l := l) σ) {S : Set K} {x : K}
    (hx : x ∈ racl k S) : σ x ∈ racl l (σ '' S) := by
  obtain ⟨q, hq0, hqx, hc⟩ := exists_poly_of_isAlgebraic ((mem_racl_iff k).1 hx)
  rw [mem_racl_iff]
  refine isAlgebraic_of_coeff_mem (p := q.map (σ : K →+* L))
    ((Polynomial.map_ne_zero_iff (σ : K →+* L).injective).2 hq0) ?_ fun n ↦ ?_
  · rw [Polynomial.eval_map,
      show σ x = (σ : K →+* L) x from rfl, Polynomial.eval₂_at_apply, hqx, map_zero]
  · rw [Polynomial.coeff_map]
    exact map_mem_adjoin hσ (hc n)

/-- Cross-base equivariance of the relative closure, as an equivalence.-/
theorem map_mem_racl_iff (hσ : Compatible (k := k) (l := l) σ) {S : Set K} {x : K} :
    σ x ∈ racl l (σ '' S) ↔ x ∈ racl k S := by
  refine ⟨fun h ↦ ?_, map_mem_racl hσ⟩
  have h2 := map_mem_racl hσ.symm h
  rwa [RingEquiv.symm_apply_apply,
    show σ.symm '' (σ '' S) = S by rw [← Set.image_comp]; simp] at h2

/-- Cross-base equivariance of the relative closure (blueprint Prop 4.1 with a change of base).-/
theorem image_racl (hσ : Compatible (k := k) (l := l) σ) (S : Set K) :
    σ '' (racl k S : Set K) = racl l (σ '' S) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact map_mem_racl hσ hx
  · intro hy
    refine ⟨σ.symm y, (map_mem_racl_iff hσ).1 ?_, by simp⟩
    rwa [RingEquiv.apply_symm_apply]

/-- The image of a closed intermediate field is closed.-/
theorem image_closed (hσ : Compatible (k := k) (l := l) σ) (E : ClosedIF k K) :
    σ '' (E.1 : Set K) = racl l (σ '' (E.1 : Set K)) := by
  rw [← image_racl hσ, isRAC_iff_racl_eq.1 E.2]

/-- The order isomorphism of closed lattices induced by a compatible field isomorphism.-/
def closedIFMap (σ : K ≃+* L) (hσ : Compatible (k := k) (l := l) σ) :
    ClosedIF k K ≃o ClosedIF l L where
  toFun E := ⟨racl l (σ '' (E.1 : Set K)), isRAC_racl _⟩
  invFun F := ⟨racl k (σ.symm '' (F.1 : Set L)), isRAC_racl _⟩
  left_inv E := by
    apply Subtype.ext
    apply SetLike.coe_injective
    change (racl k (σ.symm '' (racl l (σ '' (E.1 : Set K)) : Set L)) : Set K) = E.1
    rw [← image_closed hσ E, Set.image_image]
    simp only [RingEquiv.symm_apply_apply, Set.image_id']
    exact congrArg SetLike.coe (isRAC_iff_racl_eq.1 E.2)
  right_inv F := by
    apply Subtype.ext
    apply SetLike.coe_injective
    change (racl l (σ '' (racl k (σ.symm '' (F.1 : Set L)) : Set K)) : Set L) = F.1
    rw [← image_closed hσ.symm F, Set.image_image]
    simp only [RingEquiv.apply_symm_apply, Set.image_id']
    exact congrArg SetLike.coe (isRAC_iff_racl_eq.1 F.2)
  map_rel_iff' {E F} := by
    change (racl l (σ '' (E.1 : Set K)) : Set L) ⊆ racl l (σ '' (F.1 : Set K)) ↔ E.1 ≤ F.1
    rw [← image_closed hσ E, ← image_closed hσ F, Set.image_subset_image_iff σ.injective]
    rfl

/-- The transported closed field is the image of the original one.-/
@[simp] theorem coe_closedIFMap (hσ : Compatible (k := k) (l := l) σ) (E : ClosedIF k K) :
    ((closedIFMap σ hσ E).1 : Set L) = σ '' (E.1 : Set K) :=
  (image_closed hσ E).symm

/-- Transport along the identity is the identity.-/
theorem closedIFMap_refl :
    closedIFMap (RingEquiv.refl K) (compatible_refl (k := k)) = OrderIso.refl _ := by
  refine OrderIso.ext (funext fun E ↦ ?_)
  apply Subtype.ext
  apply SetLike.coe_injective
  rw [coe_closedIFMap]
  simp

/-- Transport is functorial in the field isomorphism.-/
theorem closedIFMap_trans {m M : Type*} [Field m] [Field M] [Algebra m M] {τ : L ≃+* M}
    (hσ : Compatible (k := k) (l := l) σ) (hτ : Compatible (k := l) (l := m) τ) :
    closedIFMap (σ.trans τ) (hσ.trans hτ) = (closedIFMap σ hσ).trans (closedIFMap τ hτ) := by
  refine OrderIso.ext (funext fun E ↦ ?_)
  apply Subtype.ext
  apply SetLike.coe_injective
  rw [OrderIso.trans_apply, coe_closedIFMap, coe_closedIFMap, coe_closedIFMap, RingEquiv.coe_trans,
    Set.image_comp]

end CrossBase

end AclGeom
