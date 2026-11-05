/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.AclGeom.AclGeom.Geometry.Points

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Equivalence of the lattice and point-geometry presentations

The combinatorial geometry attached to `𝒢(K/k)` has as points the atoms of
the closed lattice, with closure
`pointCl S = {P | P ≤ ⨆ (Q ∈ S), Q}`. This file provides
(blueprint §Point geometry and equivalence of presentations):

* `Point k K` and `pointCl`, with extensivity, monotonicity, idempotence;
* `Point.rep`/`Point.point_rep`: a chosen generator for each point;
* `sSup_point_image`: the supremum of points of generators is the relative
  algebraic closure of the set of generators — the bridge between point
  suprema and `racl`;
* exchange for `pointCl` (`pointCl_exchange`);
* the inverse order isomorphisms between `ClosedIF k K` and the closed point
  sets (`ClosedIF.pointSetIso`);
* transport of order isomorphisms of closed lattices to geometry
  equivalences of the point geometries (`Point.map`, `pointCl_map_iff` —
  blueprint eq. 20.3).

Finite character of `pointCl` lives with the finite-rank predicates in
`AclGeom.Geometry.FiniteRank`. The converse from closure-preserving point
equivalences to lattice isomorphisms, with both round trips, is proved in
`AclGeom.Geometry.Transport`.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** M1, checklist F5 — complete.
-/

namespace AclGeom

open IntermediateField

noncomputable section

variable {k : Type*} {K : Type*} [Field k] [Field K] [Algebra k K]

variable (k K) in
/-- The points of the combinatorial geometry of `K/k`: atoms of the closed
lattice `𝒢(K/k)`.-/
def Point := {P : ClosedIF k K // IsAtom P}

namespace Point

instance : PartialOrder (Point k K) := Subtype.partialOrder _

/-- A chosen generator of a point: `P = point k (P.rep)`.-/
def rep (P : Point k K) : K :=
  (ClosedIF.IsAtom.exists_eq_point P.2).choose

/--
@isnad1 id=not.0h3v.s7.62881381a25a from=translated src=- shape=5f74bcf5 vocab=4a99f6ea
-/
theorem rep_notMem_bot (P : Point k K) : P.rep ∉ (⊥ : ClosedIF k K) :=
  (ClosedIF.IsAtom.exists_eq_point P.2).choose_spec.1

/--
@isnad1 id=eq.0h3v.s7.50898e69b2ef from=translated src=- shape=6db09fa5 vocab=fbe01232
-/
@[simp] theorem point_rep (P : Point k K) : ClosedIF.point k P.rep = P.1 :=
  (ClosedIF.IsAtom.exists_eq_point P.2).choose_spec.2.symm

/--
@isnad1 id=mem.0h3v.s7.4bc07bc3c94b from=translated src=- shape=60fe316f vocab=0c18c04a
-/
theorem mem_rep (P : Point k K) : P.rep ∈ P.1 := by
  rw [← point_rep]
  exact ClosedIF.mem_point_self _

end Point

variable (k) in
/-- The point attached to an element `x ∉ ⊥`.-/
def Point.mk' (x : K) (hx : x ∉ (⊥ : ClosedIF k K)) : Point k K :=
  ⟨ClosedIF.point k x, ClosedIF.isAtom_point hx⟩

/-- The closure operation of the point geometry: `P` lies in the closure of
`S` when `P` is below the join of `S` (blueprint §Foundation II).-/
def pointCl (S : Set (Point k K)) : Set (Point k K) :=
  {P | P.1 ≤ sSup (Subtype.val '' S)}

/--
@isnad1 id=iff.0h4v.s8.dd030b9eba68 from=translated src=- shape=c404b2aa vocab=85c936eb
-/
theorem mem_pointCl_iff {S : Set (Point k K)} {P : Point k K} :
    P ∈ pointCl S ↔ P.1 ≤ sSup (Subtype.val '' S) := Iff.rfl

/--
@isnad1 id=le.0h3v.s5.dbe1de9b8fed from=translated src=- shape=f9a4024e vocab=ff52a359
-/
theorem subset_pointCl (S : Set (Point k K)) : S ⊆ pointCl S :=
  fun P hP ↦ mem_pointCl_iff.2 (le_sSup ⟨P, hP, rfl⟩)

/-- The supremum of the points of a set of generators is the relative
algebraic closure of that set: the bridge between the point geometry and
`racl`.
@isnad1 id=eq.0h3v.s6.54f29d8f8fca from=translated src=- shape=fdc174a5 vocab=b44adfec
-/
theorem sSup_point_image (A : Set K) :
    (sSup ((fun x ↦ ClosedIF.point k x) '' A)).1 = racl k A := by
  refine le_antisymm ?_ ?_
  · have h : sSup ((fun x ↦ ClosedIF.point k x) '' A) ≤
        ⟨racl k A, isRAC_racl A⟩ := by
      refine sSup_le ?_
      rintro - ⟨x, hx, rfl⟩
      exact ClosedIF.point_le_iff.2 (subset_racl k A hx)
    exact ClosedIF.le_iff.1 h
  · have h : A ⊆ ((sSup ((fun x ↦ ClosedIF.point k x) '' A)).1 : Set K) := by
      intro x hx
      have : ClosedIF.point k x ≤ sSup ((fun x ↦ ClosedIF.point k x) '' A) :=
        le_sSup ⟨x, hx, rfl⟩
      exact (ClosedIF.le_iff.1 this) (ClosedIF.mem_point_self x)
    calc racl k A ≤ racl k ((sSup ((fun x ↦ ClosedIF.point k x) '' A)).1 : Set K) :=
          racl_mono h
    _ = _ := isRAC_iff_racl_eq.1 (sSup ((fun x ↦ ClosedIF.point k x) '' A)).2

/-- Membership in a point closure, in terms of representatives: `P ∈ cl S`
iff the generator of `P` is algebraic over the generators of `S`.
@isnad1 id=iff.0h4v.s6.d43d09149890 from=translated src=- shape=e60337a5 vocab=2f515459
-/
theorem mem_pointCl_iff_rep_mem {S : Set (Point k K)} {P : Point k K} :
    P ∈ pointCl S ↔ P.rep ∈ racl k (Point.rep '' S) := by
  have himg : (fun x ↦ ClosedIF.point k x) '' (Point.rep '' S) = Subtype.val '' S := by
    rw [← Set.image_comp]
    exact Set.image_congr fun Q _ ↦ Q.point_rep
  have hval : ((sSup (Subtype.val '' S)).1 : IntermediateField k K)
      = racl k (Point.rep '' S) := by
    rw [← himg]
    exact sSup_point_image _
  rw [mem_pointCl_iff, ← P.point_rep, ClosedIF.point_le_iff]
  change P.rep ∈ (sSup (Subtype.val '' S)).1 ↔ _
  rw [hval]

section PointSetIso

variable (k K) in
/-- The closed point sets: fixed points of `pointCl`.-/
def ClosedPointSet := {S : Set (Point k K) // pointCl S = S}

instance : PartialOrder (ClosedPointSet k K) := Subtype.partialOrder _

namespace ClosedIF

/-- The set of points below a closed intermediate field.-/
def toPointSet (E : ClosedIF k K) : Set (Point k K) :=
  {P | P.1 ≤ E}

/--
@isnad1 id=eq.0h3v.s5.926ab3217507 from=translated src=- shape=9b104724 vocab=e589e016
-/
theorem pointCl_toPointSet (E : ClosedIF k K) :
    pointCl (toPointSet E) = toPointSet E := by
  refine Set.eq_of_subset_of_subset (fun P hP ↦ ?_) (subset_pointCl _)
  rw [mem_pointCl_iff] at hP
  refine hP.trans (sSup_le ?_)
  rintro - ⟨Q, hQ, rfl⟩
  exact hQ

/-- Every closed intermediate field is the join of its points
(atomisticity, packaged for the equivalence).
@isnad1 id=eq.0h3v.s7.7177ce3e01a2 from=translated src=- shape=6c35e1d5 vocab=9fa8b062
-/
theorem sSup_toPointSet (E : ClosedIF k K) :
    sSup (Subtype.val '' toPointSet E) = E := by
  have : Subtype.val '' toPointSet E = {P : ClosedIF k K | IsAtom P ∧ P ≤ E} := by
    ext P
    constructor
    · rintro ⟨Q, hQ, rfl⟩
      exact ⟨Q.2, hQ⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨P, h1⟩, h2, rfl⟩
  rw [this, sSup_atoms_le_eq]

variable (k K) in
/-- The two presentations of the geometry agree: the closed lattice is order
isomorphic to the lattice of closed point sets
(blueprint §Point geometry and equivalence of presentations).-/
def pointSetIso : ClosedIF k K ≃o ClosedPointSet k K where
  toFun E := ⟨toPointSet E, pointCl_toPointSet E⟩
  invFun S := sSup (Subtype.val '' S.1)
  left_inv E := sSup_toPointSet E
  right_inv S := by
    refine Subtype.ext ?_
    change toPointSet (sSup (Subtype.val '' S.1)) = S.1
    exact S.2
  map_rel_iff' {E F} := by
    constructor
    · intro h
      have h' : toPointSet E ⊆ toPointSet F := h
      have h2 : sSup (Subtype.val '' toPointSet E) ≤
          sSup (Subtype.val '' toPointSet F) := sSup_le_sSup (Set.image_mono h')
      rwa [sSup_toPointSet, sSup_toPointSet] at h2
    · intro h P hP
      exact le_trans hP h

end ClosedIF

end PointSetIso

section TransportPoints

/-- Order isomorphisms carry atoms to atoms.
@isnad1 id=isatom.1h4v.s6.d3f61c52ee20 from=translated src=- shape=2a15ae10 vocab=0e032d2e
-/
theorem IsAtom.orderIso_map {α β : Type*} [PartialOrder α] [OrderBot α]
    [PartialOrder β] [OrderBot β] (e : α ≃o β) {a : α} (h : IsAtom a) :
    IsAtom (e a) := by
  constructor
  · intro h0
    exact h.1 (e.injective (by rw [h0, e.map_bot]))
  · intro b hb
    have hlt : e.symm b < a := by
      rw [← e.symm_apply_apply a]
      exact e.symm.strictMono hb
    have hbot := h.2 _ hlt
    calc b = e (e.symm b) := (e.apply_symm_apply b).symm
    _ = e ⊥ := by rw [hbot]
    _ = ⊥ := e.map_bot

/-- Order isomorphisms preserve atoms.
@isnad1 id=iff.0h4v.s6.f250f565d5ae from=translated src=- shape=fc72dc7f vocab=0e032d2e
-/
theorem isAtom_orderIso_iff {α β : Type*} [PartialOrder α] [OrderBot α]
    [PartialOrder β] [OrderBot β] (e : α ≃o β) {a : α} :
    IsAtom (e a) ↔ IsAtom a := by
  refine ⟨fun h ↦ ?_, fun h ↦ IsAtom.orderIso_map e h⟩
  have := IsAtom.orderIso_map e.symm h
  rwa [e.symm_apply_apply] at this

variable {l : Type*} {L : Type*} [Field l] [Field L] [Algebra l L]

/-- An order isomorphism of closed lattices restricts to a bijection of
points (blueprint eq. 20.3, first half).-/
def Point.map (e : ClosedIF k K ≃o ClosedIF l L) : Point k K ≃ Point l L where
  toFun P := ⟨e P.1, (isAtom_orderIso_iff e).2 P.2⟩
  invFun Q := ⟨e.symm Q.1, (isAtom_orderIso_iff e.symm).2 Q.2⟩
  left_inv P := Subtype.ext (e.symm_apply_apply P.1)
  right_inv Q := Subtype.ext (e.apply_symm_apply Q.1)

/--
@isnad1 id=eq.0h6v.s8.f5714f11be10 from=translated src=- shape=d11104f4 vocab=a68b4cec
-/
@[simp] theorem Point.map_coe (e : ClosedIF k K ≃o ClosedIF l L)
    (P : Point k K) : (Point.map e P).1 = e P.1 := rfl

/-- An order isomorphism of closed lattices preserves the point closure
(blueprint eq. 20.3): the restriction to points is a geometry equivalence.
@isnad1 id=iff.0h7v.s8.88f74f1437f5 from=translated src=- shape=511aeb08 vocab=29faaca8
-/
theorem pointCl_map_iff (e : ClosedIF k K ≃o ClosedIF l L)
    {S : Set (Point k K)} {P : Point k K} :
    Point.map e P ∈ pointCl (Point.map e '' S) ↔ P ∈ pointCl S := by
  have hsup : sSup (Subtype.val '' (Point.map e '' S))
      = e (sSup (Subtype.val '' S)) := by
    refine le_antisymm (sSup_le ?_) ?_
    · rintro - ⟨-, ⟨Q, hQ, rfl⟩, rfl⟩
      exact e.le_iff_le.2 (le_sSup ⟨Q, hQ, rfl⟩)
    · rw [e.map_sSup]
      refine iSup₂_le ?_
      rintro - ⟨Q, hQ, rfl⟩
      exact le_sSup ⟨Point.map e Q, ⟨Q, hQ, rfl⟩, rfl⟩
  constructor
  · intro h
    refine mem_pointCl_iff.2 (e.le_iff_le.1 ?_)
    calc e P.1 = (Point.map e P).1 := rfl
    _ ≤ sSup (Subtype.val '' (Point.map e '' S)) := mem_pointCl_iff.1 h
    _ = e (sSup (Subtype.val '' S)) := hsup
  · intro h
    refine mem_pointCl_iff.2 ?_
    calc (Point.map e P).1 = e P.1 := rfl
    _ ≤ e (sSup (Subtype.val '' S)) := e.le_iff_le.2 (mem_pointCl_iff.1 h)
    _ = sSup (Subtype.val '' (Point.map e '' S)) := hsup.symm

end TransportPoints

end

end AclGeom
