/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
module

public import Tengoku.LeanPool.LeanPool.ClassificationOfSurfaces.FiniteCyclicPresentation
public import Tengoku.LeanPool.LeanPool.ClassificationOfSurfaces.PolygonalQuotient
public import Tengoku

/-!
# Polygonal realization of finite cyclic presentations

This file gives `FiniteCyclicPresentation` a quotient-space semantics directly from its stored
face words. A boundary occurrence is a face together with an index in that face's word, so
repeated signed darts remain distinct polygon sides.

The pre-realization is the disjoint union of the standard polygonal disks indexed by the
presentation's faces. Internal sides are paired exactly when their signed darts have the same
underlying edge; equal signs use the same interval parameter and opposite signs use the reversed
parameter.

`FiniteCyclicPresentation.IsSurfaceValid` already includes nonempty face boundaries, unlike the
legacy cell-complex predicate. It therefore supplies the complete occurrence-pairing certificate
needed by this construction.
-/

@[expose] public section

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace FiniteCyclicPresentation

open scoped BigOperators
open SurfaceCellComplex

/-- A position in one of the stored cyclic face words. -/
abbrev BoundaryOccurrence (P : FiniteCyclicPresentation) :=
  Σ f : P.Face, Fin (P.boundary f).length

instance boundaryOccurrenceFintype (P : FiniteCyclicPresentation) :
    Fintype P.BoundaryOccurrence :=
  inferInstance

namespace BoundaryOccurrence

/-- The signed dart stored at a boundary occurrence. -/
def dart {P : FiniteCyclicPresentation} (o : P.BoundaryOccurrence) : P.Dart :=
  (P.boundary o.1).get o.2

/-- The unoriented edge stored at a boundary occurrence. -/
def edge {P : FiniteCyclicPresentation} (o : P.BoundaryOccurrence) : P.Edge :=
  edgeOfDart o.dart

/--
@isnad1 id=eq.0h3v.s5.7b284faa936c from=translated src=- shape=780b47fa vocab=a4af150d
-/
@[simp]
theorem dart_mk (P : FiniteCyclicPresentation) (f : P.Face)
    (i : Fin (P.boundary f).length) :
    (show P.BoundaryOccurrence from ⟨f, i⟩).dart = (P.boundary f).get i :=
  rfl

/--
@isnad1 id=eq.0h3v.s5.ccf329461bc1 from=translated src=- shape=c42c6452 vocab=3a7533a1
-/
@[simp]
theorem edge_mk (P : FiniteCyclicPresentation) (f : P.Face)
    (i : Fin (P.boundary f).length) :
    (show P.BoundaryOccurrence from ⟨f, i⟩).edge =
      edgeOfDart ((P.boundary f).get i) :=
  rfl

end BoundaryOccurrence

/-- The polygon side indexed by a boundary occurrence. -/
def occurrenceSide (P : FiniteCyclicPresentation) (o : P.BoundaryOccurrence) :
    PolygonGluing.Side P.Face fun f => (P.boundary f).length :=
  ⟨o.1, o.2⟩

/--
@isnad1 id=eq.0h2v.s5.13c8c58b661e from=translated src=- shape=951e22d4 vocab=829c9525
-/
@[simp]
theorem occurrenceSide_face (P : FiniteCyclicPresentation) (o : P.BoundaryOccurrence) :
    (P.occurrenceSide o).face = o.1 :=
  rfl

/--
@isnad1 id=eq.0h2v.s5.09cae24fab74 from=translated src=- shape=4af7c034 vocab=84188b7a
-/
@[simp]
theorem occurrenceSide_index (P : FiniteCyclicPresentation) (o : P.BoundaryOccurrence) :
    (P.occurrenceSide o).index = o.2 :=
  rfl

/-- All boundary occurrences carrying the unoriented edge `e`. -/
noncomputable def edgeOccurrences (P : FiniteCyclicPresentation) (e : P.Edge) :
    Finset P.BoundaryOccurrence := by
  classical
  exact Finset.univ.filter fun o => o.edge = e

/--
@isnad1 id=iff.0h3v.s5.6044a31d60d2 from=translated src=- shape=47613944 vocab=df98d394
-/
@[simp]
theorem mem_edgeOccurrences (P : FiniteCyclicPresentation) (e : P.Edge)
    (o : P.BoundaryOccurrence) :
    o ∈ P.edgeOccurrences e ↔ o.edge = e := by
  classical
  simp [edgeOccurrences]

private noncomputable def boundaryIndexCount
    (P : FiniteCyclicPresentation) (f : P.Face) (e : P.Edge) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Fin (P.boundary f).length)).filter
    fun i => edgeOfDart ((P.boundary f).get i) = e).card

private theorem boundaryIndexCount_eq_faceEdgeMultiplicity
    (P : FiniteCyclicPresentation) (f : P.Face) (e : P.Edge) :
    P.boundaryIndexCount f e = P.faceEdgeMultiplicity f e := by
  classical
  unfold boundaryIndexCount faceEdgeMultiplicity
  let v : List.Vector P.Edge (P.boundary f).length :=
    List.Vector.ofFn fun i => edgeOfDart ((P.boundary f).get i)
  simpa [v, List.ofFn_comp'] using
    Fin.card_filter_univ_eq_vector_get_eq_count e v

/-- Total edge multiplicity is exactly the cardinality of the corresponding occurrence fiber.
@isnad1 id=eq.0h2v.s4.0c0c7391c0e7 from=translated src=- shape=ddbadb94 vocab=0e2fc7a0
-/
theorem edgeMultiplicity_eq_card_edgeOccurrences
    (P : FiniteCyclicPresentation) (e : P.Edge) :
    P.edgeMultiplicity e = (P.edgeOccurrences e).card := by
  classical
  let allOccurrences : Finset P.BoundaryOccurrence :=
    (Finset.univ : Finset P.Face).sigma fun f =>
      (Finset.univ : Finset (Fin (P.boundary f).length))
  have hall : allOccurrences = Finset.univ := by
    ext o
    simp [allOccurrences]
  calc
    P.edgeMultiplicity e =
        ∑ f : P.Face, P.boundaryIndexCount f e := by
      unfold edgeMultiplicity
      apply Finset.sum_congr rfl
      intro f _hf
      exact (P.boundaryIndexCount_eq_faceEdgeMultiplicity f e).symm
    _ = (allOccurrences.filter fun o => o.edge = e).card := by
      unfold boundaryIndexCount
      rw [show allOccurrences =
          (Finset.univ : Finset P.Face).sigma fun f =>
            (Finset.univ : Finset (Fin (P.boundary f).length)) by
        rfl]
      rw [← Finset.card_sigma]
      congr 1
      ext o
      simp only [List.get_eq_getElem, Finset.mem_sigma, Finset.mem_univ,
        Finset.mem_filter, true_and, Finset.univ_sigma_univ]
      change
        FiniteCyclicPresentation.edgeOfDart ((P.boundary o.1).get o.2) = e ↔
          FiniteCyclicPresentation.edgeOfDart ((P.boundary o.1).get o.2) = e
      rfl
    _ = (P.edgeOccurrences e).card := by
      rw [hall]
      rfl

/--
@isnad1 id=eq.0h2v.s4.2a50c753e80f from=translated src=- shape=454dc2d6 vocab=0e2fc7a0
-/
@[simp]
theorem card_edgeOccurrences (P : FiniteCyclicPresentation) (e : P.Edge) :
    (P.edgeOccurrences e).card = P.edgeMultiplicity e :=
  (P.edgeMultiplicity_eq_card_edgeOccurrences e).symm

/-- Two distinct occurrences of the same edge certify that the edge is internal.
@isnad1 id=not.2h3v.s4.bd456542e7bf from=translated src=- shape=f51b14ba vocab=d7d42b4a
-/
theorem not_isBoundaryEdge_of_ne_of_edge_eq
    {P : FiniteCyclicPresentation} {o p : P.BoundaryOccurrence}
    (hop : o ≠ p) (hedge : p.edge = o.edge) :
    ¬P.IsBoundaryEdge o.edge := by
  intro hboundary
  have ho : o ∈ P.edgeOccurrences o.edge :=
    (P.mem_edgeOccurrences o.edge o).mpr rfl
  have hp : p ∈ P.edgeOccurrences o.edge :=
    (P.mem_edgeOccurrences o.edge p).mpr hedge
  have hcard : 1 < (P.edgeOccurrences o.edge).card :=
    Finset.one_lt_card.mpr ⟨o, ho, p, hp, hop⟩
  rw [P.card_edgeOccurrences, hboundary] at hcard
  omega

private theorem dart_eq_or_eq_flip_iff_edge_eq
    {P : FiniteCyclicPresentation} (x d : P.Dart) :
    x = d ∨ x = d.flip ↔ edgeOfDart x = edgeOfDart d := by
  cases x <;> cases d <;> simp [edgeOfDart, SignedDart.flip]

/-- A compatible gluing instruction between two distinct internal boundary occurrences. -/
structure BoundaryPairing (P : FiniteCyclicPresentation) where
  /-- The `source` declaration. -/
  source : P.BoundaryOccurrence
  /-- The `target` declaration. -/
  target : P.BoundaryOccurrence
  source_ne_target : source ≠ target
  source_not_boundary : ¬P.IsBoundaryEdge source.edge
  target_not_boundary : ¬P.IsBoundaryEdge target.edge
  /-- The `direction` declaration. -/
  direction : PolygonGluing.ParameterDirection
  compatible :
    match direction with
    | .same => target.dart = source.dart
    | .opposite => target.dart = source.dart.flip

namespace IsSurfaceValid

/-- A non-boundary edge of a valid presentation occurs exactly twice.
@isnad1 id=eq.2h2v.s4.67de2b62ebf4 from=translated src=- shape=849814cb vocab=f666de74
-/
theorem edgeMultiplicity_eq_two_of_not_boundary
    {P : FiniteCyclicPresentation} (h : P.IsSurfaceValid) {e : P.Edge}
    (he : ¬P.IsBoundaryEdge e) :
    P.edgeMultiplicity e = 2 := by
  rcases h.2.2.2 e with hone | htwo
  · exact False.elim (he hone)
  · exact htwo

/-- Every internal occurrence has a unique distinct partner carrying the same unoriented edge.
@isnad1 id=existsun.2h2v.s5.4af215f418c3 from=translated src=- shape=9dc2d50a vocab=622015dc
-/
theorem exists_unique_partner
    {P : FiniteCyclicPresentation} (h : P.IsSurfaceValid)
    (source : P.BoundaryOccurrence)
    (hsource : ¬P.IsBoundaryEdge source.edge) :
    ∃! target : P.BoundaryOccurrence,
      source ≠ target ∧ target.edge = source.edge := by
  have hcard : (P.edgeOccurrences source.edge).card = 2 := by
    rw [P.card_edgeOccurrences]
    exact h.edgeMultiplicity_eq_two_of_not_boundary hsource
  obtain ⟨o₁, o₂, hne, hindices⟩ := Finset.card_eq_two.mp hcard
  have hcover (o : P.BoundaryOccurrence) (ho : o.edge = source.edge) :
      o = o₁ ∨ o = o₂ := by
    have hmem : o ∈ P.edgeOccurrences source.edge :=
      (P.mem_edgeOccurrences source.edge o).mpr ho
    simpa [hindices] using hmem
  have ho₁ : o₁.edge = source.edge := by
    apply (P.mem_edgeOccurrences source.edge o₁).mp
    simp [hindices]
  have ho₂ : o₂.edge = source.edge := by
    apply (P.mem_edgeOccurrences source.edge o₂).mp
    simp [hindices]
  rcases hcover source rfl with hsource₁ | hsource₂
  · refine ⟨o₂, ⟨hsource₁.trans_ne hne, ho₂⟩, ?_⟩
    intro target htarget
    rcases hcover target htarget.2 with htarget₁ | htarget₂
    · exact False.elim (htarget.1 (hsource₁.trans htarget₁.symm))
    · exact htarget₂
  · refine ⟨o₁, ⟨hsource₂.trans_ne hne.symm, ho₁⟩, ?_⟩
    intro target htarget
    rcases hcover target htarget.2 with htarget₁ | htarget₂
    · exact htarget₁
    · exact False.elim (htarget.1 (hsource₂.trans htarget₂.symm))

/-- Every internal boundary occurrence is the source of a compatible polygon-side pairing.
@isnad1 id=ex.2h2v.s4.e94a1bb9370d from=translated src=- shape=ee158e70 vocab=a8164078
-/
theorem exists_pairing_source
    {P : FiniteCyclicPresentation} (h : P.IsSurfaceValid)
    (source : P.BoundaryOccurrence)
    (hsource : ¬P.IsBoundaryEdge source.edge) :
    ∃ pairing : P.BoundaryPairing, pairing.source = source := by
  obtain ⟨target, ⟨hne, hedge⟩, _hunique⟩ :=
    h.exists_unique_partner source hsource
  have htarget : ¬P.IsBoundaryEdge target.edge := by
    rw [hedge]
    exact hsource
  rcases (dart_eq_or_eq_flip_iff_edge_eq target.dart source.dart).mpr hedge with
    hsame | hopposite
  · exact ⟨⟨source, target, hne, hsource, htarget, .same, hsame⟩, rfl⟩
  · exact ⟨⟨source, target, hne, hsource, htarget, .opposite, hopposite⟩, rfl⟩

end IsSurfaceValid

namespace BoundaryPairing

/-- The polygon-side identification associated to a compatible occurrence pairing. -/
def identification {P : FiniteCyclicPresentation} (pairing : P.BoundaryPairing) :
    PolygonGluing.Identification P.Face fun f => (P.boundary f).length where
  source := P.occurrenceSide pairing.source
  target := P.occurrenceSide pairing.target
  direction := pairing.direction

/--
@isnad1 id=eq.0h2v.s5.c2bb8dd01fda from=translated src=- shape=31098650 vocab=8615fb9b
-/
@[simp]
theorem identification_source {P : FiniteCyclicPresentation} (pairing : P.BoundaryPairing) :
    pairing.identification.source = P.occurrenceSide pairing.source :=
  rfl

/--
@isnad1 id=eq.0h2v.s5.8cbad4ceaede from=translated src=- shape=31098650 vocab=4698996b
-/
@[simp]
theorem identification_target {P : FiniteCyclicPresentation} (pairing : P.BoundaryPairing) :
    pairing.identification.target = P.occurrenceSide pairing.target :=
  rfl

/--
@isnad1 id=eq.0h2v.s4.2c2d8fa144b9 from=translated src=- shape=dbcdd684 vocab=c0a38fb4
-/
@[simp]
theorem identification_direction {P : FiniteCyclicPresentation} (pairing : P.BoundaryPairing) :
    pairing.identification.direction = pairing.direction :=
  rfl

end BoundaryPairing

/-- All polygon-side identifications compatible with a valid finite cyclic presentation. -/
def polygonalIdentifications
    (P : FiniteCyclicPresentation) (_valid : P.IsSurfaceValid) :
    Set (PolygonGluing.Identification P.Face fun f => (P.boundary f).length) :=
  Set.range BoundaryPairing.identification

/--
@isnad1 id=mem.1h2v.s5.f3de223dbb66 from=translated src=- shape=5c64688c vocab=33ec6bdc
-/
@[simp]
theorem pairing_identification_mem
    {P : FiniteCyclicPresentation} (valid : P.IsSurfaceValid)
    (pairing : P.BoundaryPairing) :
    pairing.identification ∈ P.polygonalIdentifications valid :=
  ⟨pairing, rfl⟩

/-- Every internal occurrence of a valid presentation starts a prescribed identification.
@isnad1 id=ex.2h2v.s6.aabcba1c21ac from=translated src=- shape=29dd2871 vocab=11dab442
-/
theorem IsSurfaceValid.exists_identification_source
    {P : FiniteCyclicPresentation} (h : P.IsSurfaceValid)
    (source : P.BoundaryOccurrence)
    (hsource : ¬P.IsBoundaryEdge source.edge) :
    ∃ identification ∈ P.polygonalIdentifications h,
      identification.source = P.occurrenceSide source := by
  obtain ⟨pairing, hp⟩ := h.exists_pairing_source source hsource
  refine ⟨pairing.identification, pairing_identification_mem h pairing, ?_⟩
  rw [BoundaryPairing.identification_source, hp]

/-- The disjoint union of the polygonal cells encoded by the stored face words. -/
abbrev PolygonalPreRealization (P : FiniteCyclicPresentation) : Type :=
  PolygonGluing.PreRealization P.Face fun f => (P.boundary f).length

/-- The generated relation from all compatible internal occurrence pairings. -/
abbrev PolygonalGluingRel
    (P : FiniteCyclicPresentation) (valid : P.IsSurfaceValid) :
    Setoid P.PolygonalPreRealization :=
  PolygonGluing.setoid (P.polygonalIdentifications valid)

/-- The polygonal quotient realized directly from a valid finite cyclic presentation. -/
abbrev PolygonalRealization
    (P : FiniteCyclicPresentation) (valid : P.IsSurfaceValid) : Type :=
  PolygonGluing.Realization (P.polygonalIdentifications valid)

/-- The quotient map from the disjoint union of face polygons. -/
def polygonalMk
    (P : FiniteCyclicPresentation) (valid : P.IsSurfaceValid) :
    P.PolygonalPreRealization → P.PolygonalRealization valid :=
  PolygonGluing.mk (P.polygonalIdentifications valid)

/--
@isnad1 id=continuo.1h1v.s6.dfb3c2a70635 from=translated src=- shape=8927bd27 vocab=0f3894df
-/
theorem continuous_polygonalMk
    (P : FiniteCyclicPresentation) (valid : P.IsSurfaceValid) :
    Continuous (P.polygonalMk valid) :=
  PolygonGluing.continuous_mk (P.polygonalIdentifications valid)

/--
@isnad1 id=isquotie.1h1v.s6.edbf970ee3c4 from=translated src=- shape=8927bd27 vocab=c4d3c8a2
-/
theorem isQuotientMap_polygonalMk
    (P : FiniteCyclicPresentation) (valid : P.IsSurfaceValid) :
    _root_.Topology.IsQuotientMap (P.polygonalMk valid) :=
  PolygonGluing.isQuotientMap_mk (P.polygonalIdentifications valid)

/-- Every compatible pairing identifies the corresponding side points in the quotient.
@isnad1 id=eq.1h3v.s7.54a9bf59def4 from=translated src=- shape=78b1f95b vocab=cf666fb9
-/
theorem polygonalMk_pairing_eq
    {P : FiniteCyclicPresentation} (valid : P.IsSurfaceValid)
    (pairing : P.BoundaryPairing) (t : unitInterval) :
    P.polygonalMk valid (pairing.identification.source.point t) =
      P.polygonalMk valid
        (pairing.identification.target.point (pairing.identification.parameter t)) :=
  PolygonGluing.mk_source_eq_mk_target pairing.identification
    (pairing_identification_mem valid pairing) t

/-- Cut-and-paste data sufficient to compare two polygonal realizations.

The maps start on the two polygonal pre-realizations but land in the opposite quotient. This
asymmetric-looking formulation is deliberate: after a polygon is cut into two faces, the reverse
map need not lift continuously to the disjoint union of those faces, although it can be continuous
as a map to their glued quotient. -/
structure RealizationEquivData
    (P Q : FiniteCyclicPresentation) (validP : P.IsSurfaceValid)
    (validQ : Q.IsSurfaceValid) where
  /-- The `toPre` declaration. -/
  toPre : P.PolygonalPreRealization → Q.PolygonalRealization validQ
  /-- The `invPre` declaration. -/
  invPre : Q.PolygonalPreRealization → P.PolygonalRealization validP
  continuous_toPre : Continuous toPre
  continuous_invPre : Continuous invPre
  to_respects :
    ∀ x y, P.PolygonalGluingRel validP x y → toPre x = toPre y
  inv_respects :
    ∀ x y, Q.PolygonalGluingRel validQ x y → invPre x = invPre y
  left_inverse_mk :
    ∀ x, Quotient.lift invPre inv_respects (toPre x) = P.polygonalMk validP x
  right_inverse_mk :
    ∀ y, Quotient.lift toPre to_respects (invPre y) = Q.polygonalMk validQ y

namespace RealizationEquivData

/-- Descend the forward cut-and-paste map through the source gluing relation. -/
def toQuotient
    {P Q : FiniteCyclicPresentation} {validP : P.IsSurfaceValid}
    {validQ : Q.IsSurfaceValid} (data : RealizationEquivData P Q validP validQ) :
    P.PolygonalRealization validP → Q.PolygonalRealization validQ :=
  Quotient.lift data.toPre data.to_respects

/-- Descend the reverse cut-and-paste map through the target gluing relation. -/
def invQuotient
    {P Q : FiniteCyclicPresentation} {validP : P.IsSurfaceValid}
    {validQ : Q.IsSurfaceValid} (data : RealizationEquivData P Q validP validQ) :
    Q.PolygonalRealization validQ → P.PolygonalRealization validP :=
  Quotient.lift data.invPre data.inv_respects

/--
@isnad1 id=eq.2h4v.s5.3972c5428ddc from=translated src=- shape=935c5322 vocab=28868c63
-/
@[simp]
theorem toQuotient_polygonalMk
    {P Q : FiniteCyclicPresentation} {validP : P.IsSurfaceValid}
    {validQ : Q.IsSurfaceValid} (data : RealizationEquivData P Q validP validQ)
    (x : P.PolygonalPreRealization) :
    data.toQuotient (P.polygonalMk validP x) = data.toPre x :=
  rfl

/--
@isnad1 id=eq.2h4v.s5.3ec1430b39c8 from=translated src=- shape=34e884c0 vocab=a0d0fdd1
-/
@[simp]
theorem invQuotient_polygonalMk
    {P Q : FiniteCyclicPresentation} {validP : P.IsSurfaceValid}
    {validQ : Q.IsSurfaceValid} (data : RealizationEquivData P Q validP validQ)
    (y : Q.PolygonalPreRealization) :
    data.invQuotient (Q.polygonalMk validQ y) = data.invPre y :=
  rfl

/--
@isnad1 id=continuo.2h3v.s7.902bffaac0aa from=translated src=- shape=50834365 vocab=6bbcfa07
-/
theorem continuous_toQuotient
    {P Q : FiniteCyclicPresentation} {validP : P.IsSurfaceValid}
    {validQ : Q.IsSurfaceValid} (data : RealizationEquivData P Q validP validQ) :
    Continuous data.toQuotient :=
  data.continuous_toPre.quotient_lift data.to_respects

/--
@isnad1 id=continuo.2h3v.s7.834a6eef2d44 from=translated src=- shape=9d6f4d07 vocab=4a1bf747
-/
theorem continuous_invQuotient
    {P Q : FiniteCyclicPresentation} {validP : P.IsSurfaceValid}
    {validQ : Q.IsSurfaceValid} (data : RealizationEquivData P Q validP validQ) :
    Continuous data.invQuotient :=
  data.continuous_invPre.quotient_lift data.inv_respects

/-- Cut-and-paste data descend to a homeomorphism of the generated polygonal quotients. -/
noncomputable def homeomorph
    {P Q : FiniteCyclicPresentation} {validP : P.IsSurfaceValid}
    {validQ : Q.IsSurfaceValid} (data : RealizationEquivData P Q validP validQ) :
    P.PolygonalRealization validP ≃ₜ Q.PolygonalRealization validQ where
  toFun := data.toQuotient
  invFun := data.invQuotient
  left_inv := by
    intro q
    induction q using Quotient.inductionOn'
    exact data.left_inverse_mk _
  right_inv := by
    intro q
    induction q using Quotient.inductionOn'
    exact data.right_inverse_mk _
  continuous_toFun := data.continuous_toQuotient
  continuous_invFun := data.continuous_invQuotient

end RealizationEquivData

/-- Quotient semantics for comparing two valid finite cyclic presentations. -/
def PolygonallyEquivalent
    (P Q : FiniteCyclicPresentation) (validP : P.IsSurfaceValid)
    (validQ : Q.IsSurfaceValid) : Prop :=
  Nonempty (P.PolygonalRealization validP ≃ₜ Q.PolygonalRealization validQ)

/-- A cut-and-paste certificate proves polygonal equivalence.
@isnad1 id=polygona.2h3v.s4.01279259cad5 from=translated src=- shape=9b3950b6 vocab=c26e2298
-/
theorem RealizationEquivData.polygonallyEquivalent
    {P Q : FiniteCyclicPresentation} {validP : P.IsSurfaceValid}
    {validQ : Q.IsSurfaceValid} (data : RealizationEquivData P Q validP validQ) :
    PolygonallyEquivalent P Q validP validQ :=
  ⟨data.homeomorph⟩

end FiniteCyclicPresentation
end ClassificationOfSurfaces
end Topology
end LeanEval
