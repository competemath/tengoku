/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
module

public import Tengoku.LeanPool.LeanPool.ClassificationOfSurfaces.CellComplex
public import Tengoku

/-!
# Countermodels and semantic anchors

This file is the executable half of the Definition Faithfulness rules in
`docs/AUTOFORMALIZATION_GUIDE.md`.  It must stay in the default build target: if a definition is
weakened until junk witnesses satisfy it, something in this file stops compiling (or a negation
in this file becomes provable *and* its positive counterpart does too, which the trivial-closure
review catches).

Contents:

* positive anchor: the standard 2-simplex carries a geometric triangulation with one face;
* must-imply anchors are proved at the definition site
  (`GeometricTriangulation.compactSpace`, `GeometricTriangulation.t2Space`,
  `GeometricTriangulation.faces_nonempty`);
* non-examples: `ℝ` and `ℚ` admit no geometric triangulation;
* vacuity probes: empty face families and one-point vertex types cannot triangulate a nonempty
  space;
* an executable witness showing why an arbitrary finite triangulation record is not itself a
  certified cell presentation;
* cell-complex non-examples: an unused dart orbit and disconnected face systems;
* a record of the vacuity failure of the retiring `SurfaceTriangulable` predicate, kept as
  documentation of why `GeometricTriangulation` replaces it.
-/

@[expose] public section

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Countermodels

/-! ## Positive anchor -/

/-- The one-face complex on three vertices realizes exactly the standard 2-simplex.
@isnad1 id=eq.0h0v.s6.235a5d454f66 from=translated src=- shape=c8985a58 vocab=71cbdc93
-/
theorem geometricRealization_single_face :
    GeometricRealization (Fin 3) {Finset.univ} = stdSimplex ℝ (Fin 3) := by
  ext x
  simp [GeometricRealization]

/-- The standard 2-simplex carries a geometric triangulation with a single face. -/
noncomputable def stdSimplexTriangulation :
    GeometricTriangulation (stdSimplex ℝ (Fin 3)) where
  Vertex := Fin 3
  faces := {Finset.univ}
  faces_card := by
    intro t ht
    rw [Finset.mem_singleton] at ht
    subst ht
    simp
  homeo := Homeomorph.setCongr geometricRealization_single_face

/-! ## Vacuity probes for geometric triangulations -/

/-! ## Non-examples

A faithful notion of finite triangulation must fail for non-compact spaces.  The previous
`SurfaceTriangulable` predicate passed both of these with the empty triangulation. -/

/-! ## Legacy bridge countermodel

`FiniteSurfaceTriangulation` still has an arbitrary stored realization.  This fixture satisfies
its current validity record for every universe-0 topological space using `Homeomorph.refl`, while
its two face words are empty.  Consequently its cell presentation is neither incidence-valid nor
face-edge connected.  The faithful Radó theorem does not use this object as its conclusion; it
enters only through the explicitly ledgered compatibility bridge. -/

/-- Every universe-0 topological space inhabits the legacy triangulation structure. -/
noncomputable def arbitrarySpaceLegacyTriangulation
    (S : Type) [TopologicalSpace S] : FiniteSurfaceTriangulation S where
  Vertex := Fin 3
  Edge := PUnit
  Triangle := Bool
  vertexFintype := inferInstance
  vertexDecidableEq := inferInstance
  edgeFintype := inferInstance
  triangleFintype := inferInstance
  realization := S
  realizationTop := inferInstance
  edgeVertices := fun _ => {0, 1}
  triangleVertices := fun _ => Finset.univ
  edgeSource := fun _ => 0
  edgeTarget := fun _ => 1
  triangleBoundary := fun _ => []
  edgeIsBoundary := fun _ => True
  isSurfaceTriangulation := by
    constructor
    · intro e
      simp
    · intro t
      simp
    · intro e
      simp
    · intro e
      simp
    · intro e
      norm_num
    · intro t oe hoe
      simp at hoe
  homeomorphSurface := ⟨Homeomorph.refl S⟩

/-- The arbitrary stored realization makes the legacy topological field hold by reflexivity.
@isnad1 id=nonempty.0h1v.s4.e76548e52168 from=translated src=- shape=eab656d5 vocab=d0da7710
-/
theorem arbitrarySpaceLegacyTriangulation_homeomorphSurface
    (S : Type) [TopologicalSpace S] :
    Nonempty ((arbitrarySpaceLegacyTriangulation S).realization ≃ₜ S) :=
  (arbitrarySpaceLegacyTriangulation S).homeomorphSurface

/-- Empty boundary words leave the stored edge orbit unused, so the converted presentation is
not incidence-valid.
@isnad1 id=not.0h1v.s3.232444234663 from=translated src=- shape=71465b91 vocab=5869f188
-/
theorem arbitrarySpaceLegacyTriangulation_not_isSurfaceValid
    (S : Type) [TopologicalSpace S] :
    ¬ (arbitrarySpaceLegacyTriangulation S).toCellComplex.IsSurfaceValid := by
  rintro ⟨_, _, _, hedges⟩
  rcases hedges (SurfaceCellComplex.SignedDart.pos PUnit.unit) with hone | htwo
  · rcases hone with ⟨⟨f, i⟩, _⟩
    change Fin 0 at i
    exact Fin.elim0 i
  · rcases htwo with ⟨⟨f, i⟩, _⟩
    change Fin 0 at i
    exact Fin.elim0 i

/-- The two empty face words have no adjacency path, so the converted presentation is not
face-edge connected.
@isnad1 id=not.0h1v.s3.e6d83a8a2754 from=translated src=- shape=71465b91 vocab=37d7ce50
-/
theorem arbitrarySpaceLegacyTriangulation_not_isConnected
    (S : Type) [TopologicalSpace S] :
    ¬ (arbitrarySpaceLegacyTriangulation S).toCellComplex.IsConnected := by
  rintro ⟨_, hconnected⟩
  have adjacent_false : ∀ f g,
      (arbitrarySpaceLegacyTriangulation S).toCellComplex.FaceAdjacent f g → False := by
    intro f g h
    rcases h with ⟨d, hd, e, he, _⟩
    change d ∈ [] at hd
    simp at hd
  have reach_eq : ∀ {f g},
      Relation.ReflTransGen
        (arbitrarySpaceLegacyTriangulation S).toCellComplex.FaceAdjacent f g → f = g := by
    intro f g h
    induction h with
    | refl => rfl
    | tail _ hstep _ => exact (adjacent_false _ _ hstep).elim
  exact Bool.false_ne_true (reach_eq (hconnected false true))

/-! ## Cell-complex incidence countermodels -/

open SurfaceCellComplex.SignedDart

/-- A one-face presentation with an edge orbit omitted from every boundary word. -/
def unusedDartOrbit : SurfaceCellComplex :=
  SurfaceCellComplex.oneFacePresentation PUnit []

/-- Incidence validity rejects an edge orbit with zero boundary occurrences.
@isnad1 id=not.0h0v.s1.adf63c33fcd2 from=translated src=- shape=87ceb31f vocab=98dab935
-/
theorem unusedDartOrbit_not_isSurfaceValid :
    ¬ unusedDartOrbit.IsSurfaceValid := by
  rintro ⟨_, _, _, hedges⟩
  rcases hedges (pos PUnit.unit) with hone | htwo
  · rcases hone with ⟨⟨f, i⟩, _⟩
    cases f
    exact Fin.elim0 i
  · rcases htwo with ⟨⟨f, i⟩, _⟩
    cases f
    exact Fin.elim0 i

/-- Two otherwise plausible one-edge faces sharing only a stored vertex, but no edge orbit. -/
def disconnectedBoundaryFaces : SurfaceCellComplex where
  Face := Bool
  Dart := SurfaceCellComplex.SignedDart Bool
  Vertex := PUnit
  faceFintype := inferInstance
  dartFintype := inferInstance
  vertexFintype := inferInstance
  inv := SurfaceCellComplex.SignedDart.flipEquiv Bool
  source := fun _ => PUnit.unit
  target := fun _ => PUnit.unit
  boundary := fun f => [pos f]
  inv_involutive := SurfaceCellComplex.SignedDart.flip_flip
  inv_source := by intro d; rfl
  inv_target := by intro d; rfl

/-- The disconnected fixture is locally valid: each of its two edge orbits occurs exactly once.
@isnad1 id=issurfac.0h0v.s1.94e731831bd0 from=translated src=- shape=49959d42 vocab=b396128e
-/
theorem disconnectedBoundaryFaces_isSurfaceValid :
    disconnectedBoundaryFaces.IsSurfaceValid := by
  refine ⟨⟨false⟩, ?_, ?_, ?_⟩
  · intro f g h
    change [pos f] ~r [pos g] at h
    have hmem : pos f ∈ [pos g] := h.mem_iff.mp (by simp)
    exact SurfaceCellComplex.SignedDart.pos.inj (List.mem_singleton.mp hmem)
  · intro d
    cases d with
    | pos b =>
        change neg b ≠ pos b
        intro h
        cases h
    | neg b =>
        change pos b ≠ neg b
        intro h
        cases h
  · intro d
    left
    cases d with
    | pos b =>
        let o : disconnectedBoundaryFaces.BoundaryOccurrence :=
          ⟨b, ⟨0, by simp [disconnectedBoundaryFaces]⟩⟩
        refine ⟨o, Or.inl rfl, ?_⟩
        rintro ⟨f, i⟩ hi
        change Fin 1 at i
        fin_cases i
        have hfb : f = b := by
          have hi' : pos f = pos b ∨
              pos f = disconnectedBoundaryFaces.inv (pos b) := by
            simpa [SurfaceCellComplex.Occurs, SurfaceCellComplex.SameEdge,
              SurfaceCellComplex.BoundaryOccurrence.dart, disconnectedBoundaryFaces] using hi
          rcases hi' with hi' | hi'
          · exact SurfaceCellComplex.SignedDart.pos.inj hi'
          · change pos f = neg b at hi'
            cases hi'
        cases hfb
        rfl
    | neg b =>
        let o : disconnectedBoundaryFaces.BoundaryOccurrence :=
          ⟨b, ⟨0, by simp [disconnectedBoundaryFaces]⟩⟩
        refine ⟨o, Or.inr rfl, ?_⟩
        rintro ⟨f, i⟩ hi
        change Fin 1 at i
        fin_cases i
        have hfb : f = b := by
          have hi' : pos f = disconnectedBoundaryFaces.inv (neg b) := by
            simpa [SurfaceCellComplex.Occurs, SurfaceCellComplex.SameEdge,
              SurfaceCellComplex.BoundaryOccurrence.dart, disconnectedBoundaryFaces] using hi
          change pos f = pos b at hi'
          exact SurfaceCellComplex.SignedDart.pos.inj hi'
        cases hfb
        rfl

/-- Face-edge connectedness rejects two face systems even when the stored vertex type is a point.
@isnad1 id=not.0h0v.s1.c59f5d5c7089 from=translated src=- shape=87ceb31f vocab=bae2c55c
-/
theorem disconnectedBoundaryFaces_not_isConnected :
    ¬ disconnectedBoundaryFaces.IsConnected := by
  rintro ⟨_, hconnected⟩
  have adjacent_eq :
      ∀ f g, disconnectedBoundaryFaces.FaceAdjacent f g → f = g := by
    intro f g h
    rcases h with ⟨d, hd, e, he, hsame⟩
    have hd' : d = pos f := List.mem_singleton.mp hd
    have he' : e = pos g := List.mem_singleton.mp he
    subst d
    subst e
    rcases hsame with hsame | hsame
    · exact (SurfaceCellComplex.SignedDart.pos.inj hsame).symm
    · change pos g = neg f at hsame
      cases hsame
  have reach_eq : ∀ {f g},
      Relation.ReflTransGen disconnectedBoundaryFaces.FaceAdjacent f g → f = g := by
    intro f g h
    induction h with
    | refl => rfl
    | tail _hfg hgh ih => exact ih.trans (adjacent_eq _ _ hgh)
  exact Bool.false_ne_true (reach_eq (hconnected false true))

/-! ## Vacuity record

The legacy predicate `SurfaceTriangulable` was satisfied by **every** topological space via the
empty triangulation, because its `realization` field was arbitrary and unlinked to the
combinatorial data.  The predicate and the machine-checked vacuity proof were deleted together
(per the Definition Faithfulness rules); the proof is preserved in git history on the commit that
introduced this file.  If you find yourself able to write such a proof for
`GeometricTriangulation`, the definition has been broken. -/

end Countermodels
end ClassificationOfSurfaces
end Topology
end LeanEval
