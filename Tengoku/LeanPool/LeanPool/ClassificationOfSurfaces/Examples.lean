/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
module

public import Tengoku.LeanPool.LeanPool.ClassificationOfSurfaces.CellComplexQuotient
public import Tengoku.LeanPool.LeanPool.ClassificationOfSurfaces.Representatives
public import Tengoku

/-!
# Standard combinatorial examples

This file names the small surfaces we should keep as regression tests while the definitions mature.
The examples are concrete one-face boundary-word presentations in the shared `SurfaceCellComplex`
API. Their topology is supplied by the faithful polygonal quotient layer.
-/

@[expose] public section

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces

/-- The normal form for the sphere. -/
def sphereNormalForm : NormalForm :=
  NormalForm.sphere

/-- The normal form for the disk: orientable genus zero with one boundary component. -/
def diskNormalForm : NormalForm :=
  NormalForm.orientable 0 1

/-- The normal form for the annulus: orientable genus zero with two boundary components. -/
def annulusNormalForm : NormalForm :=
  NormalForm.orientable 0 2

/-- The normal form for the torus: orientable genus one with no boundary. -/
def torusNormalForm : NormalForm :=
  NormalForm.orientable 1 0

/-- The normal form for the projective plane: one crosscap and no boundary. -/
def projectivePlaneNormalForm : NormalForm :=
  NormalForm.nonOrientable 1 0

/-- The normal form for the Mobius strip: one crosscap and one boundary component. -/
def mobiusStripNormalForm : NormalForm :=
  NormalForm.nonOrientable 1 1

/-- Edge names for the disk example. -/
inductive DiskEdge where
  | h
deriving DecidableEq, Repr

instance : Fintype DiskEdge :=
  Fintype.ofList [.h] (by intro edge; cases edge; simp)

/-- Edge names for the annulus example. -/
inductive AnnulusEdge where
  | d₀
  | c₀
  | d₁
  | c₁
deriving DecidableEq, Repr

instance : Fintype AnnulusEdge :=
  Fintype.ofList [.d₀, .c₀, .d₁, .c₁] (by
    intro edge
    cases edge <;> simp)

/-- Edge names for the torus example. -/
inductive TorusEdge where
  | a
  | b
deriving DecidableEq, Repr

instance : Fintype TorusEdge :=
  Fintype.ofList [.a, .b] (by intro edge; cases edge <;> simp)

/-- Edge names for the projective-plane example. -/
inductive ProjectivePlaneEdge where
  | a
deriving DecidableEq, Repr

instance : Fintype ProjectivePlaneEdge :=
  Fintype.ofList [.a] (by intro edge; cases edge; simp)

/-- Edge names for the Mobius-strip example. -/
inductive MobiusStripEdge where
  | a
  | h
deriving DecidableEq, Repr

instance : Fintype MobiusStripEdge :=
  Fintype.ofList [.a, .h] (by intro edge; cases edge <;> simp)

open SurfaceCellComplex.SignedDart

/-- One-face boundary-word presentation for the disk. -/
def diskCellComplex : SurfaceCellComplex :=
  SurfaceCellComplex.oneFacePresentation DiskEdge [pos DiskEdge.h]

/-- One-face boundary-word presentation for the annulus: `d₀ c₀ d₀⁻¹ d₁ c₁ d₁⁻¹`.

The `dᵢ` pairs are internal seams and the single occurrences `cᵢ` are the two boundary
contours. This is a renaming of the genus-zero, two-contour normal form from Gallier--Xu
Definition 6.5. -/
def annulusCellComplex : SurfaceCellComplex :=
  SurfaceCellComplex.oneFacePresentation AnnulusEdge
    [pos AnnulusEdge.d₀, pos AnnulusEdge.c₀, neg AnnulusEdge.d₀,
      pos AnnulusEdge.d₁, pos AnnulusEdge.c₁, neg AnnulusEdge.d₁]

/-- One-face boundary-word presentation for the torus: `a b a⁻¹ b⁻¹`. -/
def torusCellComplex : SurfaceCellComplex :=
  SurfaceCellComplex.oneFacePresentation TorusEdge
    [pos TorusEdge.a, pos TorusEdge.b, neg TorusEdge.a, neg TorusEdge.b]

/-- One-face boundary-word presentation for the projective plane: `a a`. -/
def projectivePlaneCellComplex : SurfaceCellComplex :=
  SurfaceCellComplex.oneFacePresentation ProjectivePlaneEdge
    [pos ProjectivePlaneEdge.a, pos ProjectivePlaneEdge.a]

/-- One-face boundary-word presentation for the Mobius strip: `a a h`. -/
def mobiusStripCellComplex : SurfaceCellComplex :=
  SurfaceCellComplex.oneFacePresentation MobiusStripEdge
    [pos MobiusStripEdge.a, pos MobiusStripEdge.a, pos MobiusStripEdge.h]

/-- The annulus has the full length-six, two-contour boundary word. -/
theorem annulusCellComplex_boundary :
    annulusCellComplex.boundary PUnit.unit =
      [pos AnnulusEdge.d₀, pos AnnulusEdge.c₀, neg AnnulusEdge.d₀,
        pos AnnulusEdge.d₁, pos AnnulusEdge.c₁, neg AnnulusEdge.d₁] := by
  rfl

/-- Regression check: edge-orbit multiplicity accepts the non-orientable word `a a`. -/
theorem projectivePlaneCellComplex_isSurfaceValid :
    projectivePlaneCellComplex.IsSurfaceValid := by
  apply SurfaceCellComplex.oneFacePresentation_isSurfaceValid
  intro e
  cases e
  decide

/-! ## Occurrence-pairing validity -/

/-- The disk word has one boundary occurrence and no internal pairings. -/
theorem diskCellComplex_occurrencePairingValid :
    diskCellComplex.OccurrencePairingValid := by
  apply SurfaceCellComplex.oneFacePresentation_occurrencePairingValid
  · decide
  · intro e
    cases e
    decide

/-- The corrected annulus word has two internal seam pairs and two boundary occurrences. -/
theorem annulusCellComplex_occurrencePairingValid :
    annulusCellComplex.OccurrencePairingValid := by
  apply SurfaceCellComplex.oneFacePresentation_occurrencePairingValid
  · decide
  · intro e
    cases e <;> decide

/-- The torus word pairs both of its edge names internally. -/
theorem torusCellComplex_occurrencePairingValid :
    torusCellComplex.OccurrencePairingValid := by
  apply SurfaceCellComplex.oneFacePresentation_occurrencePairingValid
  · decide
  · intro e
    cases e <;> decide

/-- The two copies of the projective-plane edge form one internal pair. -/
theorem projectivePlaneCellComplex_occurrencePairingValid :
    projectivePlaneCellComplex.OccurrencePairingValid := by
  apply SurfaceCellComplex.oneFacePresentation_occurrencePairingValid
  · decide
  · intro e
    cases e
    decide

/-- The Mobius-strip word has one internal pair and one boundary occurrence. -/
theorem mobiusStripCellComplex_occurrencePairingValid :
    mobiusStripCellComplex.OccurrencePairingValid := by
  apply SurfaceCellComplex.oneFacePresentation_occurrencePairingValid
  · decide
  · intro e
    cases e <;> decide

/-- Incidence validity of the disk presentation. -/
theorem diskCellComplex_isSurfaceValid : diskCellComplex.IsSurfaceValid :=
  diskCellComplex_occurrencePairingValid.surface_valid

/-- Incidence validity of the corrected annulus presentation. -/
theorem annulusCellComplex_isSurfaceValid : annulusCellComplex.IsSurfaceValid :=
  annulusCellComplex_occurrencePairingValid.surface_valid

/-- Incidence validity of the torus presentation. -/
theorem torusCellComplex_isSurfaceValid : torusCellComplex.IsSurfaceValid :=
  torusCellComplex_occurrencePairingValid.surface_valid

/-- Incidence validity of the Mobius-strip presentation. -/
theorem mobiusStripCellComplex_isSurfaceValid : mobiusStripCellComplex.IsSurfaceValid :=
  mobiusStripCellComplex_occurrencePairingValid.surface_valid

/-- A minimal one-triangle triangulation of `PUnit`, used only to test the data conversion API. -/
def oneTriangleTriangulation : FiniteSurfaceTriangulation PUnit where
  Vertex := Fin 3
  Edge := Fin 3
  Triangle := PUnit
  vertexFintype := inferInstance
  vertexDecidableEq := inferInstance
  edgeFintype := inferInstance
  triangleFintype := inferInstance
  realization := PUnit
  realizationTop := inferInstance
  edgeVertices := fun
    | 0 => {0, 1}
    | 1 => {1, 2}
    | 2 => {2, 0}
  triangleVertices := fun _ => Finset.univ
  edgeSource := fun e => e
  edgeTarget := fun e => ⟨(e.1 + 1) % 3, Nat.mod_lt _ (by decide)⟩
  triangleBoundary := fun _ =>
    [OrientedEdge.pos 0, OrientedEdge.pos 1, OrientedEdge.pos 2]
  edgeIsBoundary := fun _ => True
  isSurfaceTriangulation :=
    { edge_card := by
        intro e
        fin_cases e <;>
        decide
      triangle_card := by
        intro t
        cases t
        decide
      edgeSource_mem := by
        intro e
        fin_cases e <;>
        decide
      edgeTarget_mem := by
        intro e
        fin_cases e <;>
        decide
      edgeSource_ne_edgeTarget := by
        intro e
        fin_cases e <;>
        decide
      boundary_edge_vertices_subset := by
        intro t oe hoe
        exact Finset.subset_univ _ }
  homeomorphSurface := ⟨Homeomorph.refl PUnit⟩

/-- A one-triangle fixture with one reversed side, used to test oriented conversion. -/
def reversedSideTriangulation : FiniteSurfaceTriangulation PUnit where
  Vertex := Fin 3
  Edge := Fin 3
  Triangle := PUnit
  vertexFintype := inferInstance
  vertexDecidableEq := inferInstance
  edgeFintype := inferInstance
  triangleFintype := inferInstance
  realization := PUnit
  realizationTop := inferInstance
  edgeVertices := fun
    | 0 => {0, 1}
    | 1 => {1, 2}
    | 2 => {2, 0}
  triangleVertices := fun _ => Finset.univ
  edgeSource := fun e => e
  edgeTarget := fun e => ⟨(e.1 + 1) % 3, Nat.mod_lt _ (by decide)⟩
  triangleBoundary := fun _ =>
    [OrientedEdge.pos 0, OrientedEdge.pos 1, OrientedEdge.neg 2]
  edgeIsBoundary := fun _ => True
  isSurfaceTriangulation :=
    { edge_card := by
        intro e
        fin_cases e <;>
        decide
      triangle_card := by
        intro t
        cases t
        decide
      edgeSource_mem := by
        intro e
        fin_cases e <;>
        decide
      edgeTarget_mem := by
        intro e
        fin_cases e <;>
        decide
      edgeSource_ne_edgeTarget := by
        intro e
        fin_cases e <;>
        decide
      boundary_edge_vertices_subset := by
        intro t oe hoe
        exact Finset.subset_univ _ }
  homeomorphSurface := ⟨Homeomorph.refl PUnit⟩

end ClassificationOfSurfaces
end Topology
end LeanEval
