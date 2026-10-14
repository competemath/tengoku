/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
module

public import Tengoku.LeanPool.LeanPool.ClassificationOfSurfaces.SignedPresentation
public import Tengoku

/-!
# Finite cyclic surface presentations

This file packages the purely combinatorial data used by polygon-word moves. Edge names and faces
are finite by construction, and a face boundary is a cyclic list of signed edge names. Unlike
`SurfaceCellComplex`, this presentation has no arbitrary vertex labels or placeholder realization.

`PresentationIso` records orientation-preserving changes of names: an equivalence of edge names,
an equivalence of faces, and a rotation witness for every renamed face boundary. Allowing an
independent orientation reversal for each edge is a separate extension needed before the most
general polygon-word moves.
`EdgeRelabeling` records an equivalence of edge names together with an independent orientation
reversal for each source edge. `SignedPresentationIso` combines such a relabeling with an
equivalence of faces and a rotation witness for every renamed face boundary. The original
orientation-preserving `PresentationIso` remains available as a compatible special case.

`OrientedFace` gives each stored face a positive and negative traversal view without mutating the
presentation. The negative boundary word is the reversed list with every dart orientation
flipped, as required by the oriented polygon conventions used in Gallier--Xu moves.

Gallier--Xu Definition 6.1 has one exceptional cell complex: one face, no edges, and the empty
boundary word. The ordinary `IsSurfaceValid` predicate continues to require nonempty face
boundaries. At the end of the file, `IsEmptyWordSphere` recognizes the exceptional signed
isomorphism class and `IsGallierValid` adds it as an explicit disjunct. The presentation
`twoMonogonSphere` is the nonexceptional two-face model obtained by the book's P2 refinement.
-/

@[expose] public section

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces

open scoped BigOperators

/-- A finite list of cyclic signed boundary words with edge names in `Fin edgeCount`. -/
structure FiniteCyclicPresentation where
  /-- The `edgeCount` declaration. -/
  edgeCount : ℕ
  /-- The `faces` declaration. -/
  faces : List (List (SurfaceCellComplex.SignedDart (Fin edgeCount)))

namespace FiniteCyclicPresentation

open SurfaceCellComplex

/-- The finite type of unoriented edge names. -/
abbrev Edge (P : FiniteCyclicPresentation) :=
  Fin P.edgeCount

/-- Signed occurrences of unoriented edge names. -/
abbrev Dart (P : FiniteCyclicPresentation) :=
  SignedDart P.Edge

/-- Faces are positions in the stored list of boundary words. -/
abbrev Face (P : FiniteCyclicPresentation) :=
  Fin P.faces.length

/-- The stored cyclic boundary word of a face. -/
def boundary (P : FiniteCyclicPresentation) (f : P.Face) : List P.Dart :=
  P.faces.get f

/-- Forget the orientation of a signed edge occurrence. -/
def edgeOfDart {α : Type*} : SignedDart α → α
  | .pos e => e
  | .neg e => e

/--
@isnad1 id=eq.0h2v.s3.b3c80f69f50c from=translated src=- shape=4f3f71b4 vocab=9ef2d3c9
-/
@[simp]
theorem edgeOfDart_flip {α : Type*} (d : SignedDart α) :
    edgeOfDart d.flip = edgeOfDart d := by
  cases d <;> rfl

/-- Reverse the traversal direction of a signed boundary word. -/
def inverseWord {α : Type*} (word : List (SignedDart α)) :
    List (SignedDart α) :=
  word.reverse.map SignedDart.flip

/--
@isnad1 id=eq.0h1v.s3.c532f66bace1 from=translated src=- shape=96bd7b29 vocab=74a76fad
-/
theorem inverseWord_nil {α : Type*} :
    inverseWord ([] : List (SignedDart α)) = [] :=
  rfl

/--
@isnad1 id=eq.0h2v.s4.f06cfbfea6e9 from=translated src=- shape=ebdf4a29 vocab=352a8877
-/
@[simp]
theorem inverseWord_length {α : Type*} (word : List (SignedDart α)) :
    (inverseWord word).length = word.length := by
  simp [inverseWord]

/--
@isnad1 id=eq.0h2v.s4.7fd69154c400 from=translated src=- shape=9bcc0c0c vocab=509f8de0
-/
@[simp]
theorem inverseWord_inverseWord {α : Type*} (word : List (SignedDart α)) :
    inverseWord (inverseWord word) = word := by
  simp [inverseWord, List.map_map, Function.comp_def]

/-- Reversing signed words is an involution.
@isnad1 id=involuti.0h1v.s3.d44afe45e62d from=translated src=- shape=34fcea4e vocab=2e02d69f
-/
theorem inverseWord_involutive {α : Type*} :
    Function.Involutive (@inverseWord α) :=
  inverseWord_inverseWord

/--
@isnad1 id=eq.0h3v.s5.a7f82d510bdd from=translated src=- shape=3b802d51 vocab=6490dfb1
-/
@[simp]
theorem inverseWord_append {α : Type*}
    (left right : List (SignedDart α)) :
    inverseWord (left ++ right) = inverseWord right ++ inverseWord left := by
  simp [inverseWord]

/-- Reversing traversal direction preserves cyclic equivalence.
@isnad1 id=isrotate.1h3v.s4.8aeb332d2dc3 from=translated src=- shape=374e5335 vocab=34621d4e
-/
theorem inverseWord_isRotated {α : Type*}
    {left right : List (SignedDart α)} (h : left.IsRotated right) :
    (inverseWord left).IsRotated (inverseWord right) := by
  exact h.reverse.map SignedDart.flip

/--
@isnad1 id=iff.0h3v.s4.1ba85f034368 from=translated src=- shape=64c2271c vocab=34621d4e
-/
@[simp]
theorem inverseWord_isRotated_iff {α : Type*}
    (left right : List (SignedDart α)) :
    (inverseWord left).IsRotated (inverseWord right) ↔
      left.IsRotated right := by
  constructor
  · intro h
    simpa only [inverseWord_inverseWord] using inverseWord_isRotated h
  · exact inverseWord_isRotated

/--
@isnad1 id=eq.0h2v.s4.744d4d36a420 from=translated src=- shape=c2333dc8 vocab=b25f1475
-/
@[simp]
theorem map_edgeOfDart_inverseWord {α : Type*}
    (word : List (SignedDart α)) :
    (inverseWord word).map edgeOfDart = (word.map edgeOfDart).reverse := by
  simp [inverseWord, List.map_map, Function.comp_def]

/-- A relabeling of unoriented edges with an independent orientation reversal for each source
edge. -/
structure EdgeRelabeling (α β : Type*) where
  /-- The `edgeEquiv` declaration. -/
  edgeEquiv : α ≃ β
  /-- The `reverse` declaration. -/
  reverse : α → Bool

namespace EdgeRelabeling

/-- Apply an edge relabeling to a signed dart. -/
def mapDart {α β : Type*} (e : EdgeRelabeling α β) : SignedDart α → SignedDart β
  | .pos a =>
      if e.reverse a then
        .neg (e.edgeEquiv a)
      else
        .pos (e.edgeEquiv a)
  | .neg a =>
      if e.reverse a then
        .pos (e.edgeEquiv a)
      else
        .neg (e.edgeEquiv a)

/-- The identity signed-edge relabeling. -/
def refl (α : Type*) : EdgeRelabeling α α where
  edgeEquiv := Equiv.refl α
  reverse := fun _ ↦ false

/-- Reverse a signed-edge relabeling. -/
def symm {α β : Type*} (e : EdgeRelabeling α β) : EdgeRelabeling β α where
  edgeEquiv := e.edgeEquiv.symm
  reverse := fun b ↦ e.reverse (e.edgeEquiv.symm b)

/-- Compose signed-edge relabelings. Reversing twice cancels, so the reversal bits compose by
exclusive-or. -/
def trans {α β γ : Type*}
    (e : EdgeRelabeling α β) (f : EdgeRelabeling β γ) : EdgeRelabeling α γ where
  edgeEquiv := e.edgeEquiv.trans f.edgeEquiv
  reverse := fun a ↦ Bool.xor (e.reverse a) (f.reverse (e.edgeEquiv a))

/-- An ordinary edge equivalence, viewed as a relabeling that preserves every chosen
orientation. -/
def ofEquiv {α β : Type*} (e : α ≃ β) : EdgeRelabeling α β where
  edgeEquiv := e
  reverse := fun _ ↦ false

/--
@isnad1 id=eq.0h2v.s3.6db49ba8d190 from=translated src=- shape=c22bccd1 vocab=6786f816
-/
@[simp]
theorem mapDart_refl {α : Type*} (d : SignedDart α) :
    (refl α).mapDart d = d := by
  cases d <;> rfl

/--
@isnad1 id=eq.0h4v.s4.3e7f45d6ed75 from=translated src=- shape=2ce9bb00 vocab=3d4a8449
-/
@[simp]
theorem mapDart_symm_apply {α β : Type*} (e : EdgeRelabeling α β)
    (d : SignedDart α) :
    e.symm.mapDart (e.mapDart d) = d := by
  cases d with
  | pos a =>
      cases h : e.reverse a <;>
        simp [mapDart, symm, h]
  | neg a =>
      cases h : e.reverse a <;>
        simp [mapDart, symm, h]

/--
@isnad1 id=eq.0h4v.s4.ba510624be2e from=translated src=- shape=66ebb760 vocab=3d4a8449
-/
@[simp]
theorem mapDart_apply_symm {α β : Type*} (e : EdgeRelabeling α β)
    (d : SignedDart β) :
    e.mapDart (e.symm.mapDart d) = d := by
  cases d with
  | pos b =>
      cases h : e.reverse (e.edgeEquiv.symm b) <;>
        simp [mapDart, symm, h]
  | neg b =>
      cases h : e.reverse (e.edgeEquiv.symm b) <;>
        simp [mapDart, symm, h]

/-- A signed-edge relabeling is an equivalence on darts. -/
def dartEquiv {α β : Type*} (e : EdgeRelabeling α β) :
    SignedDart α ≃ SignedDart β where
  toFun := e.mapDart
  invFun := e.symm.mapDart
  left_inv := e.mapDart_symm_apply
  right_inv := e.mapDart_apply_symm

/--
@isnad1 id=eq.0h4v.s5.624fb29594ec from=translated src=- shape=2d1adaf0 vocab=cf5f692f
-/
@[simp]
theorem dartEquiv_apply {α β : Type*} (e : EdgeRelabeling α β) (d : SignedDart α) :
    e.dartEquiv d = e.mapDart d :=
  rfl

/--
@isnad1 id=eq.0h4v.s5.7f0a85ef2edc from=translated src=- shape=3165c5dd vocab=c41c3acf
-/
@[simp]
theorem edgeOfDart_mapDart {α β : Type*} (e : EdgeRelabeling α β)
    (d : SignedDart α) :
    edgeOfDart (e.mapDart d) = e.edgeEquiv (edgeOfDart d) := by
  cases d with
  | pos a =>
      cases h : e.reverse a <;>
        simp [mapDart, h, edgeOfDart]
  | neg a =>
      cases h : e.reverse a <;>
        simp [mapDart, h, edgeOfDart]

/--
@isnad1 id=eq.0h4v.s6.22e4481c5990 from=translated src=- shape=f190f8c8 vocab=42f28909
-/
theorem edgeOfDart_dartEquiv {α β : Type*} (e : EdgeRelabeling α β)
    (d : SignedDart α) :
    edgeOfDart (e.dartEquiv d) = e.edgeEquiv (edgeOfDart d) :=
  e.edgeOfDart_mapDart d

/--
@isnad1 id=eq.0h4v.s4.300439dc9edf from=translated src=- shape=1e195b52 vocab=ffe708a2
-/
@[simp]
theorem mapDart_flip {α β : Type*} (e : EdgeRelabeling α β)
    (d : SignedDart α) :
    e.mapDart d.flip = (e.mapDart d).flip := by
  cases d with
  | pos a =>
      cases h : e.reverse a <;>
        simp [mapDart, SignedDart.flip, h]
  | neg a =>
      cases h : e.reverse a <;>
        simp [mapDart, SignedDart.flip, h]

/--
@isnad1 id=eq.0h4v.s6.3c99c4fbcaf7 from=translated src=- shape=09fda735 vocab=c0a9963c
-/
theorem dartEquiv_flip {α β : Type*} (e : EdgeRelabeling α β)
    (d : SignedDart α) :
    e.dartEquiv d.flip = (e.dartEquiv d).flip :=
  e.mapDart_flip d

/--
@isnad1 id=eq.0h6v.s5.be2233d4bdb4 from=translated src=- shape=e70b94e5 vocab=171e0039
-/
@[simp]
theorem mapDart_trans {α β γ : Type*}
    (e : EdgeRelabeling α β) (f : EdgeRelabeling β γ) (d : SignedDart α) :
    (e.trans f).mapDart d = f.mapDart (e.mapDart d) := by
  cases d with
  | pos a =>
      cases h₁ : e.reverse a <;>
        cases h₂ : f.reverse (e.edgeEquiv a) <;>
          simp [mapDart, trans, h₁, h₂]
  | neg a =>
      cases h₁ : e.reverse a <;>
        cases h₂ : f.reverse (e.edgeEquiv a) <;>
          simp [mapDart, trans, h₁, h₂]

/--
@isnad1 id=eq.0h4v.s5.495db53ffac2 from=translated src=- shape=32ffbd18 vocab=f85a1495
-/
@[simp]
theorem mapDart_ofEquiv {α β : Type*} (e : α ≃ β) (d : SignedDart α) :
    (ofEquiv e).mapDart d = SignedDart.mapEquiv e d := by
  cases d <;> rfl

/--
@isnad1 id=eq.0h4v.s6.f69345643172 from=translated src=- shape=a01afb48 vocab=111f96f3
-/
@[simp]
theorem map_mapDart_ofEquiv {α β : Type*} (e : α ≃ β) (l : List (SignedDart α)) :
    l.map (ofEquiv e).mapDart = l.map (SignedDart.mapEquiv e) := by
  induction l with
  | nil => rfl
  | cons d l ih =>
      simp only [List.map_cons, mapDart_ofEquiv, ih]

/--
@isnad1 id=eq.0h2v.s4.b65d837a9cbb from=translated src=- shape=7214de11 vocab=6cee29be
-/
theorem map_mapDart_refl {α : Type*} (l : List (SignedDart α)) :
    l.map (refl α).mapDart = l := by
  induction l with
  | nil => rfl
  | cons d l ih =>
      simp only [List.map_cons, mapDart_refl, ih]

/--
@isnad1 id=eq.0h4v.s5.b8db1e34d8b9 from=translated src=- shape=d3b68ab2 vocab=96ea0336
-/
theorem map_mapDart_symm {α β : Type*}
    (e : EdgeRelabeling α β) (l : List (SignedDart α)) :
    (l.map e.mapDart).map e.symm.mapDart = l := by
  induction l with
  | nil => rfl
  | cons d l ih =>
      simp only [List.map_cons, mapDart_symm_apply, ih]

/--
@isnad1 id=eq.0h6v.s5.3655f00d698c from=translated src=- shape=fd1d48c7 vocab=3d8abd02
-/
theorem map_mapDart_trans {α β γ : Type*}
    (e : EdgeRelabeling α β) (f : EdgeRelabeling β γ) (l : List (SignedDart α)) :
    l.map (e.trans f).mapDart = (l.map e.mapDart).map f.mapDart := by
  induction l with
  | nil => rfl
  | cons d l ih =>
      simp only [List.map_cons, mapDart_trans, ih]

/--
@isnad1 id=eq.0h4v.s5.0733594a8519 from=translated src=- shape=af8dba02 vocab=e189b8df
-/
@[simp]
theorem inverseWord_map_mapDart {α β : Type*}
    (e : EdgeRelabeling α β) (word : List (SignedDart α)) :
    inverseWord (word.map e.mapDart) =
      (inverseWord word).map e.mapDart := by
  simp [inverseWord, List.map_map, Function.comp_def]

end EdgeRelabeling

/--
@isnad1 id=eq.0h4v.s6.b7ba81800bbd from=translated src=- shape=9ceff121 vocab=1bd7465f
-/
@[simp]
theorem edgeOfDart_mapEquiv {α β : Type*} (e : α ≃ β) (d : SignedDart α) :
    edgeOfDart (SignedDart.mapEquiv e d) = e (edgeOfDart d) := by
  cases d <;> rfl

/--
@isnad1 id=eq.0h2v.s5.6f450a115fd7 from=translated src=- shape=595dda3f vocab=43e96ff6
-/
@[simp]
theorem mapEquiv_refl {α : Type*} (d : SignedDart α) :
    SignedDart.mapEquiv (Equiv.refl α) d = d := by
  cases d <;> rfl

/--
@isnad1 id=eq.0h6v.s6.825edc5fa03e from=translated src=- shape=1d551abf vocab=dc464923
-/
@[simp]
theorem mapEquiv_trans {α β γ : Type*} (e : α ≃ β) (f : β ≃ γ)
    (d : SignedDart α) :
    SignedDart.mapEquiv (e.trans f) d =
      SignedDart.mapEquiv f (SignedDart.mapEquiv e d) := by
  cases d <;> rfl

/--
@isnad1 id=eq.0h4v.s6.5e43b986b2dd from=translated src=- shape=987b0ab3 vocab=98ecce37
-/
@[simp]
theorem mapEquiv_symm_apply {α β : Type*} (e : α ≃ β) (d : SignedDart α) :
    SignedDart.mapEquiv e.symm (SignedDart.mapEquiv e d) = d := by
  cases d <;> simp [SignedDart.mapEquiv]

/--
@isnad1 id=eq.0h2v.s5.0baeb45c9775 from=translated src=- shape=706f2230 vocab=3361ea49
-/
theorem map_mapEquiv_refl {α : Type*} (l : List (SignedDart α)) :
    l.map (SignedDart.mapEquiv (Equiv.refl α)) = l := by
  induction l with
  | nil => rfl
  | cons d l ih =>
      simp only [List.map_cons, mapEquiv_refl, ih]

/--
@isnad1 id=eq.0h4v.s6.3411137b4c65 from=translated src=- shape=608e65d8 vocab=e50ffa1a
-/
theorem map_mapEquiv_symm {α β : Type*} (e : α ≃ β) (l : List (SignedDart α)) :
    (l.map (SignedDart.mapEquiv e)).map (SignedDart.mapEquiv e.symm) = l := by
  induction l with
  | nil => rfl
  | cons d l ih =>
      simp only [List.map_cons, mapEquiv_symm_apply, ih]

/--
@isnad1 id=eq.0h6v.s7.9bd0cef0df78 from=translated src=- shape=5eee3855 vocab=f01b71d8
-/
theorem map_mapEquiv_trans {α β γ : Type*} (e : α ≃ β) (f : β ≃ γ)
    (l : List (SignedDart α)) :
    l.map (SignedDart.mapEquiv (e.trans f)) =
      (l.map (SignedDart.mapEquiv e)).map (SignedDart.mapEquiv f) := by
  induction l with
  | nil => rfl
  | cons d l ih =>
      simp only [List.map_cons, mapEquiv_trans, ih]

/--
@isnad1 id=eq.0h4v.s6.bd8350587359 from=translated src=- shape=fdc16f0a vocab=6acb0873
-/
@[simp]
theorem inverseWord_map_mapEquiv {α β : Type*}
    (e : α ≃ β) (word : List (SignedDart α)) :
    inverseWord (word.map (SignedDart.mapEquiv e)) =
      (inverseWord word).map (SignedDart.mapEquiv e) := by
  simp [inverseWord, List.map_map, Function.comp_def]

/-- A face together with one of its two traversal orientations. `false` selects the stored
orientation and `true` selects its reverse. -/
structure OrientedFace (P : FiniteCyclicPresentation) where
  /-- The `face` declaration. -/
  face : P.Face
  /-- The `orientation` declaration. -/
  orientation : Bool
deriving DecidableEq, Fintype

namespace OrientedFace

/-- A face with its stored traversal orientation. -/
def pos {P : FiniteCyclicPresentation} (f : P.Face) : P.OrientedFace :=
  ⟨f, false⟩

/-- A face with the traversal orientation opposite to the stored one. -/
def neg {P : FiniteCyclicPresentation} (f : P.Face) : P.OrientedFace :=
  ⟨f, true⟩

/-- Reverse the traversal orientation of a face. -/
def flip {P : FiniteCyclicPresentation} (f : P.OrientedFace) :
    P.OrientedFace :=
  ⟨f.face, !f.orientation⟩

/--
@isnad1 id=eq.0h2v.s3.5a5412a488b3 from=translated src=- shape=6ddf6d3e vocab=9c5865ec
-/
@[simp]
theorem pos_face {P : FiniteCyclicPresentation} (f : P.Face) :
    (pos f).face = f :=
  rfl

/--
@isnad1 id=eq.0h2v.s3.336eac3b4129 from=translated src=- shape=6ddf6d3e vocab=ff26c532
-/
@[simp]
theorem neg_face {P : FiniteCyclicPresentation} (f : P.Face) :
    (neg f).face = f :=
  rfl

/--
@isnad1 id=eq.0h2v.s4.790f57406901 from=translated src=- shape=dc061f59 vocab=553e9193
-/
@[simp]
theorem flip_face {P : FiniteCyclicPresentation} (f : P.OrientedFace) :
    f.flip.face = f.face :=
  rfl

/--
@isnad1 id=eq.0h2v.s4.9e1fa68361a9 from=translated src=- shape=d6576abc vocab=335939aa
-/
@[simp]
theorem flip_pos {P : FiniteCyclicPresentation} (f : P.Face) :
    (pos f).flip = neg f :=
  rfl

/--
@isnad1 id=eq.0h2v.s4.db8afac94956 from=translated src=- shape=d6576abc vocab=335939aa
-/
@[simp]
theorem flip_neg {P : FiniteCyclicPresentation} (f : P.Face) :
    (neg f).flip = pos f :=
  rfl

/--
@isnad1 id=eq.0h2v.s3.61552651c94f from=translated src=- shape=6ddf6d3e vocab=755118ef
-/
@[simp]
theorem flip_flip {P : FiniteCyclicPresentation} (f : P.OrientedFace) :
    f.flip.flip = f := by
  cases f with
  | mk face orientation =>
      cases orientation <;> rfl

end OrientedFace

/-- The boundary of an oriented face, read in its chosen traversal direction. -/
abbrev orientedBoundary (P : FiniteCyclicPresentation)
    (f : P.OrientedFace) : List P.Dart :=
  if f.orientation then inverseWord (P.boundary f.face) else P.boundary f.face

/--
@isnad1 id=eq.0h2v.s4.b8a085eea208 from=translated src=- shape=d8898af0 vocab=c59f9736
-/
@[simp]
theorem orientedBoundary_pos (P : FiniteCyclicPresentation) (f : P.Face) :
    P.orientedBoundary (.pos f) = P.boundary f :=
  rfl

/--
@isnad1 id=eq.0h2v.s4.93a7deda2732 from=translated src=- shape=8c23ae6b vocab=7347feef
-/
@[simp]
theorem orientedBoundary_neg (P : FiniteCyclicPresentation) (f : P.Face) :
    P.orientedBoundary (.neg f) = inverseWord (P.boundary f) :=
  rfl

/--
@isnad1 id=eq.0h2v.s4.e69adb8a2a94 from=translated src=- shape=ca4025ca vocab=9aa048e9
-/
@[simp]
theorem orientedBoundary_flip (P : FiniteCyclicPresentation)
    (f : P.OrientedFace) :
    P.orientedBoundary f.flip = inverseWord (P.orientedBoundary f) := by
  cases f with
  | mk face orientation =>
      cases orientation <;> simp [OrientedFace.flip, orientedBoundary]

/--
@isnad1 id=eq.0h2v.s4.84e45ae3b4f6 from=translated src=- shape=799b09d3 vocab=d62576ac
-/
@[simp]
theorem orientedBoundary_length (P : FiniteCyclicPresentation)
    (f : P.OrientedFace) :
    (P.orientedBoundary f).length = (P.boundary f.face).length := by
  cases f with
  | mk face orientation =>
      cases orientation <;> simp [orientedBoundary]

/-- Multiplicity of an edge in one face boundary. -/
def faceEdgeMultiplicity (P : FiniteCyclicPresentation) (f : P.Face) (e : P.Edge) : ℕ :=
  ((P.boundary f).map edgeOfDart).count e

/-- Reading a face boundary in the opposite direction does not change edge multiplicities.
@isnad1 id=eq.0h3v.s5.fbdf7c2c765c from=translated src=- shape=bdb8e18b vocab=eea8cb5e
-/
theorem orientedBoundary_edgeMultiplicity (P : FiniteCyclicPresentation)
    (f : P.OrientedFace) (e : P.Edge) :
    ((P.orientedBoundary f).map edgeOfDart).count e =
      P.faceEdgeMultiplicity f.face e := by
  cases f with
  | mk face orientation =>
      cases orientation
      · rfl
      · unfold faceEdgeMultiplicity
        rw [orientedBoundary, ite_eq_left rfl, map_edgeOfDart_inverseWord]
        exact (List.reverse_perm _).count_eq e

/-- Total number of boundary occurrences of an unoriented edge. -/
def edgeMultiplicity (P : FiniteCyclicPresentation) (e : P.Edge) : ℕ :=
  ∑ f : P.Face, P.faceEdgeMultiplicity f e

/-- An edge is a boundary edge when it occurs in exactly one face boundary position. -/
def IsBoundaryEdge (P : FiniteCyclicPresentation) (e : P.Edge) : Prop :=
  P.edgeMultiplicity e = 1

/-- Incidence validity for a finite cyclic presentation.

There is at least one face, every face has a nonempty boundary, different faces have different
cyclic boundary words, and every edge occurs either once or twice. -/
def IsSurfaceValid (P : FiniteCyclicPresentation) : Prop :=
  Nonempty P.Face ∧
    (∀ f, P.boundary f ≠ []) ∧
    (∀ f g, (P.boundary f).IsRotated (P.boundary g) → f = g) ∧
    ∀ e, P.edgeMultiplicity e = 1 ∨ P.edgeMultiplicity e = 2

/-- Two faces are adjacent when their boundary words contain a common unoriented edge. -/
def FaceAdjacent (P : FiniteCyclicPresentation) (f g : P.Face) : Prop :=
  ∃ e : P.Edge,
    e ∈ (P.boundary f).map edgeOfDart ∧ e ∈ (P.boundary g).map edgeOfDart

/-- Connectivity of the face-edge incidence graph. -/
def IsConnected (P : FiniteCyclicPresentation) : Prop :=
  Nonempty P.Face ∧ ∀ f g, Relation.ReflTransGen P.FaceAdjacent f g

/-- The exceptional Gallier--Xu presentation with one face, no edges, and an empty boundary.

Definition 6.1 explicitly allows this case. Its geometric realization is assigned to the sphere
on page 86. -/
@[reducible]
def emptyWordSphere : FiniteCyclicPresentation where
  edgeCount := 0
  faces := [[]]

/-- The two-monogon presentation with boundaries `d` and `d⁻¹`.

Gallier--Xu page 86 obtains this presentation from `emptyWordSphere` by the P2 face split. Unlike
the exceptional presentation, it satisfies the ordinary nonempty-boundary validity predicate. -/
@[reducible]
def twoMonogonSphere : FiniteCyclicPresentation where
  edgeCount := 1
  faces := [[.pos 0], [.neg 0]]

/--
@isnad1 id=eq.0h1v.s3.d22b742e8162 from=translated src=- shape=708ab39f vocab=047f67ef
-/
theorem emptyWordSphere_boundary (f : emptyWordSphere.Face) :
    emptyWordSphere.boundary f = [] := by
  simp [boundary, emptyWordSphere]

/-- The exceptional empty-word presentation is connected because it has exactly one face.
@isnad1 id=isconnec.0h0v.s1.73f836251cbc from=translated src=- shape=49959d42 vocab=c8605af3
-/
theorem emptyWordSphere_isConnected :
    emptyWordSphere.IsConnected := by
  refine ⟨⟨0, by simp [emptyWordSphere]⟩, ?_⟩
  intro f g
  fin_cases f
  fin_cases g
  exact Relation.ReflTransGen.refl

/-- The exceptional presentation is deliberately excluded from ordinary validity.
@isnad1 id=not.0h0v.s1.ca1c6db7000d from=translated src=- shape=87ceb31f vocab=cb82d358
-/
theorem emptyWordSphere_not_isSurfaceValid :
    ¬ emptyWordSphere.IsSurfaceValid := by
  intro h
  let f : emptyWordSphere.Face := ⟨0, by simp [emptyWordSphere]⟩
  exact h.2.1 f (emptyWordSphere_boundary f)

/--
@isnad1 id=eq.0h0v.s5.3830e8312d43 from=translated src=- shape=c6a81320 vocab=763340f4
-/
@[simp]
theorem twoMonogonSphere_boundary_zero :
    twoMonogonSphere.boundary 0 = [.pos 0] := by
  rfl

/--
@isnad1 id=eq.0h0v.s5.17dfe5ad2df4 from=translated src=- shape=c6a81320 vocab=763340f4
-/
@[simp]
theorem twoMonogonSphere_boundary_one :
    twoMonogonSphere.boundary 1 = [.neg 0] := by
  rfl

/--
@isnad1 id=ne.0h1v.s3.1fc843c347c9 from=translated src=- shape=708ab39f vocab=76b9c083
-/
theorem twoMonogonSphere_boundary_nonempty (f : twoMonogonSphere.Face) :
    twoMonogonSphere.boundary f ≠ [] := by
  fin_cases f <;> simp

/--
@isnad1 id=eq.1h2v.s4.71f37fa11d6b from=translated src=- shape=52bbee88 vocab=a448a7c7
-/
theorem twoMonogonSphere_boundary_injective
    (f g : twoMonogonSphere.Face)
    (h : (twoMonogonSphere.boundary f).IsRotated
      (twoMonogonSphere.boundary g)) :
    f = g := by
  fin_cases f <;> fin_cases g
  · rfl
  · simp at h
  · simp at h
  · rfl

/--
@isnad1 id=eq.0h1v.s3.64c567939f71 from=translated src=- shape=ce544db3 vocab=31f112e2
-/
@[simp]
theorem twoMonogonSphere_edgeMultiplicity (e : twoMonogonSphere.Edge) :
    twoMonogonSphere.edgeMultiplicity e = 2 := by
  fin_cases e
  decide

/-- The P2-expanded two-monogon sphere satisfies ordinary incidence validity.
@isnad1 id=issurfac.0h0v.s1.2b9a30c002f1 from=translated src=- shape=49959d42 vocab=ac624ced
-/
theorem twoMonogonSphere_isSurfaceValid :
    twoMonogonSphere.IsSurfaceValid := by
  refine ⟨⟨0, by simp [twoMonogonSphere]⟩, twoMonogonSphere_boundary_nonempty,
    twoMonogonSphere_boundary_injective, ?_⟩
  intro e
  exact Or.inr (twoMonogonSphere_edgeMultiplicity e)

/--
@isnad1 id=faceadja.0h2v.s3.dbc5dfdabcfb from=translated src=- shape=827a9ef1 vocab=af682e25
-/
theorem twoMonogonSphere_faceAdjacent (f g : twoMonogonSphere.Face) :
    twoMonogonSphere.FaceAdjacent f g := by
  refine ⟨0, ?_, ?_⟩
  · fin_cases f <;>
      simp [boundary, twoMonogonSphere, edgeOfDart]
  · fin_cases g <;>
      simp [boundary, twoMonogonSphere, edgeOfDart]

/-- The two monogons are adjacent through their common unoriented edge.
@isnad1 id=isconnec.0h0v.s1.fbd535589479 from=translated src=- shape=49959d42 vocab=a8c6cc41
-/
theorem twoMonogonSphere_isConnected :
    twoMonogonSphere.IsConnected := by
  refine ⟨⟨0, by simp [twoMonogonSphere]⟩, ?_⟩
  intro f g
  exact Relation.ReflTransGen.single (twoMonogonSphere_faceAdjacent f g)

/-- An orientation-preserving isomorphism of finite cyclic presentations, allowing a cyclic
rotation of each face. The sign of every dart is retained under `edgeEquiv`. -/
structure PresentationIso (P Q : FiniteCyclicPresentation) where
  /-- The `edgeEquiv` declaration. -/
  edgeEquiv : P.Edge ≃ Q.Edge
  /-- The `faceEquiv` declaration. -/
  faceEquiv : P.Face ≃ Q.Face
  boundary_rotated :
    ∀ f, ((P.boundary f).map (SignedDart.mapEquiv edgeEquiv)).IsRotated
      (Q.boundary (faceEquiv f))

namespace PresentationIso

/-- The identity isomorphism of a finite cyclic presentation. -/
def refl (P : FiniteCyclicPresentation) : PresentationIso P P where
  edgeEquiv := Equiv.refl P.Edge
  faceEquiv := Equiv.refl P.Face
  boundary_rotated := by
    intro f
    rw [map_mapEquiv_refl]
    exact List.IsRotated.refl (P.boundary f)

/-- Reverse an isomorphism of finite cyclic presentations. -/
def symm {P Q : FiniteCyclicPresentation} (e : PresentationIso P Q) :
    PresentationIso Q P where
  edgeEquiv := e.edgeEquiv.symm
  faceEquiv := e.faceEquiv.symm
  boundary_rotated := by
    intro f
    have h := (e.boundary_rotated (e.faceEquiv.symm f)).symm.map
      (SignedDart.mapEquiv e.edgeEquiv.symm)
    rw [map_mapEquiv_symm] at h
    simpa only [e.faceEquiv.apply_symm_apply] using h

/-- Compose isomorphisms of finite cyclic presentations. -/
def trans {P Q R : FiniteCyclicPresentation}
    (e : PresentationIso P Q) (f : PresentationIso Q R) :
    PresentationIso P R where
  edgeEquiv := e.edgeEquiv.trans f.edgeEquiv
  faceEquiv := e.faceEquiv.trans f.faceEquiv
  boundary_rotated := by
    intro p
    have h₁ := (e.boundary_rotated p).map (SignedDart.mapEquiv f.edgeEquiv)
    have h₂ := f.boundary_rotated (e.faceEquiv p)
    rw [map_mapEquiv_trans]
    exact h₁.trans h₂

/-- A presentation isomorphism preserves the multiplicity of an edge in each corresponding
face.
@isnad1 id=eq.0h5v.s6.3682b4f39d6c from=translated src=- shape=384b0682 vocab=e0cc26e5
-/
theorem faceEdgeMultiplicity_eq {P Q : FiniteCyclicPresentation}
    (e : PresentationIso P Q) (f : P.Face) (a : P.Edge) :
    P.faceEdgeMultiplicity f a =
      Q.faceEdgeMultiplicity (e.faceEquiv f) (e.edgeEquiv a) := by
  have h := (e.boundary_rotated f).map edgeOfDart
  have hcount := h.perm.count_eq (e.edgeEquiv a)
  have hcount' :
      (((P.boundary f).map edgeOfDart).map e.edgeEquiv).count (e.edgeEquiv a) =
        ((Q.boundary (e.faceEquiv f)).map edgeOfDart).count (e.edgeEquiv a) := by
    simpa [List.map_map, Function.comp_def] using hcount
  calc
    P.faceEdgeMultiplicity f a =
        (((P.boundary f).map edgeOfDart).map e.edgeEquiv).count (e.edgeEquiv a) := by
          symm
          exact List.count_map_of_injective _ e.edgeEquiv e.edgeEquiv.injective a
    _ = Q.faceEdgeMultiplicity (e.faceEquiv f) (e.edgeEquiv a) := hcount'

/-- A presentation isomorphism preserves total edge multiplicities.
@isnad1 id=eq.0h4v.s5.501c8eafe98b from=translated src=- shape=e83d5b4b vocab=ba1ad3f5
-/
theorem edgeMultiplicity_eq {P Q : FiniteCyclicPresentation}
    (e : PresentationIso P Q) (a : P.Edge) :
    P.edgeMultiplicity a = Q.edgeMultiplicity (e.edgeEquiv a) := by
  unfold edgeMultiplicity
  exact Fintype.sum_equiv e.faceEquiv _ _ fun f ↦ e.faceEdgeMultiplicity_eq f a

/-- Corresponding face boundaries have the same length.
@isnad1 id=eq.0h4v.s5.abdd812b4a19 from=translated src=- shape=a1f71194 vocab=16ddf881
-/
theorem boundary_length_eq {P Q : FiniteCyclicPresentation}
    (e : PresentationIso P Q) (f : P.Face) :
    (P.boundary f).length = (Q.boundary (e.faceEquiv f)).length := by
  simpa using (e.boundary_rotated f).perm.length_eq

/-- Cyclic equivalence of face boundaries is preserved by a presentation isomorphism.
@isnad1 id=isrotate.1h5v.s6.e77178e1efae from=translated src=- shape=4142567a vocab=25e97979
-/
theorem map_isRotated {P Q : FiniteCyclicPresentation}
    (e : PresentationIso P Q) {f g : P.Face}
    (h : (P.boundary f).IsRotated (P.boundary g)) :
    (Q.boundary (e.faceEquiv f)).IsRotated (Q.boundary (e.faceEquiv g)) := by
  exact (e.boundary_rotated f).symm.trans
    ((h.map (SignedDart.mapEquiv e.edgeEquiv)).trans (e.boundary_rotated g))

/-- Two source boundaries are cyclically equivalent exactly when the corresponding target
boundaries are.
@isnad1 id=iff.0h5v.s6.f0e436b4bb3b from=translated src=- shape=b81cb35b vocab=25e97979
-/
theorem isRotated_iff {P Q : FiniteCyclicPresentation}
    (e : PresentationIso P Q) (f g : P.Face) :
    (P.boundary f).IsRotated (P.boundary g) ↔
      (Q.boundary (e.faceEquiv f)).IsRotated (Q.boundary (e.faceEquiv g)) := by
  constructor
  · exact e.map_isRotated
  · intro h
    simpa [PresentationIso.symm] using e.symm.map_isRotated h

/-- Face adjacency is preserved by a presentation isomorphism.
@isnad1 id=faceadja.1h5v.s6.d5114eccb213 from=translated src=- shape=da5e6f3d vocab=2897f5b8
-/
theorem map_faceAdjacent {P Q : FiniteCyclicPresentation}
    (e : PresentationIso P Q) {f g : P.Face} (h : P.FaceAdjacent f g) :
    Q.FaceAdjacent (e.faceEquiv f) (e.faceEquiv g) := by
  rcases h with ⟨a, hfa, hga⟩
  refine ⟨e.edgeEquiv a, ?_, ?_⟩
  · apply ((e.boundary_rotated f).map edgeOfDart).mem_iff.mp
    simpa [Function.comp_def] using
      (List.mem_map.mpr ⟨a, hfa, rfl⟩ :
        e.edgeEquiv a ∈ ((P.boundary f).map edgeOfDart).map e.edgeEquiv)
  · apply ((e.boundary_rotated g).map edgeOfDart).mem_iff.mp
    simpa [Function.comp_def] using
      (List.mem_map.mpr ⟨a, hga, rfl⟩ :
        e.edgeEquiv a ∈ ((P.boundary g).map edgeOfDart).map e.edgeEquiv)

/-- Face adjacency corresponds exactly under a presentation isomorphism.
@isnad1 id=iff.0h5v.s6.2987d207f88d from=translated src=- shape=cba69e09 vocab=2897f5b8
-/
theorem faceAdjacent_iff {P Q : FiniteCyclicPresentation}
    (e : PresentationIso P Q) (f g : P.Face) :
    P.FaceAdjacent f g ↔ Q.FaceAdjacent (e.faceEquiv f) (e.faceEquiv g) := by
  constructor
  · exact e.map_faceAdjacent
  · intro h
    simpa [PresentationIso.symm] using e.symm.map_faceAdjacent h

/-- Boundary-edge status is preserved by a presentation isomorphism.
@isnad1 id=iff.0h4v.s5.a9c75340ae7d from=translated src=- shape=ed239d2a vocab=86d6d901
-/
theorem isBoundaryEdge_iff {P Q : FiniteCyclicPresentation}
    (e : PresentationIso P Q) (a : P.Edge) :
    P.IsBoundaryEdge a ↔ Q.IsBoundaryEdge (e.edgeEquiv a) := by
  unfold IsBoundaryEdge
  rw [e.edgeMultiplicity_eq]

/-- Incidence validity is preserved by a presentation isomorphism.
@isnad1 id=issurfac.1h3v.s3.0f21d81a677e from=translated src=- shape=a72c41e2 vocab=480678a1
-/
theorem isSurfaceValid {P Q : FiniteCyclicPresentation}
    (e : PresentationIso P Q) (h : P.IsSurfaceValid) : Q.IsSurfaceValid := by
  refine ⟨e.faceEquiv.nonempty_congr.mp h.1, ?_, ?_, ?_⟩
  · intro q hq
    let f := e.faceEquiv.symm q
    have hlength := e.boundary_length_eq f
    rw [e.faceEquiv.apply_symm_apply] at hlength
    have hzero : (P.boundary f).length = 0 := by
      simpa only [hq, List.length_nil] using hlength
    exact h.2.1 f (List.length_eq_zero_iff.mp hzero)
  · intro q r hqr
    let f := e.faceEquiv.symm q
    let g := e.faceEquiv.symm r
    have htarget :
        (Q.boundary (e.faceEquiv f)).IsRotated (Q.boundary (e.faceEquiv g)) := by
      dsimp [f, g]
      simpa only [e.faceEquiv.apply_symm_apply] using hqr
    have hsource := (e.isRotated_iff f g).mpr htarget
    exact e.faceEquiv.symm.injective (h.2.2.1 f g hsource)
  · intro b
    let a := e.edgeEquiv.symm b
    have hmultiplicity := h.2.2.2 a
    rw [e.edgeMultiplicity_eq] at hmultiplicity
    dsimp [a] at hmultiplicity
    simpa only [e.edgeEquiv.apply_symm_apply] using hmultiplicity

/-- Incidence validity corresponds exactly under a presentation isomorphism.
@isnad1 id=iff.0h3v.s3.03fab8e4a17d from=translated src=- shape=702d8506 vocab=480678a1
-/
theorem isSurfaceValid_iff {P Q : FiniteCyclicPresentation}
    (e : PresentationIso P Q) : P.IsSurfaceValid ↔ Q.IsSurfaceValid :=
  ⟨e.isSurfaceValid, e.symm.isSurfaceValid⟩

/-- Face-incidence connectivity is preserved by a presentation isomorphism.
@isnad1 id=isconnec.1h3v.s3.224eb6672015 from=translated src=- shape=a72c41e2 vocab=49c16d7a
-/
theorem isConnected {P Q : FiniteCyclicPresentation}
    (e : PresentationIso P Q) (h : P.IsConnected) : Q.IsConnected := by
  refine ⟨e.faceEquiv.nonempty_congr.mp h.1, ?_⟩
  intro q r
  have hchain := h.2 (e.faceEquiv.symm q) (e.faceEquiv.symm r)
  have hmapped := hchain.lift e.faceEquiv fun _ _ hadj ↦ e.map_faceAdjacent hadj
  change Relation.ReflTransGen Q.FaceAdjacent
    (e.faceEquiv (e.faceEquiv.symm q)) (e.faceEquiv (e.faceEquiv.symm r)) at hmapped
  simpa only [e.faceEquiv.apply_symm_apply] using hmapped

/-- Face-incidence connectivity corresponds exactly under a presentation isomorphism.
@isnad1 id=iff.0h3v.s3.57f3eeca3c95 from=translated src=- shape=702d8506 vocab=49c16d7a
-/
theorem isConnected_iff {P Q : FiniteCyclicPresentation}
    (e : PresentationIso P Q) : P.IsConnected ↔ Q.IsConnected :=
  ⟨e.isConnected, e.symm.isConnected⟩

end PresentationIso

/-- A signed isomorphism of finite cyclic presentations. Each edge may be independently
reoriented while it is renamed; face boundary order is preserved up to cyclic rotation. -/
structure SignedPresentationIso (P Q : FiniteCyclicPresentation) where
  /-- The `edgeRelabeling` declaration. -/
  edgeRelabeling : EdgeRelabeling P.Edge Q.Edge
  /-- The `faceEquiv` declaration. -/
  faceEquiv : P.Face ≃ Q.Face
  boundary_rotated :
    ∀ f, ((P.boundary f).map edgeRelabeling.mapDart).IsRotated
      (Q.boundary (faceEquiv f))

namespace SignedPresentationIso

/-- The underlying equivalence of unoriented edge names. -/
abbrev edgeEquiv {P Q : FiniteCyclicPresentation} (e : SignedPresentationIso P Q) :
    P.Edge ≃ Q.Edge :=
  e.edgeRelabeling.edgeEquiv

/-- The orientation-reversal bit attached to a source edge. -/
abbrev reverse {P Q : FiniteCyclicPresentation} (e : SignedPresentationIso P Q) :
    P.Edge → Bool :=
  e.edgeRelabeling.reverse

/-- Regard an orientation-preserving presentation isomorphism as a general signed
isomorphism. -/
def ofPresentationIso {P Q : FiniteCyclicPresentation} (e : PresentationIso P Q) :
    SignedPresentationIso P Q where
  edgeRelabeling := EdgeRelabeling.ofEquiv e.edgeEquiv
  faceEquiv := e.faceEquiv
  boundary_rotated := by
    intro f
    rw [EdgeRelabeling.map_mapDart_ofEquiv]
    exact e.boundary_rotated f

/-- The identity signed isomorphism of a finite cyclic presentation. -/
def refl (P : FiniteCyclicPresentation) : SignedPresentationIso P P where
  edgeRelabeling := EdgeRelabeling.refl P.Edge
  faceEquiv := Equiv.refl P.Face
  boundary_rotated := by
    intro f
    rw [EdgeRelabeling.map_mapDart_refl]
    exact List.IsRotated.refl (P.boundary f)

/-- Reverse a signed isomorphism of finite cyclic presentations. -/
def symm {P Q : FiniteCyclicPresentation} (e : SignedPresentationIso P Q) :
    SignedPresentationIso Q P where
  edgeRelabeling := e.edgeRelabeling.symm
  faceEquiv := e.faceEquiv.symm
  boundary_rotated := by
    intro f
    have h := (e.boundary_rotated (e.faceEquiv.symm f)).symm.map
      e.edgeRelabeling.symm.mapDart
    rw [EdgeRelabeling.map_mapDart_symm] at h
    simpa only [e.faceEquiv.apply_symm_apply] using h

/-- Compose signed isomorphisms of finite cyclic presentations. -/
def trans {P Q R : FiniteCyclicPresentation}
    (e : SignedPresentationIso P Q) (f : SignedPresentationIso Q R) :
    SignedPresentationIso P R where
  edgeRelabeling := e.edgeRelabeling.trans f.edgeRelabeling
  faceEquiv := e.faceEquiv.trans f.faceEquiv
  boundary_rotated := by
    intro p
    have h₁ := (e.boundary_rotated p).map f.edgeRelabeling.mapDart
    have h₂ := f.boundary_rotated (e.faceEquiv p)
    rw [EdgeRelabeling.map_mapDart_trans]
    exact h₁.trans h₂

/-- A signed presentation isomorphism transports the two orientations of every face. -/
def orientedFaceEquiv {P Q : FiniteCyclicPresentation}
    (e : SignedPresentationIso P Q) :
    P.OrientedFace ≃ Q.OrientedFace where
  toFun f := ⟨e.faceEquiv f.face, f.orientation⟩
  invFun f := ⟨e.faceEquiv.symm f.face, f.orientation⟩
  left_inv := by
    intro f
    cases f
    simp
  right_inv := by
    intro f
    cases f
    simp

/--
@isnad1 id=eq.0h4v.s6.1d65d7ea6c95 from=translated src=- shape=70e89c61 vocab=545a4010
-/
@[simp]
theorem orientedFaceEquiv_face {P Q : FiniteCyclicPresentation}
    (e : SignedPresentationIso P Q) (f : P.OrientedFace) :
    (e.orientedFaceEquiv f).face = e.faceEquiv f.face :=
  rfl

/--
@isnad1 id=eq.0h4v.s5.edf09005f10e from=translated src=- shape=0179ada9 vocab=f7965b12
-/
@[simp]
theorem orientedFaceEquiv_orientation {P Q : FiniteCyclicPresentation}
    (e : SignedPresentationIso P Q) (f : P.OrientedFace) :
    (e.orientedFaceEquiv f).orientation = f.orientation :=
  rfl

/--
@isnad1 id=eq.0h4v.s6.eb1af056d687 from=translated src=- shape=09425b48 vocab=16b36be5
-/
@[simp]
theorem orientedFaceEquiv_pos {P Q : FiniteCyclicPresentation}
    (e : SignedPresentationIso P Q) (f : P.Face) :
    e.orientedFaceEquiv (.pos f) = .pos (e.faceEquiv f) :=
  rfl

/--
@isnad1 id=eq.0h4v.s6.0c2c815fcaba from=translated src=- shape=09425b48 vocab=2eabbd5a
-/
@[simp]
theorem orientedFaceEquiv_neg {P Q : FiniteCyclicPresentation}
    (e : SignedPresentationIso P Q) (f : P.Face) :
    e.orientedFaceEquiv (.neg f) = .neg (e.faceEquiv f) :=
  rfl

/--
@isnad1 id=eq.0h4v.s6.f7e0452de5cf from=translated src=- shape=a98c8e1a vocab=d293d372
-/
@[simp]
theorem orientedFaceEquiv_flip {P Q : FiniteCyclicPresentation}
    (e : SignedPresentationIso P Q) (f : P.OrientedFace) :
    e.orientedFaceEquiv f.flip = (e.orientedFaceEquiv f).flip :=
  rfl

/-- A signed presentation isomorphism transports either traversal orientation of every face
boundary up to cyclic rotation.
@isnad1 id=isrotate.0h4v.s6.2ef797ad387c from=translated src=- shape=b1f4b96b vocab=7b10479e
-/
theorem orientedBoundary_rotated {P Q : FiniteCyclicPresentation}
    (e : SignedPresentationIso P Q) (f : P.OrientedFace) :
    ((P.orientedBoundary f).map e.edgeRelabeling.mapDart).IsRotated
      (Q.orientedBoundary (e.orientedFaceEquiv f)) := by
  cases f with
  | mk face orientation =>
      cases orientation
      · exact e.boundary_rotated face
      · change
          ((inverseWord (P.boundary face)).map e.edgeRelabeling.mapDart).IsRotated
            (inverseWord (Q.boundary (e.faceEquiv face)))
        rw [← EdgeRelabeling.inverseWord_map_mapDart]
        exact inverseWord_isRotated (e.boundary_rotated face)

/-- A signed presentation isomorphism preserves edge multiplicity in each corresponding
face.
@isnad1 id=eq.0h5v.s6.bfcd9dad5dee from=translated src=- shape=384b0682 vocab=5c296384
-/
theorem faceEdgeMultiplicity_eq {P Q : FiniteCyclicPresentation}
    (e : SignedPresentationIso P Q) (f : P.Face) (a : P.Edge) :
    P.faceEdgeMultiplicity f a =
      Q.faceEdgeMultiplicity (e.faceEquiv f) (e.edgeEquiv a) := by
  have h := (e.boundary_rotated f).map edgeOfDart
  have hcount := h.perm.count_eq (e.edgeEquiv a)
  have hcount' :
      (((P.boundary f).map edgeOfDart).map e.edgeEquiv).count (e.edgeEquiv a) =
        ((Q.boundary (e.faceEquiv f)).map edgeOfDart).count (e.edgeEquiv a) := by
    simpa [List.map_map, Function.comp_def] using hcount
  calc
    P.faceEdgeMultiplicity f a =
        (((P.boundary f).map edgeOfDart).map e.edgeEquiv).count (e.edgeEquiv a) := by
          symm
          exact List.count_map_of_injective _ e.edgeEquiv e.edgeEquiv.injective a
    _ = Q.faceEdgeMultiplicity (e.faceEquiv f) (e.edgeEquiv a) := hcount'

/-- A signed presentation isomorphism preserves total edge multiplicities.
@isnad1 id=eq.0h4v.s5.8cfd5cf53399 from=translated src=- shape=e83d5b4b vocab=b0d6c0e1
-/
theorem edgeMultiplicity_eq {P Q : FiniteCyclicPresentation}
    (e : SignedPresentationIso P Q) (a : P.Edge) :
    P.edgeMultiplicity a = Q.edgeMultiplicity (e.edgeEquiv a) := by
  unfold edgeMultiplicity
  exact Fintype.sum_equiv e.faceEquiv _ _ fun f ↦ e.faceEdgeMultiplicity_eq f a

/-- Corresponding face boundaries have the same length under a signed isomorphism.
@isnad1 id=eq.0h4v.s5.c818dd26dc55 from=translated src=- shape=a1f71194 vocab=6633edec
-/
theorem boundary_length_eq {P Q : FiniteCyclicPresentation}
    (e : SignedPresentationIso P Q) (f : P.Face) :
    (P.boundary f).length = (Q.boundary (e.faceEquiv f)).length := by
  simpa using (e.boundary_rotated f).perm.length_eq

/-- Cyclic equivalence of face boundaries is preserved by a signed presentation isomorphism.
@isnad1 id=isrotate.1h5v.s6.fe60602c4d9a from=translated src=- shape=4142567a vocab=119d3c3b
-/
theorem map_isRotated {P Q : FiniteCyclicPresentation}
    (e : SignedPresentationIso P Q) {f g : P.Face}
    (h : (P.boundary f).IsRotated (P.boundary g)) :
    (Q.boundary (e.faceEquiv f)).IsRotated (Q.boundary (e.faceEquiv g)) := by
  exact (e.boundary_rotated f).symm.trans
    ((h.map e.edgeRelabeling.mapDart).trans (e.boundary_rotated g))

/-- Two source boundaries are cyclically equivalent exactly when the corresponding target
boundaries are.
@isnad1 id=iff.0h5v.s6.df8dfefcffb3 from=translated src=- shape=b81cb35b vocab=119d3c3b
-/
theorem isRotated_iff {P Q : FiniteCyclicPresentation}
    (e : SignedPresentationIso P Q) (f g : P.Face) :
    (P.boundary f).IsRotated (P.boundary g) ↔
      (Q.boundary (e.faceEquiv f)).IsRotated (Q.boundary (e.faceEquiv g)) := by
  constructor
  · exact e.map_isRotated
  · intro h
    simpa [SignedPresentationIso.symm] using e.symm.map_isRotated h

/-- Face adjacency is preserved by a signed presentation isomorphism.
@isnad1 id=faceadja.1h5v.s6.a8120afd9918 from=translated src=- shape=da5e6f3d vocab=1d222d19
-/
theorem map_faceAdjacent {P Q : FiniteCyclicPresentation}
    (e : SignedPresentationIso P Q) {f g : P.Face} (h : P.FaceAdjacent f g) :
    Q.FaceAdjacent (e.faceEquiv f) (e.faceEquiv g) := by
  rcases h with ⟨a, hfa, hga⟩
  refine ⟨e.edgeEquiv a, ?_, ?_⟩
  · apply ((e.boundary_rotated f).map edgeOfDart).mem_iff.mp
    simpa [Function.comp_def] using
      (List.mem_map.mpr ⟨a, hfa, rfl⟩ :
        e.edgeEquiv a ∈ ((P.boundary f).map edgeOfDart).map e.edgeEquiv)
  · apply ((e.boundary_rotated g).map edgeOfDart).mem_iff.mp
    simpa [Function.comp_def] using
      (List.mem_map.mpr ⟨a, hga, rfl⟩ :
        e.edgeEquiv a ∈ ((P.boundary g).map edgeOfDart).map e.edgeEquiv)

/-- Face adjacency corresponds exactly under a signed presentation isomorphism.
@isnad1 id=iff.0h5v.s6.a16a69b7631e from=translated src=- shape=cba69e09 vocab=1d222d19
-/
theorem faceAdjacent_iff {P Q : FiniteCyclicPresentation}
    (e : SignedPresentationIso P Q) (f g : P.Face) :
    P.FaceAdjacent f g ↔ Q.FaceAdjacent (e.faceEquiv f) (e.faceEquiv g) := by
  constructor
  · exact e.map_faceAdjacent
  · intro h
    simpa [SignedPresentationIso.symm] using e.symm.map_faceAdjacent h

/-- Boundary-edge status is preserved by a signed presentation isomorphism.
@isnad1 id=iff.0h4v.s5.97a06a64ec15 from=translated src=- shape=ed239d2a vocab=1dc1a67c
-/
theorem isBoundaryEdge_iff {P Q : FiniteCyclicPresentation}
    (e : SignedPresentationIso P Q) (a : P.Edge) :
    P.IsBoundaryEdge a ↔ Q.IsBoundaryEdge (e.edgeEquiv a) := by
  unfold IsBoundaryEdge
  rw [e.edgeMultiplicity_eq]

/-- Incidence validity is preserved by a signed presentation isomorphism.
@isnad1 id=issurfac.1h3v.s3.17f5731a5aa6 from=translated src=- shape=a72c41e2 vocab=3d9410f9
-/
theorem isSurfaceValid {P Q : FiniteCyclicPresentation}
    (e : SignedPresentationIso P Q) (h : P.IsSurfaceValid) : Q.IsSurfaceValid := by
  refine ⟨e.faceEquiv.nonempty_congr.mp h.1, ?_, ?_, ?_⟩
  · intro q hq
    let f := e.faceEquiv.symm q
    have hlength := e.boundary_length_eq f
    rw [e.faceEquiv.apply_symm_apply] at hlength
    have hzero : (P.boundary f).length = 0 := by
      simpa only [hq, List.length_nil] using hlength
    exact h.2.1 f (List.length_eq_zero_iff.mp hzero)
  · intro q r hqr
    let f := e.faceEquiv.symm q
    let g := e.faceEquiv.symm r
    have htarget :
        (Q.boundary (e.faceEquiv f)).IsRotated (Q.boundary (e.faceEquiv g)) := by
      dsimp [f, g]
      simpa only [e.faceEquiv.apply_symm_apply] using hqr
    have hsource := (e.isRotated_iff f g).mpr htarget
    exact e.faceEquiv.symm.injective (h.2.2.1 f g hsource)
  · intro b
    let a := e.edgeEquiv.symm b
    have hmultiplicity := h.2.2.2 a
    rw [e.edgeMultiplicity_eq] at hmultiplicity
    dsimp [a] at hmultiplicity
    simpa only [e.edgeEquiv.apply_symm_apply] using hmultiplicity

/-- Incidence validity corresponds exactly under a signed presentation isomorphism.
@isnad1 id=iff.0h3v.s3.da1722ce6161 from=translated src=- shape=702d8506 vocab=3d9410f9
-/
theorem isSurfaceValid_iff {P Q : FiniteCyclicPresentation}
    (e : SignedPresentationIso P Q) : P.IsSurfaceValid ↔ Q.IsSurfaceValid :=
  ⟨e.isSurfaceValid, e.symm.isSurfaceValid⟩

/-- Face-incidence connectivity is preserved by a signed presentation isomorphism.
@isnad1 id=isconnec.1h3v.s3.96ffeb92e2aa from=translated src=- shape=a72c41e2 vocab=a241ea1b
-/
theorem isConnected {P Q : FiniteCyclicPresentation}
    (e : SignedPresentationIso P Q) (h : P.IsConnected) : Q.IsConnected := by
  refine ⟨e.faceEquiv.nonempty_congr.mp h.1, ?_⟩
  intro q r
  have hchain := h.2 (e.faceEquiv.symm q) (e.faceEquiv.symm r)
  have hmapped := hchain.lift e.faceEquiv fun _ _ hadj ↦ e.map_faceAdjacent hadj
  change Relation.ReflTransGen Q.FaceAdjacent
    (e.faceEquiv (e.faceEquiv.symm q)) (e.faceEquiv (e.faceEquiv.symm r)) at hmapped
  simpa only [e.faceEquiv.apply_symm_apply] using hmapped

/-- Face-incidence connectivity corresponds exactly under a signed presentation isomorphism.
@isnad1 id=iff.0h3v.s3.e62c1eb87382 from=translated src=- shape=702d8506 vocab=a241ea1b
-/
theorem isConnected_iff {P Q : FiniteCyclicPresentation}
    (e : SignedPresentationIso P Q) : P.IsConnected ↔ Q.IsConnected :=
  ⟨e.isConnected, e.symm.isConnected⟩

end SignedPresentationIso

/-- The signed-isomorphism class of Gallier--Xu's exceptional one-face empty-word sphere. -/
def IsEmptyWordSphere (P : FiniteCyclicPresentation) : Prop :=
  Nonempty (SignedPresentationIso emptyWordSphere P)

/-- Gallier--Xu validity for the packed presentation layer.

The first disjunct is the ordinary nonempty-boundary case. The second is precisely the exceptional
one-face, zero-edge, empty-boundary presentation allowed by Definition 6.1. -/
def IsGallierValid (P : FiniteCyclicPresentation) : Prop :=
  (P.IsSurfaceValid ∧ P.IsConnected) ∨ P.IsEmptyWordSphere

/--
@isnad1 id=eq.1h1v.s3.58a696dd71a1 from=translated src=- shape=aa073f8f vocab=f51da672
-/
theorem IsEmptyWordSphere.edgeCount_eq_zero
    {P : FiniteCyclicPresentation} (h : P.IsEmptyWordSphere) :
    P.edgeCount = 0 := by
  rcases h with ⟨e⟩
  simpa [emptyWordSphere] using (Fintype.card_congr e.edgeEquiv).symm

/--
@isnad1 id=eq.1h1v.s4.34e3e8261fed from=translated src=- shape=85452860 vocab=58b38b52
-/
theorem IsEmptyWordSphere.faces_length_eq_one
    {P : FiniteCyclicPresentation} (h : P.IsEmptyWordSphere) :
    P.faces.length = 1 := by
  rcases h with ⟨e⟩
  simpa [emptyWordSphere] using (Fintype.card_congr e.faceEquiv).symm

/--
@isnad1 id=eq.1h2v.s4.bd511fecf817 from=translated src=- shape=5b6ab181 vocab=4ec9c8d7
-/
theorem IsEmptyWordSphere.boundary_eq_nil
    {P : FiniteCyclicPresentation} (h : P.IsEmptyWordSphere) (f : P.Face) :
    P.boundary f = [] := by
  rcases h with ⟨e⟩
  let p := e.faceEquiv.symm f
  have hlength := e.boundary_length_eq p
  rw [e.faceEquiv.apply_symm_apply] at hlength
  have hzero : (P.boundary f).length = 0 := by
    simpa only [emptyWordSphere_boundary, List.length_nil] using hlength.symm
  exact List.length_eq_zero_iff.mp hzero

/-- Intrinsic characterization of the exceptional signed-isomorphism class.
@isnad1 id=iff.0h1v.s5.ddfd830d20c0 from=translated src=- shape=37dcb3ce vocab=4e43b5ff
-/
theorem isEmptyWordSphere_iff (P : FiniteCyclicPresentation) :
    P.IsEmptyWordSphere ↔ P.edgeCount = 0 ∧ P.faces = [[]] := by
  constructor
  · intro h
    refine ⟨h.edgeCount_eq_zero, ?_⟩
    have hlength : P.faces.length = 1 := h.faces_length_eq_one
    let f : P.Face := ⟨0, by omega⟩
    calc
      P.faces = [P.faces.get f] :=
        List.eq_cons_of_length_one hlength
      _ = [[]] := by rw [show P.faces.get f = [] from h.boundary_eq_nil f]
  · rintro ⟨hedges, hfaces⟩
    cases P with
    | mk edgeCount faces =>
        dsimp at hedges hfaces
        subst edgeCount
        subst faces
        exact ⟨SignedPresentationIso.refl emptyWordSphere⟩

/--
@isnad1 id=isemptyw.0h0v.s1.096289cd2ffc from=translated src=- shape=49959d42 vocab=68c92d6d
-/
theorem emptyWordSphere_isEmptyWordSphere :
    emptyWordSphere.IsEmptyWordSphere :=
  ⟨SignedPresentationIso.refl emptyWordSphere⟩

/--
@isnad1 id=isconnec.1h1v.s2.b0daf83bf42a from=translated src=- shape=6321fd23 vocab=d72ba729
-/
theorem IsEmptyWordSphere.isConnected
    {P : FiniteCyclicPresentation} (h : P.IsEmptyWordSphere) :
    P.IsConnected := by
  rcases h with ⟨e⟩
  exact e.isConnected emptyWordSphere_isConnected

/-- Empty-word spheres are exactly the exceptional, non-ordinary branch of Gallier validity.
@isnad1 id=not.1h1v.s3.6223e55d5255 from=translated src=- shape=58f8d12c vocab=8ed96687
-/
theorem IsEmptyWordSphere.not_isSurfaceValid
    {P : FiniteCyclicPresentation} (h : P.IsEmptyWordSphere) :
    ¬ P.IsSurfaceValid := by
  intro hvalid
  rcases h with ⟨e⟩
  exact emptyWordSphere_not_isSurfaceValid (e.symm.isSurfaceValid hvalid)

/--
@isnad1 id=isgallie.1h1v.s2.1a741063a45d from=translated src=- shape=6321fd23 vocab=1321b45f
-/
theorem IsEmptyWordSphere.isGallierValid
    {P : FiniteCyclicPresentation} (h : P.IsEmptyWordSphere) :
    P.IsGallierValid :=
  Or.inr h

/--
@isnad1 id=isgallie.2h1v.s3.4521c8d5592b from=translated src=- shape=cbe5c5ba vocab=651dabc2
-/
theorem isGallierValid_of_isSurfaceValid_of_isConnected
    {P : FiniteCyclicPresentation} (hvalid : P.IsSurfaceValid)
    (hconnected : P.IsConnected) :
    P.IsGallierValid :=
  Or.inl ⟨hvalid, hconnected⟩

/--
@isnad1 id=isgallie.0h0v.s1.60f1ac7bebf2 from=translated src=- shape=49959d42 vocab=f60c8c1b
-/
theorem emptyWordSphere_isGallierValid :
    emptyWordSphere.IsGallierValid :=
  emptyWordSphere_isEmptyWordSphere.isGallierValid

/--
@isnad1 id=isgallie.0h0v.s1.6656effaaa5d from=translated src=- shape=49959d42 vocab=f6ec1e0d
-/
theorem twoMonogonSphere_isGallierValid :
    twoMonogonSphere.IsGallierValid :=
  isGallierValid_of_isSurfaceValid_of_isConnected
    twoMonogonSphere_isSurfaceValid twoMonogonSphere_isConnected

/--
@isnad1 id=isconnec.1h1v.s2.e6b42a6107c7 from=translated src=- shape=6321fd23 vocab=94e96331
-/
theorem IsGallierValid.isConnected
    {P : FiniteCyclicPresentation} (h : P.IsGallierValid) :
    P.IsConnected := by
  rcases h with hregular | hempty
  · exact hregular.2
  · exact hempty.isConnected

namespace SignedPresentationIso

/-- A signed presentation isomorphism preserves the exceptional empty-word sphere class.
@isnad1 id=isemptyw.1h3v.s3.5adc91d1e3df from=translated src=- shape=a72c41e2 vocab=2917640f
-/
theorem isEmptyWordSphere {P Q : FiniteCyclicPresentation}
    (e : SignedPresentationIso P Q) (h : P.IsEmptyWordSphere) :
    Q.IsEmptyWordSphere := by
  rcases h with ⟨i⟩
  exact ⟨i.trans e⟩

/--
@isnad1 id=iff.0h3v.s3.f0e084c149f7 from=translated src=- shape=702d8506 vocab=2917640f
-/
theorem isEmptyWordSphere_iff {P Q : FiniteCyclicPresentation}
    (e : SignedPresentationIso P Q) :
    P.IsEmptyWordSphere ↔ Q.IsEmptyWordSphere :=
  ⟨e.isEmptyWordSphere, e.symm.isEmptyWordSphere⟩

/-- Gallier--Xu validity is preserved by signed edge and face relabeling.
@isnad1 id=isgallie.1h3v.s3.adba61ff5061 from=translated src=- shape=a72c41e2 vocab=2fe9f295
-/
theorem isGallierValid {P Q : FiniteCyclicPresentation}
    (e : SignedPresentationIso P Q) (h : P.IsGallierValid) :
    Q.IsGallierValid := by
  rcases h with hregular | hempty
  · exact Or.inl ⟨e.isSurfaceValid hregular.1, e.isConnected hregular.2⟩
  · exact Or.inr (e.isEmptyWordSphere hempty)

/--
@isnad1 id=iff.0h3v.s3.91c0153bfbeb from=translated src=- shape=702d8506 vocab=2fe9f295
-/
theorem isGallierValid_iff {P Q : FiniteCyclicPresentation}
    (e : SignedPresentationIso P Q) :
    P.IsGallierValid ↔ Q.IsGallierValid :=
  ⟨e.isGallierValid, e.symm.isGallierValid⟩

end SignedPresentationIso

end FiniteCyclicPresentation
end ClassificationOfSurfaces
end Topology
end LeanEval
