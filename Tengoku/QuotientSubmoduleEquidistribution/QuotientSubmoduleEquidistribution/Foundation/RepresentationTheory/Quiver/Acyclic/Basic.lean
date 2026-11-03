/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Adapted for the quotient-submodule equidistribution formalization from TauCeti commit
eeb5b4bee8bf17747ded538639102901e2cd1116.
-/
module

public import Tengoku.Seed.Combinatorics.Quiver.Path.Vertices
public import Tengoku.Seed.Data.List.Nodup

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Acyclic quivers

This file defines an acyclic quiver to be one whose closed paths are all trivial. It develops
the elementary path API for excluding directed cycles, including the fact that paths cannot run
in both directions between distinct vertices.

This is the orientation-sensitive notion of acyclicity used for path algebras and quiver
representations. It is distinct from acyclicity of the underlying undirected graph.

## References

This file implements the Layer 0 “Acyclicity, as a predicate” target of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/Suggested.lean` and its
`README.md`.
-/

public section

namespace QuotientSubmoduleEquidistribution.Foundation

open Quiver

universe u v

variable {V : Type u} [Quiver.{v} V]

/-- A quiver is acyclic if every closed path is trivial.-/
def Quiver.IsAcyclic (V : Type u) [Quiver.{v} V] : Prop :=
  ∀ ⦃a : V⦄ (p : Path a a), p = Path.nil

/-- The defining closed-path condition for an acyclic quiver.
@isnad1 id=iff.0h1v.s4.a67b9e183c8b from=translated src=- shape=ed97c526 vocab=afdca58c
-/
theorem Quiver.isAcyclic_def :
    Quiver.IsAcyclic V ↔ ∀ ⦃a : V⦄ (p : Path a a), p = Path.nil :=
  Iff.rfl

namespace Quiver.IsAcyclic

/-- Every closed path in an acyclic quiver is trivial.-/
theorem eq_nil (h : Quiver.IsAcyclic V) {a : V} (p : Path a a) : p = Path.nil :=
  h p

/-- A quiver is acyclic exactly when every closed path has length zero.
@isnad1 id=iff.0h1v.s4.50b8a59d205a from=translated src=- shape=72b9f4b8 vocab=787850ab
-/
theorem iff_forall_length_eq_zero :
    Quiver.IsAcyclic V ↔ ∀ ⦃a : V⦄ (p : Path a a), p.length = 0 := by
  constructor
  · intro h a p
    rw [h.eq_nil p]
    exact Path.length_nil
  · intro h a p
    exact p.eq_nil_of_length_zero (h p)

/-- In an acyclic quiver, every closed path has length zero.
@isnad1 id=eq.1h3v.s4.0cc3542b1659 from=translated src=- shape=e61dd936 vocab=787850ab
-/
@[simp]
theorem length_eq_zero (h : Quiver.IsAcyclic V) {a : V} (p : Path a a) :
    p.length = 0 :=
  iff_forall_length_eq_zero.mp h p

/-- An acyclic quiver has no closed path of positive length.
@isnad1 id=not.1h3v.s5.893fb90b6dfa from=translated src=- shape=83152a67 vocab=591bb970
-/
theorem not_length_pos (h : Quiver.IsAcyclic V) {a : V} (p : Path a a) :
    ¬0 < p.length := by
  rw [h.length_eq_zero p]
  exact Nat.lt_irrefl 0

/-- A quiver is acyclic exactly when it has no closed path of positive length.
@isnad1 id=iff.0h1v.s5.cf1e8547977e from=translated src=- shape=062c4db8 vocab=591bb970
-/
theorem iff_forall_not_length_pos :
    Quiver.IsAcyclic V ↔ ∀ ⦃a : V⦄ (p : Path a a), ¬0 < p.length := by
  constructor
  · exact fun h a p ↦ h.not_length_pos p
  · intro h a p
    apply p.eq_nil_of_length_zero
    have hp := h p
    omega

/-- A quiver is acyclic exactly when it has no nontrivial closed path.
@isnad1 id=iff.0h1v.s5.2473228d3a68 from=translated src=- shape=14f00ff7 vocab=afdca58c
-/
theorem iff_not_exists_ne_nil :
    Quiver.IsAcyclic V ↔ ¬∃ (a : V) (p : Path a a), p ≠ Path.nil := by
  constructor
  · intro h hex
    obtain ⟨a, p, hp⟩ := hex
    exact hp (h.eq_nil p)
  · intro h a p
    by_contra hp
    exact h ⟨a, p, hp⟩

/-- The composition of paths in opposite directions is trivial in an acyclic quiver.
@isnad1 id=eq.1h5v.s5.b2529c98e3a0 from=translated src=- shape=50c7b36d vocab=a1db8949
-/
@[simp]
theorem comp_eq_nil (h : Quiver.IsAcyclic V) {a b : V}
    (p : Path a b) (q : Path b a) :
    p.comp q = Path.nil :=
  h.eq_nil (p.comp q)

/-- If paths run in both directions in an acyclic quiver, the forward path has length zero.
@isnad1 id=eq.1h5v.s5.87323a7d893e from=translated src=- shape=c817ac45 vocab=787850ab
-/
theorem length_eq_zero_of_paths_left (h : Quiver.IsAcyclic V) {a b : V}
    (p : Path a b) (q : Path b a) :
    p.length = 0 :=
  Path.nil_of_comp_eq_nil_left (h.comp_eq_nil p q)

/-- If paths run in both directions in an acyclic quiver, the reverse path has length zero.
@isnad1 id=eq.1h5v.s5.40084d049eea from=translated src=- shape=8490bb21 vocab=787850ab
-/
theorem length_eq_zero_of_paths_right (h : Quiver.IsAcyclic V) {a b : V}
    (p : Path a b) (q : Path b a) :
    q.length = 0 :=
  h.length_eq_zero_of_paths_left q p

/-- Vertices joined by paths in both directions in an acyclic quiver are equal.-/
theorem eq_of_paths (h : Quiver.IsAcyclic V) {a b : V}
    (p : Path a b) (q : Path b a) :
    a = b :=
  p.eq_of_length_zero (h.length_eq_zero_of_paths_left p q)

/-- The vertices encountered by a path in an acyclic quiver are pairwise distinct.
@isnad1 id=nodup.1h4v.s4.1b99ea9624a7 from=translated src=- shape=1843594b vocab=010fd90c
-/
theorem vertices_nodup (h : Quiver.IsAcyclic V) {a b : V} (p : Path a b) :
    p.vertices.Nodup := by
  induction p with
  | nil => simp
  | cons p e ih =>
    rw [Path.vertices_cons, List.nodup_concat]
    refine ⟨?_, ih⟩
    intro he
    obtain ⟨p₁, p₂, hp⟩ := p.exists_eq_comp_of_mem_vertices he
    have hlength := h.length_eq_zero (p₂.cons e)
    rw [Path.length_cons] at hlength
    omega

/-- Between distinct vertices of an acyclic quiver, paths cannot exist in both directions.
@isnad1 id=not.2h3v.s5.faaae997f001 from=translated src=- shape=849196ee vocab=804e0f2f
-/
theorem not_nonempty_path_and_nonempty_path (h : Quiver.IsAcyclic V) {a b : V}
    (hab : a ≠ b) :
    ¬(Nonempty (Path a b) ∧ Nonempty (Path b a)) := by
  rintro ⟨⟨p⟩, ⟨q⟩⟩
  exact hab (h.eq_of_paths p q)

/-- A path between distinct vertices of an acyclic quiver excludes every reverse path.
@isnad1 id=isempty.2h4v.s4.a693fe04a829 from=translated src=- shape=aacf7958 vocab=2b3c731d
-/
theorem isEmpty_path_of_path (h : Quiver.IsAcyclic V) {a b : V}
    (hab : a ≠ b) (p : Path a b) :
    IsEmpty (Path b a) :=
  ⟨fun q ↦ hab (h.eq_of_paths p q)⟩

/-- An acyclic quiver has no loops.
@isnad1 id=isempty.1h2v.s4.acb4fb713f0a from=translated src=- shape=ca4f0bef vocab=df5636ac
-/
theorem isEmpty_hom_self (h : Quiver.IsAcyclic V) (a : V) :
    IsEmpty (a ⟶ a) :=
  ⟨fun e ↦ Path.cons_ne_nil Path.nil e (h e.toPath)⟩

/-- In an acyclic quiver, an arrow excludes every reverse arrow.
@isnad1 id=isempty.1h4v.s4.a2b334cbf2fd from=translated src=- shape=6ee35eaf vocab=df5636ac
-/
theorem isEmpty_hom_of_hom (h : Quiver.IsAcyclic V) {a b : V}
    (e : a ⟶ b) : IsEmpty (b ⟶ a) :=
  ⟨fun f ↦ by simpa using h.length_eq_zero_of_paths_left e.toPath f.toPath⟩

/-- Closed paths in an acyclic quiver form a subsingleton.
@isnad1 id=subsingl.1h2v.s4.a66627254c42 from=translated src=- shape=ca4f0bef vocab=b898e617
-/
theorem subsingleton_path_self (h : Quiver.IsAcyclic V) (a : V) :
    Subsingleton (Path a a) :=
  ⟨fun p q ↦ (h.eq_nil p).trans (h.eq_nil q).symm⟩

/-- A quiver with no arrows is acyclic.
@isnad1 id=isacycli.0h1v.s4.db738db73cd2 from=translated src=- shape=c2c583e4 vocab=df5636ac
-/
theorem of_isEmpty_hom [∀ a b : V, IsEmpty (a ⟶ b)] :
    Quiver.IsAcyclic V := by
  intro a p
  cases p with
  | nil => rfl
  | cons _ e => exact isEmptyElim e

/-- A quiver mapping to an acyclic quiver is acyclic if the induced map on each closed-path
type is injective.
@isnad1 id=isacycli.2h3v.s5.e1e65de339cb from=translated src=- shape=dff6fde6 vocab=a97c4002
-/
theorem of_mapPath_self_injective {W : Type*} [Quiver W] (F : V ⥤q W)
    (hW : Quiver.IsAcyclic W)
    (hinj : ∀ ⦃a : V⦄, Function.Injective (F.mapPath : Path a a → Path (F.obj a) (F.obj a))) :
    Quiver.IsAcyclic V := by
  intro a p
  apply hinj
  rw [hW.eq_nil (F.mapPath p)]
  exact F.mapPath_nil a

/-- A quiver is acyclic if its induced maps on all path types are injective and its target is
acyclic.
@isnad1 id=isacycli.2h3v.s5.cbd4bb8c50f0 from=translated src=- shape=169ddbfd vocab=a97c4002
-/
theorem of_mapPath_injective {W : Type*} [Quiver W] (F : V ⥤q W)
    (hW : Quiver.IsAcyclic W)
    (hinj : ∀ ⦃a b : V⦄, Function.Injective (F.mapPath : Path a b → Path (F.obj a) (F.obj b))) :
    Quiver.IsAcyclic V :=
  of_mapPath_self_injective F hW fun {_} ↦ @hinj _ _

end Quiver.IsAcyclic

end QuotientSubmoduleEquidistribution.Foundation
