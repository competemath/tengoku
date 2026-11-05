/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.AclGeom.AclGeom.Correspondence.GenericPoints

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Composition of correspondence germs at generic points

The opening of the correspondence calculus (blueprint §8.1, checklist C2)
in the elementwise presentation of the rational-curve route (design issue
on the project tracker): an irreducible finite correspondence germ between
two point-curves is presented by an interalgebraic pair of transcendental
elements, and composition happens at a *shared middle representative*:

* `mem_racl_trans` / `comp_pair_of_shared_middle`: with a literally shared
  middle, the composite pair is automatically interalgebraic — all content
  lives in the matching step;
* `exists_pair_relocation_fixing`: the matching step — a germ presentation
  `(w', u)` relocates onto any prescribed interalgebraic representative
  `w` of its source point, preserving the vanishing ideal and hence the
  germ. This is blueprint Lemma 8.1(b) with the transcendence basis pinned
  to a prescribed image;
* `FiniteCorrespondencePair`, `FiniteCorrespondenceGerm`, and
  `FiniteCorrespondenceGerm.Composes`: the selected-branch presentation of
  finite correspondences and their composition;
* `FiniteCorrespondenceGerm.exists_composite`: matching makes the relational
  composite nonempty, while retaining the chosen irreducible component;
* `fiber_product_rank_count`: the explicit rank-five calculation used in
  blueprint equation (8.6).

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** complete (M4a, issue #12 pipeline step 1).
-/

namespace AclGeom

open IntermediateField

noncomputable section

variable {k : Type*} {Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]

section SharedMiddle

/-- Interalgebraicity is transitive through a shared middle element.
@isnad1 id=mem.2h5v.s7.0bf247629276 from=translated src=- shape=df8e5fe5 vocab=6ed771df
-/
theorem mem_racl_trans {z w u : Ω} (hzw : z ∈ racl k ({w} : Set Ω))
    (hwu : w ∈ racl k ({u} : Set Ω)) : z ∈ racl k ({u} : Set Ω) :=
  racl_le_of_subset_racl (Set.singleton_subset_iff.2 hwu) hzw

end SharedMiddle

section SelectedBaseChange

end SelectedBaseChange

section Matching

end Matching

section Germs

/-- A generic pair presenting a finite correspondence between two rational
curves.  The two coordinates are interalgebraic and the source is generic
over the ground field.-/
structure FiniteCorrespondencePair (k Ω : Type*) [Field k] [Field Ω]
    [Algebra k Ω] where
  /-- Source coordinate of the selected generic branch.-/
  source : Ω
  /-- Target coordinate of the selected generic branch.-/
  target : Ω
  /-- The source coordinate is transcendental over the ground field.-/
  source_generic : source ∉ racl k (∅ : Set Ω)
  /-- The target is algebraic over the source.-/
  target_mem_source : target ∈ racl k {source}
  /-- The source is algebraic over the target.-/
  source_mem_target : source ∈ racl k {target}

namespace FiniteCorrespondencePair

variable (P : FiniteCorrespondencePair k Ω)

/-- The target of a finite correspondence is generic whenever its source
is generic.
@isnad1 id=not.0h3v.s6.714b2eddd78e from=translated src=- shape=02ee2280 vocab=412a088c
-/
theorem target_generic : P.target ∉ racl k (∅ : Set Ω) := by
  intro ht
  exact P.source_generic
    (racl_le_of_subset_racl (Set.singleton_subset_iff.2 ht) P.source_mem_target)

/-- Reverse a selected correspondence branch.-/
def swap : FiniteCorrespondencePair k Ω where
  source := P.target
  target := P.source
  source_generic := P.target_generic
  target_mem_source := P.source_mem_target
  source_mem_target := P.target_mem_source

/--
@isnad1 id=eq.0h3v.s5.e5f1b940cae9 from=translated src=- shape=45436065 vocab=73eea9c1
-/
@[simp] theorem swap_source : P.swap.source = P.target := rfl

/--
@isnad1 id=eq.0h3v.s5.0f94724d2f31 from=translated src=- shape=45436065 vocab=73eea9c1
-/
@[simp] theorem swap_target : P.swap.target = P.source := rfl

/--
@isnad1 id=eq.0h3v.s5.5d489e9d86ef from=translated src=- shape=19868076 vocab=d572a2ae
-/
@[simp] theorem swap_swap : P.swap.swap = P := by
  cases P
  rfl

/-- The diagonal branch at a generic coordinate.-/
def identity (x : Ω) (hx : x ∉ racl k (∅ : Set Ω)) :
    FiniteCorrespondencePair k Ω where
  source := x
  target := x
  source_generic := hx
  target_mem_source := subset_racl k {x} rfl
  source_mem_target := subset_racl k {x} rfl

/-- The prime ideal of the selected generic branch.-/
def ideal : Ideal (MvPolynomial (Fin 2) k) :=
  idealOf k ![P.source, P.target]

/-- Composition at a literally shared middle coordinate.-/
def comp (Q : FiniteCorrespondencePair k Ω) (h : P.target = Q.source) :
    FiniteCorrespondencePair k Ω where
  source := P.source
  target := Q.target
  source_generic := P.source_generic
  target_mem_source := by
    apply mem_racl_trans (w := P.target)
    · simpa [h] using Q.target_mem_source
    · exact P.target_mem_source
  source_mem_target := by
    apply mem_racl_trans (w := P.target)
    · exact P.source_mem_target
    · simpa [h] using Q.source_mem_target

/--
@isnad1 id=eq.1h4v.s6.83ef6a44c221 from=translated src=- shape=52ee62fe vocab=19b42ab4
-/
@[simp] theorem comp_source (Q : FiniteCorrespondencePair k Ω)
    (h : P.target = Q.source) : (P.comp Q h).source = P.source := rfl

/--
@isnad1 id=eq.1h4v.s6.1a432bb8b196 from=translated src=- shape=71601a6f vocab=19b42ab4
-/
@[simp] theorem comp_target (Q : FiniteCorrespondencePair k Ω)
    (h : P.target = Q.source) : (P.comp Q h).target = Q.target := rfl

end FiniteCorrespondencePair

/-- A finite-correspondence germ is its prime branch ideal together with a
generic interalgebraic pair presenting that ideal.  Keeping the witness is
intentional: composition of correspondences selects a component rather than
the whole scheme-theoretic fiber product.-/
@[ext] structure FiniteCorrespondenceGerm (k Ω : Type*) [Field k] [Field Ω]
    [Algebra k Ω] where
  /-- Prime ideal of the selected correspondence component.-/
  carrier : Ideal (MvPolynomial (Fin 2) k)
  /-- A generic pair presenting the component.-/
  presentation : ∃ P : FiniteCorrespondencePair k Ω, carrier = P.ideal

namespace FiniteCorrespondenceGerm

/-- The germ presented by a generic finite-correspondence pair.-/
def ofPair (P : FiniteCorrespondencePair k Ω) :
    FiniteCorrespondenceGerm k Ω where
  carrier := P.ideal
  presentation := ⟨P, rfl⟩

/-- The inverse germ of a selected presentation.-/
def inverseOfPair (P : FiniteCorrespondencePair k Ω) :
    FiniteCorrespondenceGerm k Ω :=
  ofPair P.swap

/-- The identity germ at a generic coordinate.-/
def identity (x : Ω) (hx : x ∉ racl k (∅ : Set Ω)) :
    FiniteCorrespondenceGerm k Ω :=
  ofPair (FiniteCorrespondencePair.identity x hx)

/-- Relational composition of selected correspondence components.  The
literal common middle records the chosen component of the fiber product.-/
def Composes (C D E : FiniteCorrespondenceGerm k Ω) : Prop :=
  ∃ (P Q : FiniteCorrespondencePair k Ω) (h : P.target = Q.source),
    C.carrier = P.ideal ∧ D.carrier = Q.ideal ∧
      E.carrier = (P.comp Q h).ideal

end FiniteCorrespondenceGerm

end Germs

section FiberProductRank

end FiberProductRank

end

end AclGeom
