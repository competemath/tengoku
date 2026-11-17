/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.Seed.Data.Set.Prod

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Relation algebra

This file provides a small unbundled algebra for binary relations represented as subsets of a
product. It deliberately reuses `Set.graphOn` for graphs rather than introducing a second graph
representation.
-/

open Set

universe u v w t u' v'

namespace DescriptiveSetTheory

variable {X : Type u} {Y : Type v} {Z : Type w} {W : Type t}

/-- Swap the two coordinates of a relation.-/
def swapRelation (R : Set (X × Y)) : Set (Y × X) :=
  {q | (q.2, q.1) ∈ R}

/-- The set of first coordinates occurring in a relation.-/
def relationDomain (R : Set (X × Y)) : Set X :=
  {x | ∃ y, (x, y) ∈ R}

/-- The set of second coordinates occurring in a relation.-/
def relationRange (R : Set (X × Y)) : Set Y :=
  {y | ∃ x, (x, y) ∈ R}

/-- Relational composition, read from left to right: first `R`, then `S`.-/
def relationComp (R : Set (X × Y)) (S : Set (Y × Z)) : Set (X × Z) :=
  {q | ∃ y, (q.1, y) ∈ R ∧ (y, q.2) ∈ S}

/-- Pull a relation back along maps on its two coordinates.-/
def relationPreimage {A : Type*} {B : Type*} (f : A → X) (g : B → Y)
    (R : Set (X × Y)) : Set (A × B) :=
  Prod.map f g ⁻¹' R

/-- Image of a relation under equivalences of its two coordinates. The inverse-image presentation
keeps membership and section equations definitional.-/
def relationEquivImage {X' : Type u'} {Y' : Type v'} (eX : X ≃ X') (eY : Y ≃ Y')
    (R : Set (X × Y)) : Set (X' × Y') :=
  {q | (eX.symm q.1, eY.symm q.2) ∈ R}

/--
@isnad1 id=iff.0h4v.s5.e25dcd281d87 from=translated src=- shape=04c64f7b vocab=c17abc5f
-/
@[simp] theorem mem_swapRelation {R : Set (X × Y)} {q : Y × X} :
    q ∈ swapRelation R ↔ (q.2, q.1) ∈ R :=
  Iff.rfl

/--
@isnad1 id=iff.0h4v.s5.96414e3acf06 from=translated src=- shape=ced668d1 vocab=7b184519
-/
@[simp] theorem mem_relationDomain {R : Set (X × Y)} {x : X} :
    x ∈ relationDomain R ↔ ∃ y, (x, y) ∈ R :=
  Iff.rfl

/--
@isnad1 id=iff.0h4v.s5.c61ad06d5c07 from=translated src=- shape=b9d7eb82 vocab=aee020d3
-/
@[simp] theorem mem_relationRange {R : Set (X × Y)} {y : Y} :
    y ∈ relationRange R ↔ ∃ x, (x, y) ∈ R :=
  Iff.rfl

/--
@isnad1 id=iff.0h6v.s6.8623f12ac907 from=translated src=- shape=a4afabfa vocab=aab58825
-/
@[simp] theorem mem_relationComp {R : Set (X × Y)} {S : Set (Y × Z)} {q : X × Z} :
    q ∈ relationComp R S ↔ ∃ y, (q.1, y) ∈ R ∧ (y, q.2) ∈ S :=
  Iff.rfl

/--
@isnad1 id=iff.0h8v.s6.d2a73f09ab4d from=translated src=- shape=928e157d vocab=8ba550b9
-/
@[simp] theorem mem_relationPreimage {A : Type*} {B : Type*} (f : A → X) (g : B → Y)
    (R : Set (X × Y)) (q : A × B) :
    q ∈ relationPreimage f g R ↔ (f q.1, g q.2) ∈ R :=
  Iff.rfl

/--
@isnad1 id=iff.0h8v.s6.6e8ce3de3467 from=translated src=- shape=38a06a4c vocab=27e26cb5
-/
@[simp] theorem mem_relationEquivImage {X' : Type u'} {Y' : Type v'}
    (eX : X ≃ X') (eY : Y ≃ Y') (R : Set (X × Y)) (q : X' × Y') :
    q ∈ relationEquivImage eX eY R ↔ (eX.symm q.1, eY.symm q.2) ∈ R :=
  Iff.rfl

/-- The inverse-image presentation is extensionally the ordinary product-equivalence image.
@isnad1 id=eq.0h7v.s6.b68917811edd from=translated src=- shape=c9469c75 vocab=469f1792
-/
theorem relationEquivImage_eq_image_prodMap {X' : Type u'} {Y' : Type v'}
    (eX : X ≃ X') (eY : Y ≃ Y') (R : Set (X × Y)) :
    relationEquivImage eX eY R = Prod.map eX eY '' R := by
  ext q
  constructor
  · intro hq
    refine ⟨(eX.symm q.1, eY.symm q.2), hq, ?_⟩
    simp
  · rintro ⟨q, hq, rfl⟩
    simpa using hq

/--
@isnad1 id=eq.0h3v.s4.f83b0f47aecf from=translated src=- shape=e99dfaae vocab=a2be53ca
-/
@[simp] theorem swapRelation_swap (R : Set (X × Y)) :
    swapRelation (swapRelation R) = R := by
  ext q
  rfl

/--
@isnad1 id=eq.0h3v.s5.d7bc6a8e0415 from=translated src=- shape=72969cc2 vocab=ebb6f966
-/
@[simp] theorem swapRelation_compl (R : Set (X × Y)) :
    swapRelation Rᶜ = (swapRelation R)ᶜ := by
  ext q
  rfl

/--
@isnad1 id=eq.0h4v.s5.17bbed93e82f from=translated src=- shape=ce47c053 vocab=2f6eada8
-/
@[simp] theorem swapRelation_union (R S : Set (X × Y)) :
    swapRelation (R ∪ S) = swapRelation R ∪ swapRelation S := by
  ext q
  rfl

/--
@isnad1 id=eq.0h4v.s5.98de66f19aa8 from=translated src=- shape=ce47c053 vocab=3ee66d2b
-/
@[simp] theorem swapRelation_inter (R S : Set (X × Y)) :
    swapRelation (R ∩ S) = swapRelation R ∩ swapRelation S := by
  ext q
  rfl

/-- Relational composition is associative.
@isnad1 id=eq.0h7v.s5.b9cd60efb5e7 from=translated src=- shape=4d264d61 vocab=1b373af5
-/
theorem relationComp_assoc (R : Set (X × Y)) (S : Set (Y × Z)) (T : Set (Z × W)) :
    relationComp (relationComp R S) T = relationComp R (relationComp S T) := by
  ext q
  simp only [mem_relationComp]
  constructor
  · rintro ⟨z, ⟨y, hxy, hyz⟩, hzw⟩
    exact ⟨y, hxy, z, hyz, hzw⟩
  · rintro ⟨y, hxy, z, hyz, hzw⟩
    exact ⟨z, ⟨y, hxy, hyz⟩, hzw⟩

/-- Swapping reverses relational composition.
@isnad1 id=eq.0h5v.s5.7833fad45f2f from=translated src=- shape=4dc446ca vocab=25702274
-/
theorem swapRelation_comp (R : Set (X × Y)) (S : Set (Y × Z)) :
    swapRelation (relationComp R S) = relationComp (swapRelation S) (swapRelation R) := by
  ext q
  simp only [mem_swapRelation, mem_relationComp]
  constructor
  · rintro ⟨y, hxy, hyz⟩
    exact ⟨y, hyz, hxy⟩
  · rintro ⟨y, hyz, hxy⟩
    exact ⟨y, hxy, hyz⟩

/--
@isnad1 id=eq.0h4v.s4.8e7f796d5368 from=translated src=- shape=e8bdd2a3 vocab=3c8b05bb
-/
@[simp] theorem relationDomain_graphOn (s : Set X) (f : X → Y) :
    relationDomain (s.graphOn f) = s := by
  ext x
  simp

/--
@isnad1 id=eq.0h4v.s4.beb2f9449a9a from=translated src=- shape=63171ea2 vocab=13f821e1
-/
@[simp] theorem relationRange_graphOn (s : Set X) (f : X → Y) :
    relationRange (s.graphOn f) = f '' s := by
  ext y
  simp [eq_comm]

/-- Composition of functional graphs agrees with function composition.
@isnad1 id=eq.0h6v.s5.eddb37689587 from=translated src=- shape=003b91d2 vocab=2db40189
-/
theorem relationComp_graphOn (s : Set X) (f : X → Y) (g : Y → Z) :
    relationComp (s.graphOn f) (univ.graphOn g) = s.graphOn (g ∘ f) := by
  ext q
  simp [Function.comp_def]

end DescriptiveSetTheory
