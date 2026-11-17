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

@[simp] theorem mem_swapRelation {R : Set (X × Y)} {q : Y × X} :
    q ∈ swapRelation R ↔ (q.2, q.1) ∈ R :=
  Iff.rfl

@[simp] theorem mem_relationDomain {R : Set (X × Y)} {x : X} :
    x ∈ relationDomain R ↔ ∃ y, (x, y) ∈ R :=
  Iff.rfl

@[simp] theorem mem_relationRange {R : Set (X × Y)} {y : Y} :
    y ∈ relationRange R ↔ ∃ x, (x, y) ∈ R :=
  Iff.rfl

@[simp] theorem mem_relationComp {R : Set (X × Y)} {S : Set (Y × Z)} {q : X × Z} :
    q ∈ relationComp R S ↔ ∃ y, (q.1, y) ∈ R ∧ (y, q.2) ∈ S :=
  Iff.rfl

@[simp] theorem mem_relationPreimage {A : Type*} {B : Type*} (f : A → X) (g : B → Y)
    (R : Set (X × Y)) (q : A × B) :
    q ∈ relationPreimage f g R ↔ (f q.1, g q.2) ∈ R :=
  Iff.rfl

@[simp] theorem mem_relationEquivImage {X' : Type u'} {Y' : Type v'}
    (eX : X ≃ X') (eY : Y ≃ Y') (R : Set (X × Y)) (q : X' × Y') :
    q ∈ relationEquivImage eX eY R ↔ (eX.symm q.1, eY.symm q.2) ∈ R :=
  Iff.rfl

/-- The inverse-image presentation is extensionally the ordinary product-equivalence image.-/
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

@[simp] theorem swapRelation_swap (R : Set (X × Y)) :
    swapRelation (swapRelation R) = R := by
  ext q
  rfl

@[simp] theorem swapRelation_compl (R : Set (X × Y)) :
    swapRelation Rᶜ = (swapRelation R)ᶜ := by
  ext q
  rfl

@[simp] theorem swapRelation_union (R S : Set (X × Y)) :
    swapRelation (R ∪ S) = swapRelation R ∪ swapRelation S := by
  ext q
  rfl

@[simp] theorem swapRelation_inter (R S : Set (X × Y)) :
    swapRelation (R ∩ S) = swapRelation R ∩ swapRelation S := by
  ext q
  rfl

/-- Relational composition is associative.-/
theorem relationComp_assoc (R : Set (X × Y)) (S : Set (Y × Z)) (T : Set (Z × W)) :
    relationComp (relationComp R S) T = relationComp R (relationComp S T) := by
  ext q
  simp only [mem_relationComp]
  constructor
  · rintro ⟨z, ⟨y, hxy, hyz⟩, hzw⟩
    exact ⟨y, hxy, z, hyz, hzw⟩
  · rintro ⟨y, hxy, z, hyz, hzw⟩
    exact ⟨z, ⟨y, hxy, hyz⟩, hzw⟩

/-- Swapping reverses relational composition.-/
theorem swapRelation_comp (R : Set (X × Y)) (S : Set (Y × Z)) :
    swapRelation (relationComp R S) = relationComp (swapRelation S) (swapRelation R) := by
  ext q
  simp only [mem_swapRelation, mem_relationComp]
  constructor
  · rintro ⟨y, hxy, hyz⟩
    exact ⟨y, hyz, hxy⟩
  · rintro ⟨y, hyz, hxy⟩
    exact ⟨y, hxy, hyz⟩

@[simp] theorem relationDomain_graphOn (s : Set X) (f : X → Y) :
    relationDomain (s.graphOn f) = s := by
  ext x
  simp

@[simp] theorem relationRange_graphOn (s : Set X) (f : X → Y) :
    relationRange (s.graphOn f) = f '' s := by
  ext y
  simp [eq_comm]

/-- Composition of functional graphs agrees with function composition.-/
theorem relationComp_graphOn (s : Set X) (f : X → Y) (g : Y → Z) :
    relationComp (s.graphOn f) (univ.graphOn g) = s.graphOn (g ∘ f) := by
  ext q
  simp [Function.comp_def]

end DescriptiveSetTheory
