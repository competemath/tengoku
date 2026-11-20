/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Design.CanonicalBiplane

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped BigOperators

namespace SRG266.QuasiSymmetric

structure TripleDesign57 (P B : Type*) [Fintype P] [DecidableEq P]
    [Fintype B] [DecidableEq B] where
  point_card : Fintype.card P = 57
  index_card : Fintype.card B = 266
  block : B → Finset P
  block_size : ∀ b, (block b).card = 12
  replication : ∀ p, (Finset.univ.filter fun b => p ∈ block b).card = 56
  point_pair : ∀ p q, p ≠ q →
    (Finset.univ.filter fun b => p ∈ block b ∧ q ∈ block b).card = 11
  point_triple : ∀ p q r, p ≠ q → p ≠ r → q ≠ r →
    (Finset.univ.filter fun b => p ∈ block b ∧ q ∈ block b ∧ r ∈ block b).card = 2
  block_intersections : ∀ b c, b ≠ c →
    (block b ∩ block c).card = 0 ∨ (block b ∩ block c).card = 3

namespace ConcreteQSD56

set_option maxRecDepth 2048

variable (Q : ConcreteQSD56)

abbrev ExtensionPoint := Option (Fin 56)

abbrev ExtensionBlock := Fin 210 ⊕ ↥Q.canonicalBiplaneBlocks

noncomputable def extensionBlock : Q.ExtensionBlock → Finset ExtensionPoint
  | Sum.inl B => (Q.pointsOn B).map ⟨Option.some, Option.some_injective _⟩
  | Sum.inr S => insert none (S.val.map ⟨Option.some, Option.some_injective _⟩)

@[simp] theorem some_mem_extensionBlock_old (p : Fin 56) (B : Fin 210) :
    some p ∈ Q.extensionBlock (Sum.inl B) ↔ Q.matrix p B = 1 := by
  simp [extensionBlock]

@[simp] theorem none_notMem_extensionBlock_old (B : Fin 210) :
    none ∉ Q.extensionBlock (Sum.inl B) := by simp [extensionBlock]

@[simp] theorem some_mem_extensionBlock_new (p : Fin 56)
    (S : ↥Q.canonicalBiplaneBlocks) :
    some p ∈ Q.extensionBlock (Sum.inr S) ↔ p ∈ S.val := by
  simp [extensionBlock]

@[simp] theorem none_mem_extensionBlock_new (S : ↥Q.canonicalBiplaneBlocks) :
    none ∈ Q.extensionBlock (Sum.inr S) := by simp [extensionBlock]

theorem extensionPoint_card : Fintype.card ExtensionPoint = 57 := by
  simp [ExtensionPoint]

theorem extensionBlock_card : Fintype.card Q.ExtensionBlock = 266 := by
  simp [ExtensionBlock, Q.canonicalBiplane_card]

theorem extensionBlock_size (b : Q.ExtensionBlock) : (Q.extensionBlock b).card = 12 := by
  rcases b with b | S
  · simp [extensionBlock, Q.card_pointsOn]
  · simp [extensionBlock, Q.canonicalBiplane_block_card S.property]

theorem count_extensionBlock (R : Q.ExtensionBlock → Prop) [DecidablePred R] :
    (Finset.univ.filter R).card =
      (Finset.univ.filter fun b : Fin 210 => R (Sum.inl b)).card +
      (Finset.univ.filter fun S : ↥Q.canonicalBiplaneBlocks => R (Sum.inr S)).card := by
  simp only [Finset.card_filter, Fintype.sum_sum_type]

theorem count_canonicalBiplaneSubtype (R : Finset (Fin 56) → Prop) [DecidablePred R] :
    (Finset.univ.filter fun S : ↥Q.canonicalBiplaneBlocks => R S.val).card =
      (Q.canonicalBiplaneBlocks.filter R).card := by
  classical
  refine Finset.card_bij (fun S _ => S.val) ?_ ?_ ?_
  · intro S hS
    exact Finset.mem_filter.mpr ⟨S.property, (Finset.mem_filter.mp hS).2⟩
  · intro S hS T hT h
    exact Subtype.ext h
  · intro S hS
    exact ⟨⟨S,(Finset.mem_filter.mp hS).1⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hS).2⟩, rfl⟩

theorem extension_replication (p : ExtensionPoint) :
    (Finset.univ.filter fun b => p ∈ Q.extensionBlock b).card = 56 := by
  rw [Q.count_extensionBlock]
  cases p with
  | none => simp [Q.canonicalBiplane_card]
  | some p =>
    simp only [some_mem_extensionBlock_old, some_mem_extensionBlock_new]
    rw [Q.count_canonicalBiplaneSubtype (fun S => p ∈ S), Q.canonicalBiplane_replication]
    change (Q.blocksThrough p).card + 11 = 56
    rw [Q.card_blocksThrough]

theorem extension_point_pair (p q : ExtensionPoint) (hpq : p ≠ q) :
    (Finset.univ.filter fun b => p ∈ Q.extensionBlock b ∧ q ∈ Q.extensionBlock b).card = 11 := by
  rw [Q.count_extensionBlock]
  cases p with
  | none =>
    cases q with
    | none => exact (hpq rfl).elim
    | some q =>
      simp only [none_notMem_extensionBlock_old, false_and, Finset.filter_false,
        Finset.card_empty, none_mem_extensionBlock_new, true_and,
        some_mem_extensionBlock_new, zero_add]
      rw [Q.count_canonicalBiplaneSubtype (fun S => q ∈ S), Q.canonicalBiplane_replication]
  | some p =>
    cases q with
    | none =>
      simp only [none_notMem_extensionBlock_old, and_false, Finset.filter_false,
        Finset.card_empty, none_mem_extensionBlock_new, and_true,
        some_mem_extensionBlock_new, zero_add]
      rw [Q.count_canonicalBiplaneSubtype (fun S => p ∈ S), Q.canonicalBiplane_replication]
    | some q =>
      have hne : p ≠ q := fun h => hpq (congrArg some h)
      simp only [some_mem_extensionBlock_old, some_mem_extensionBlock_new]
      rw [Q.count_canonicalBiplaneSubtype (fun S => p ∈ S ∧ q ∈ S),
        Q.canonicalBiplane_point_pair hne]
      change (Q.blocksThroughPair p q).card + 2 = 11
      rw [Q.card_blocksThroughPair hne]

theorem extension_point_triple (p q r : ExtensionPoint)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    (Finset.univ.filter fun b => p ∈ Q.extensionBlock b ∧
      q ∈ Q.extensionBlock b ∧ r ∈ Q.extensionBlock b).card = 2 := by
  rw [Q.count_extensionBlock]
  cases p <;> cases q <;> cases r
  all_goals try exact (hpq rfl).elim
  all_goals try exact (hpr rfl).elim
  all_goals try exact (hqr rfl).elim
  all_goals simp only [none_notMem_extensionBlock_old, none_mem_extensionBlock_new,
    some_mem_extensionBlock_old, some_mem_extensionBlock_new, false_and,
    and_false, true_and, and_true, Finset.filter_false, Finset.card_empty,
    zero_add]
  · rename_i q r
    rw [Q.count_canonicalBiplaneSubtype (fun S => q ∈ S ∧ r ∈ S)]
    exact Q.canonicalBiplane_point_pair (fun h => hqr (congrArg some h))
  · rename_i p r
    rw [Q.count_canonicalBiplaneSubtype (fun S => p ∈ S ∧ r ∈ S)]
    exact Q.canonicalBiplane_point_pair (fun h => hpr (congrArg some h))
  · rename_i p q
    rw [Q.count_canonicalBiplaneSubtype (fun S => p ∈ S ∧ q ∈ S)]
    exact Q.canonicalBiplane_point_pair (fun h => hpq (congrArg some h))
  · rename_i p q r
    rw [Q.count_canonicalBiplaneSubtype (fun S => p ∈ S ∧ q ∈ S ∧ r ∈ S)]
    exact Q.canonicalBiplane_triple_complement (fun h => hpq (congrArg some h))
      (fun h => hpr (congrArg some h)) (fun h => hqr (congrArg some h))

theorem extension_block_intersections (b c : Q.ExtensionBlock) (hbc : b ≠ c) :
    (Q.extensionBlock b ∩ Q.extensionBlock c).card = 0 ∨
      (Q.extensionBlock b ∩ Q.extensionBlock c).card = 3 := by
  rcases b with b | S <;> rcases c with c | T
  · have hne : b ≠ c := fun h => hbc (congrArg Sum.inl h)
    have h := Q.card_pointsOnPair hne
    have heq : Q.pointsOn b ∩ Q.pointsOn c = Q.pointsOnPair b c := by
      ext p
      simp [pointsOnPair]
    simpa only [extensionBlock, ← Finset.map_inter, Finset.card_map, heq] using h
  · have h := Q.canonicalBiplane_old_block_intersections T.property b
    simpa [extensionBlock, Finset.inter_insert_of_notMem,
      ← Finset.map_inter] using h
  · have h := Q.canonicalBiplane_old_block_intersections S.property c
    simpa [extensionBlock, Finset.insert_inter_of_notMem,
      ← Finset.map_inter, Finset.inter_comm] using h
  · have hne : S.val ≠ T.val := fun h => hbc (congrArg Sum.inr (Subtype.ext h))
    right
    simp [extensionBlock, ← Finset.map_inter,
      Q.canonicalBiplane_block_pair S.property T.property hne]

noncomputable def toTripleDesign57 : TripleDesign57 ExtensionPoint Q.ExtensionBlock where
  point_card := extensionPoint_card
  index_card := Q.extensionBlock_card
  block := Q.extensionBlock
  block_size := Q.extensionBlock_size
  replication := Q.extension_replication
  point_pair := Q.extension_point_pair
  point_triple := Q.extension_point_triple
  block_intersections := Q.extension_block_intersections

end ConcreteQSD56
end SRG266.QuasiSymmetric
