/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Design.Concrete

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped BigOperators Matrix

namespace SRG266.QuasiSymmetric

section Counting

variable {α : Type*}

theorem sum_eq_card_filter [Fintype α] (a : α → ℤ) (ha : ∀ x, a x = 0 ∨ a x = 1) :
    (∑ x, a x) = ((Finset.univ.filter fun x => a x = 1).card : ℤ) := by
  have hpoint : ∀ x, a x = if a x = 1 then (1 : ℤ) else 0 := by
    intro x
    rcases ha x with h | h <;> simp [h]
  rw [Finset.sum_congr rfl fun x _ => hpoint x]
  simp

theorem sum_mul_eq_card_filter [Fintype α] (a b : α → ℤ)
    (ha : ∀ x, a x = 0 ∨ a x = 1) (hb : ∀ x, b x = 0 ∨ b x = 1) :
    (∑ x, a x * b x) =
      ((Finset.univ.filter fun x => a x = 1 ∧ b x = 1).card : ℤ) := by
  have hpoint : ∀ x, a x * b x = if a x = 1 ∧ b x = 1 then (1 : ℤ) else 0 := by
    intro x
    rcases ha x with h | h <;> rcases hb x with h' | h' <;> simp [h, h']
  rw [Finset.sum_congr rfl fun x _ => hpoint x]
  simp

theorem card_filter_subtype [DecidableEq α] (s : Finset α) (p : α → Prop)
    [DecidablePred p] :
    (Finset.univ.filter fun x : ↥s => p x.val).card = (s.filter p).card := by
  rw [← Finset.card_image_of_injective _ (Subtype.val_injective (p := (· ∈ s)))]
  congr 1
  ext x
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, hpx⟩
    exact ⟨⟨x, hx⟩, hpx, rfl⟩

theorem card_filter_of_enum [DecidableEq α] {n : ℕ} (b : Fin n → α) (s : Finset α)
    (hinj : Function.Injective b) (hrange : ∀ x, x ∈ s ↔ ∃ i, b i = x)
    (p : α → Prop) [DecidablePred p] :
    (Finset.univ.filter fun i => p (b i)).card = (s.filter p).card := by
  rw [← Finset.card_image_of_injective _ hinj]
  congr 1
  ext x
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨(hrange _).mpr ⟨i, rfl⟩, hi⟩
  · rintro ⟨hx, hpx⟩
    obtain ⟨i, rfl⟩ := (hrange x).mp hx
    exact ⟨i, hpx, rfl⟩

end Counting

namespace ConcreteQSD56

variable (Q : ConcreteQSD56)

def pointsOn (B : Fin 210) : Finset (Fin 56) :=
  Finset.univ.filter fun p => Q.matrix p B = 1

def pointsOnPair (B D : Fin 210) : Finset (Fin 56) :=
  Finset.univ.filter fun p => Q.matrix p B = 1 ∧ Q.matrix p D = 1

def blocksThrough (p : Fin 56) : Finset (Fin 210) :=
  Finset.univ.filter fun B => Q.matrix p B = 1

def blocksThroughPair (p q : Fin 56) : Finset (Fin 210) :=
  Finset.univ.filter fun B => Q.matrix p B = 1 ∧ Q.matrix q B = 1

@[simp] theorem mem_pointsOn {B : Fin 210} {p : Fin 56} :
    p ∈ Q.pointsOn B ↔ Q.matrix p B = 1 := by
  simp [pointsOn]

@[simp] theorem mem_blocksThrough {p : Fin 56} {B : Fin 210} :
    B ∈ Q.blocksThrough p ↔ Q.matrix p B = 1 := by
  simp [blocksThrough]

theorem card_pointsOn (B : Fin 210) : (Q.pointsOn B).card = 12 := by
  have hcol := Q.block_size B
  rw [incidenceColumnSum,
    sum_eq_card_filter (fun p => Q.matrix p B) fun p => Q.entry_cases p B] at hcol
  exact_mod_cast hcol

theorem card_blocksThrough (p : Fin 56) : (Q.blocksThrough p).card = 45 := by
  have hrow := Q.row_sum p
  rw [sum_eq_card_filter (fun B => Q.matrix p B) fun B => Q.entry_cases p B] at hrow
  exact_mod_cast hrow

theorem card_blocksThroughPair {p q : Fin 56} (h : p ≠ q) :
    (Q.blocksThroughPair p q).card = 9 := by
  have hgram := Q.point_gram p q
  rw [Matrix.mul_apply] at hgram
  simp only [Matrix.transpose_apply] at hgram
  rw [sum_mul_eq_card_filter (fun B => Q.matrix p B) (fun B => Q.matrix q B)
    (fun B => Q.entry_cases p B) fun B => Q.entry_cases q B, ite_eq_right h] at hgram
  exact_mod_cast hgram

theorem card_pointsOnPair {B D : Fin 210} (h : B ≠ D) :
    (Q.pointsOnPair B D).card = 0 ∨ (Q.pointsOnPair B D).card = 3 := by
  have hinter := Q.block_intersections h
  rw [Matrix.mul_apply] at hinter
  simp only [Matrix.transpose_apply] at hinter
  rw [sum_mul_eq_card_filter (fun p => Q.matrix p B) (fun p => Q.matrix p D)
    (fun p => Q.entry_cases p B) fun p => Q.entry_cases p D] at hinter
  rcases hinter with h' | h'
  · exact Or.inl (by exact_mod_cast h')
  · exact Or.inr (by exact_mod_cast h')

end ConcreteQSD56

structure Derived45 (P : Type*) [Fintype P] [DecidableEq P] where

  block : Fin 45 → Finset P

  point_card : Fintype.card P = 55

  block_card : ∀ i, (block i).card = 11

  pair_meet : ∀ i j, i ≠ j → ((block i) ∩ (block j)).card = 2

  replication : ∀ p, (Finset.univ.filter fun i => p ∈ block i).card = 9

structure Residual165 {P : Type*} [Fintype P] [DecidableEq P] (E : Derived45 P) where

  res : Fin 165 → Finset P

  res_card : ∀ n, (res n).card = 12

  res_meet : ∀ m n, m ≠ n →
    ((res m) ∩ (res n)).card = 0 ∨ ((res m) ∩ (res n)).card = 3

  cross_meet : ∀ i n,
    ((E.block i) ∩ (res n)).card = 0 ∨ ((E.block i) ∩ (res n)).card = 3

  res_rep : ∀ p, (Finset.univ.filter fun n => p ∈ res n).card = 36

  res_inj : Function.Injective res

abbrev Punctured (z : Fin 56) : Type := ↥((Finset.univ : Finset (Fin 56)).erase z)

theorem card_punctured (z : Fin 56) : Fintype.card (Punctured z) = 55 := by
  rw [Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ z)]
  simp

namespace ConcreteQSD56

variable (Q : ConcreteQSD56) (z : Fin 56)

def derivedIndex : Finset (Fin 210) := Q.blocksThrough z

def residualIndex : Finset (Fin 210) :=
  Finset.univ.filter fun B => Q.matrix z B = 0

def restrictedBlock (B : Fin 210) : Finset (Punctured z) :=
  Finset.univ.filter fun p => Q.matrix p.val B = 1

variable {Q z}

@[simp] theorem mem_derivedIndex {B : Fin 210} :
    B ∈ Q.derivedIndex z ↔ Q.matrix z B = 1 := by
  simp [derivedIndex]

@[simp] theorem mem_residualIndex {B : Fin 210} :
    B ∈ Q.residualIndex z ↔ Q.matrix z B = 0 := by
  simp [residualIndex]

@[simp] theorem mem_restrictedBlock {B : Fin 210} {p : Punctured z} :
    p ∈ Q.restrictedBlock z B ↔ Q.matrix p.val B = 1 := by
  simp [restrictedBlock]

variable (Q z)

theorem card_derivedIndex : (Q.derivedIndex z).card = 45 :=
  Q.card_blocksThrough z

theorem card_residualIndex : (Q.residualIndex z).card = 165 := by
  have hsplit :=
    Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 210)))
      (p := fun B => Q.matrix z B = 1)
  have hneg : (Finset.univ.filter fun B => ¬ Q.matrix z B = 1) = Q.residualIndex z := by
    ext B
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_residualIndex]
    rcases Q.entry_cases z B with h | h <;> simp [h]
  have hpos : (Finset.univ.filter fun B => Q.matrix z B = 1) = Q.derivedIndex z := rfl
  rw [hpos, hneg, card_derivedIndex] at hsplit
  simp only [Finset.card_univ, Fintype.card_fin] at hsplit
  omega

theorem restrictedBlock_card (B : Fin 210) :
    (Q.restrictedBlock z B).card = ((Q.pointsOn B).erase z).card := by
  rw [restrictedBlock,
    card_filter_subtype (Finset.univ.erase z) fun p => Q.matrix p B = 1,
    Finset.filter_erase]
  rfl

theorem restrictedBlock_inter_card (B D : Fin 210) :
    (Q.restrictedBlock z B ∩ Q.restrictedBlock z D).card =
      ((Q.pointsOnPair B D).erase z).card := by
  have hand :
      Q.restrictedBlock z B ∩ Q.restrictedBlock z D =
        Finset.univ.filter fun p : Punctured z =>
          Q.matrix p.val B = 1 ∧ Q.matrix p.val D = 1 := by
    ext p
    simp [restrictedBlock]
  rw [hand,
    card_filter_subtype (Finset.univ.erase z)
      fun p => Q.matrix p B = 1 ∧ Q.matrix p D = 1,
    Finset.filter_erase]
  rfl

variable {Q z}

theorem card_restrictedBlock_of_through {B : Fin 210} (h : Q.matrix z B = 1) :
    (Q.restrictedBlock z B).card = 11 := by
  have hmem : z ∈ Q.pointsOn B := Q.mem_pointsOn.mpr h
  rw [restrictedBlock_card, Finset.card_erase_of_mem hmem, Q.card_pointsOn B]

theorem card_restrictedBlock_of_missing {B : Fin 210} (h : Q.matrix z B = 0) :
    (Q.restrictedBlock z B).card = 12 := by
  have hmem : z ∉ Q.pointsOn B := by
    simp only [ConcreteQSD56.mem_pointsOn, h]
    norm_num
  rw [restrictedBlock_card, Finset.erase_eq_of_notMem hmem, Q.card_pointsOn B]

theorem card_restrictedBlock_inter_of_through {B D : Fin 210}
    (hB : Q.matrix z B = 1) (hD : Q.matrix z D = 1) (hBD : B ≠ D) :
    (Q.restrictedBlock z B ∩ Q.restrictedBlock z D).card = 2 := by
  have hmem : z ∈ Q.pointsOnPair B D := by
    simp only [pointsOnPair, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hB, hD⟩
  have hpos : (Q.pointsOnPair B D).card ≠ 0 := by
    intro hzero
    rw [Finset.card_eq_zero] at hzero
    exact absurd hmem (by simp [hzero])
  have hthree : (Q.pointsOnPair B D).card = 3 :=
    (Q.card_pointsOnPair hBD).resolve_left hpos
  rw [restrictedBlock_inter_card, Finset.card_erase_of_mem hmem, hthree]

theorem card_restrictedBlock_inter_of_missing {B D : Fin 210}
    (hD : Q.matrix z D = 0) (hBD : B ≠ D) :
    (Q.restrictedBlock z B ∩ Q.restrictedBlock z D).card = 0 ∨
      (Q.restrictedBlock z B ∩ Q.restrictedBlock z D).card = 3 := by
  have hmem : z ∉ Q.pointsOnPair B D := by
    simp only [pointsOnPair, Finset.mem_filter, Finset.mem_univ, true_and, hD,
      not_and]
    intro _
    norm_num
  rw [restrictedBlock_inter_card, Finset.erase_eq_of_notMem hmem]
  exact Q.card_pointsOnPair hBD

theorem card_derivedIndex_filter {p : Fin 56} (hp : p ≠ z) :
    ((Q.derivedIndex z).filter fun B => Q.matrix p B = 1).card = 9 := by
  have hfilter :
      (Q.derivedIndex z).filter (fun B => Q.matrix p B = 1) =
        Q.blocksThroughPair z p := by
    ext B
    simp only [Finset.mem_filter, mem_derivedIndex, blocksThroughPair,
      Finset.mem_univ, true_and]
  rw [hfilter]
  exact Q.card_blocksThroughPair (Ne.symm hp)

theorem card_residualIndex_filter {p : Fin 56} (hp : p ≠ z) :
    ((Q.residualIndex z).filter fun B => Q.matrix p B = 1).card = 36 := by
  have hsplit :=
    Finset.card_filter_add_card_filter_not (s := Q.blocksThrough p)
      (p := fun B => Q.matrix z B = 1)
  have hpos :
      ((Q.blocksThrough p).filter fun B => Q.matrix z B = 1) =
        (Q.derivedIndex z).filter fun B => Q.matrix p B = 1 := by
    ext B
    simp only [Finset.mem_filter, mem_blocksThrough, mem_derivedIndex]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  have hneg :
      ((Q.blocksThrough p).filter fun B => ¬ Q.matrix z B = 1) =
        (Q.residualIndex z).filter fun B => Q.matrix p B = 1 := by
    ext B
    simp only [Finset.mem_filter, mem_blocksThrough, mem_residualIndex]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(Q.entry_cases z B).resolve_right h2, h1⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h2, ?_⟩
      rw [h1]
      norm_num
  rw [hpos, hneg, card_derivedIndex_filter hp, Q.card_blocksThrough p] at hsplit
  omega

end ConcreteQSD56

namespace ConcreteQSD56

variable (Q : ConcreteQSD56) (z : Fin 56)

noncomputable def derivedEnum (i : Fin 45) : Fin 210 :=
  ((Finset.equivFinOfCardEq (card_derivedIndex Q z)).symm i : Fin 210)

noncomputable def residualEnum (n : Fin 165) : Fin 210 :=
  ((Finset.equivFinOfCardEq (card_residualIndex Q z)).symm n : Fin 210)

variable {Q z}

theorem derivedEnum_mem (i : Fin 45) : Q.derivedEnum z i ∈ Q.derivedIndex z :=
  ((Finset.equivFinOfCardEq (card_derivedIndex Q z)).symm i).2

theorem residualEnum_mem (n : Fin 165) : Q.residualEnum z n ∈ Q.residualIndex z :=
  ((Finset.equivFinOfCardEq (card_residualIndex Q z)).symm n).2

theorem derivedEnum_one (i : Fin 45) : Q.matrix z (Q.derivedEnum z i) = 1 :=
  mem_derivedIndex.mp (derivedEnum_mem i)

theorem residualEnum_zero (n : Fin 165) : Q.matrix z (Q.residualEnum z n) = 0 :=
  mem_residualIndex.mp (residualEnum_mem n)

theorem derivedEnum_injective : Function.Injective (Q.derivedEnum z) := fun _ _ hij =>
  (Finset.equivFinOfCardEq (card_derivedIndex Q z)).symm.injective (Subtype.ext hij)

theorem residualEnum_injective : Function.Injective (Q.residualEnum z) := fun _ _ hmn =>
  (Finset.equivFinOfCardEq (card_residualIndex Q z)).symm.injective (Subtype.ext hmn)

theorem derivedEnum_range (B : Fin 210) :
    B ∈ Q.derivedIndex z ↔ ∃ i, Q.derivedEnum z i = B := by
  constructor
  · intro hB
    exact ⟨Finset.equivFinOfCardEq (card_derivedIndex Q z) ⟨B, hB⟩, by simp [derivedEnum]⟩
  · rintro ⟨i, rfl⟩
    exact derivedEnum_mem i

theorem residualEnum_range (B : Fin 210) :
    B ∈ Q.residualIndex z ↔ ∃ n, Q.residualEnum z n = B := by
  constructor
  · intro hB
    exact ⟨Finset.equivFinOfCardEq (card_residualIndex Q z) ⟨B, hB⟩, by simp [residualEnum]⟩
  · rintro ⟨n, rfl⟩
    exact residualEnum_mem n

theorem derivedEnum_ne_residualEnum (i : Fin 45) (n : Fin 165) :
    Q.derivedEnum z i ≠ Q.residualEnum z n := by
  intro h
  have h1 := derivedEnum_one (Q := Q) (z := z) i
  rw [h, residualEnum_zero (Q := Q) (z := z) n] at h1
  norm_num at h1

variable (Q z)

noncomputable def derived45 : Derived45 (Punctured z) where
  block i := Q.restrictedBlock z (Q.derivedEnum z i)
  point_card := card_punctured z
  block_card i := card_restrictedBlock_of_through (derivedEnum_one i)
  pair_meet i j hij :=
    card_restrictedBlock_inter_of_through (derivedEnum_one i) (derivedEnum_one j)
      fun h => hij (derivedEnum_injective h)
  replication := by
    classical
    intro p
    have hp : p.val ≠ z := (Finset.mem_erase.mp p.2).1
    rw [show (Finset.univ.filter fun i => p ∈ Q.restrictedBlock z (Q.derivedEnum z i)) =
        Finset.univ.filter fun i => Q.matrix p.val (Q.derivedEnum z i) = 1 by
      ext i; simp]
    rw [card_filter_of_enum (Q.derivedEnum z) (Q.derivedIndex z) derivedEnum_injective
      derivedEnum_range fun B => Q.matrix p.val B = 1]
    exact card_derivedIndex_filter hp

noncomputable def residual165 : Residual165 (Q.derived45 z) where
  res n := Q.restrictedBlock z (Q.residualEnum z n)
  res_card n := card_restrictedBlock_of_missing (residualEnum_zero n)
  res_meet m n hmn :=
    card_restrictedBlock_inter_of_missing (residualEnum_zero n)
      fun h => hmn (residualEnum_injective h)
  cross_meet i n :=
    card_restrictedBlock_inter_of_missing (residualEnum_zero n)
      (derivedEnum_ne_residualEnum i n)
  res_rep := by
    classical
    intro p
    have hp : p.val ≠ z := (Finset.mem_erase.mp p.2).1
    rw [show (Finset.univ.filter fun n => p ∈ Q.restrictedBlock z (Q.residualEnum z n)) =
        Finset.univ.filter fun n => Q.matrix p.val (Q.residualEnum z n) = 1 by
      ext n; simp]
    rw [card_filter_of_enum (Q.residualEnum z) (Q.residualIndex z) residualEnum_injective
      residualEnum_range fun B => Q.matrix p.val B = 1]
    exact card_residualIndex_filter hp
  res_inj := by
    intro m n hmn
    by_contra hne
    have hmeet :=
      card_restrictedBlock_inter_of_missing (Q := Q) (z := z) (residualEnum_zero n)
        (fun h => hne (residualEnum_injective h))
    rw [show Q.restrictedBlock z (Q.residualEnum z m) =
        Q.restrictedBlock z (Q.residualEnum z n) from hmn, Finset.inter_self,
      card_restrictedBlock_of_missing (residualEnum_zero n)] at hmeet
    omega

end ConcreteQSD56

theorem exists_derived_residual_at (Q : ConcreteQSD56) (z : Fin 56) :
    ∃ (P : Type) (instF : Fintype P) (instD : DecidableEq P)
      (E : @Derived45 P instF instD), Nonempty (@Residual165 P instF instD E) :=
  ⟨Punctured z, inferInstance, inferInstance, Q.derived45 z, ⟨Q.residual165 z⟩⟩

theorem exists_derived_residual (Q : ConcreteQSD56) :
    ∃ (P : Type) (instF : Fintype P) (instD : DecidableEq P)
      (E : @Derived45 P instF instD), Nonempty (@Residual165 P instF instD E) :=
  exists_derived_residual_at Q 0

end SRG266.QuasiSymmetric
