/-
Copyright (c) 2026 Elan Roth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elan Roth
-/
module

public import Tengoku
public import Tengoku.LeanPool.LeanPool.UlmsTheorem.PGroups.UlmSubgroups

/-!
# Socle-level constructions

This file contains the p-socle and its interaction with the Ulm filtration.
-/

@[expose] public section

namespace UlmsTheorem

open Ordinal

variable (p : ℕ)

/-- The `p`-socle `P = {x | p • x = 0}`. -/
def pSocle {G : Type*} [AddCommGroup G] : AddSubgroup G where
  carrier   := {x | p • x = 0}
  zero_mem' := by simp
  add_mem'  := by
    rintro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    rw [smul_add, ha, hb, add_zero]
  neg_mem'  := by
    rintro a ha
    simp only [Set.mem_ofPred_eq] at *
    rw [smul_neg, ha, neg_zero]

section SocleLemmas

variable {G : Type*} [AddCommGroup G]

/--
@isnad1 id=iff.0h3v.s6.aa77b2a9c99b from=translated src=- shape=fa2971e6 vocab=2181463d
-/
@[simp] lemma mem_pSocle (x : G) : x ∈ pSocle p (G := G) ↔ p • x = 0 := Iff.rfl

/-- The filtered socle `P_α = P ∩ G_α`. -/
noncomputable def pSocleAt (α : Ordinal) : AddSubgroup G :=
  pSocle p ⊓ ulmSubgroup p α

/--
@isnad1 id=iff.0h4v.s6.4abbb2f5d0ef from=translated src=- shape=03c3c786 vocab=2ea90118
-/
@[simp] lemma mem_pSocleAt (α : Ordinal) (x : G) :
    x ∈ pSocleAt p α (G := G) ↔ p • x = 0 ∧ x ∈ ulmSubgroup p α := Iff.rfl

/--
@isnad1 id=eq.0h2v.s4.4b32a07ad8c7 from=translated src=- shape=3ed6f2aa vocab=b6448174
-/
lemma pSocleAt_zero : pSocleAt p (0 : Ordinal) (G := G) = pSocle p := by
  simp [pSocleAt, ulmSubgroup_zero]

/--
@isnad1 id=antitone.0h2v.s5.1f8afa7800fb from=translated src=- shape=0f0b298a vocab=f8de8058
-/
lemma pSocleAt_antitone : Antitone (fun α ↦ pSocleAt p α (G := G)) := fun _ _ h ↦
  inf_le_inf_left _ (ulmSubgroup_antitone p h)

/--
@isnad1 id=le.0h3v.s5.9909887c4929 from=translated src=- shape=dec31855 vocab=51e2804e
-/
lemma pSocleAt_succ_le (α : Ordinal) :
    pSocleAt p (Order.succ α) (G := G) ≤ pSocleAt p α :=
  pSocleAt_antitone p (Order.le_succ α)

/--
@isnad1 id=le.0h3v.s5.9a041699744f from=translated src=- shape=bcd66024 vocab=d4cfbb2f
-/
lemma pSocleAt_le_pSocle (α : Ordinal) :
    pSocleAt p α (G := G) ≤ pSocle p :=
  inf_le_left

noncomputable instance pSocleZModModule :
    Module (ZMod p) (pSocle p (G := G)) := by
  classical
  refine AddCommGroup.zmodModule (n := p) (G := pSocle p (G := G)) ?_
  intro x
  apply Subtype.ext
  exact x.property

noncomputable instance pSocleAtZModModule (α : Ordinal) :
    Module (ZMod p) (pSocleAt p α (G := G)) := by
  classical
  refine AddCommGroup.zmodModule (n := p) (G := pSocleAt p α (G := G)) ?_
  intro x
  have hx : p • (x : G) = 0 := (mem_pSocleAt p α (x : G)).1 x.property |>.1
  ext
  simp [hx]

/-- `P_{α+1}` viewed as a subgroup of `P_α`. -/
noncomputable def pSocleAtSuccSubgroupOf (α : Ordinal) :
    AddSubgroup (pSocleAt p α (G := G)) :=
  (pSocleAt p (Order.succ α) (G := G)).comap
    (AddSubgroup.subtype (pSocleAt p α))

noncomputable instance pSocleAtQuotModule (α : Ordinal) :
    Module (ZMod p) ((pSocleAt p α (G := G)) ⧸ pSocleAtSuccSubgroupOf p α) := by
  classical
  refine QuotientAddGroup.zmodModule (n := p)
    (G := pSocleAt p α (G := G)) (H := pSocleAtSuccSubgroupOf p α) ?_
  intro x
  have hx' : p • (x : G) = 0 := (mem_pSocleAt p α (x : G)).1 x.property |>.1
  have hx : p • x = 0 := by
    ext
    simp [hx']
  simp [hx]

end SocleLemmas

end UlmsTheorem
