/-
Copyright (c) 2026 Jeremy Parker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy P Parker
-/
import Tengoku.Seed.Order.Preorder.Chain
import Tengoku.Seed.Order.WithBot

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Maximal chains after adjoining a top

Adjoining one new greatest element does not change the type of maximal
chains: every maximal chain acquires that element, and deleting it leaves a
maximal chain of the original partial order.
-/

open Set

namespace HansenCograph
namespace Flag

universe u

variable {P : Type u} [PartialOrder P]

/-- Delete the adjoined greatest element from a maximal chain.-/
def dropWithTop (s : Flag (WithTop P)) : Flag P where
  carrier := {x | (x : WithTop P) ∈ s}
  Chain' := by
    intro x hx y hy hxy
    simpa using s.chain_le.total hx hy
  max_chain' := by
    intro t ht hsub
    apply Set.Subset.antisymm hsub
    intro x hxt
    apply (Flag.mem_iff_forall_le_or_ge).2
    intro c hc
    induction c using WithTop.recTopCoe with
    | top => exact Or.inl le_top
    | coe c =>
        have hct : c ∈ t := hsub hc
        simpa using ht.total hxt hct

@[simp] theorem mem_dropWithTop (s : Flag (WithTop P)) (x : P) :
    x ∈ dropWithTop s ↔ (x : WithTop P) ∈ s := Iff.rfl

/-- Add a new greatest element to a maximal chain.-/
def addWithTop (s : Flag P) : Flag (WithTop P) where
  carrier := ((↑) : P → WithTop P) '' (s : Set P) ∪ {⊤}
  Chain' := by
    intro x hx y hy hxy
    rcases hx with ⟨a, ha, rfl⟩ | hx
    · rcases hy with ⟨b, hb, rfl⟩ | hy
      · simpa using s.chain_le.total ha hb
      · have : y = ⊤ := by simpa using hy
        subst y
        exact Or.inl le_top
    · have : x = ⊤ := by simpa using hx
      subst x
      rcases hy with ⟨b, hb, rfl⟩ | hy
      · exact Or.inr le_top
      · have : y = ⊤ := by simpa using hy
        subst y
        exact False.elim (hxy rfl)
  max_chain' := by
    intro t ht hsub
    apply Set.Subset.antisymm hsub
    intro x hxt
    induction x using WithTop.recTopCoe with
    | top => exact Or.inr (by simp)
    | coe x =>
        apply Or.inl
        refine ⟨x, ?_, rfl⟩
        apply (Flag.mem_iff_forall_le_or_ge).2
        intro y hy
        have hy' : (y : WithTop P) ∈ t :=
          hsub (Or.inl ⟨y, hy, rfl⟩)
        simpa using ht.total hxt hy'

@[simp] theorem coe_mem_addWithTop (s : Flag P) (x : P) :
    (x : WithTop P) ∈ addWithTop s ↔ x ∈ s := by
  change (x : WithTop P) ∈
    (((↑) : P → WithTop P) '' (s : Set P) ∪ {⊤}) ↔ x ∈ s
  simp

@[simp] theorem top_mem_addWithTop (s : Flag P) :
    (⊤ : WithTop P) ∈ addWithTop s := by
  exact Or.inr (by simp)

/-- Maximal chains are unchanged by adjoining one new greatest element.-/
def withTopEquiv : Flag (WithTop P) ≃ Flag P where
  toFun := dropWithTop
  invFun := addWithTop
  left_inv s := by
    apply Flag.ext
    ext x
    induction x using WithTop.recTopCoe with
    | top => simp [Flag.top_mem]
    | coe x => simp
  right_inv s := by
    apply Flag.ext
    ext x
    simp

end Flag
end HansenCograph
