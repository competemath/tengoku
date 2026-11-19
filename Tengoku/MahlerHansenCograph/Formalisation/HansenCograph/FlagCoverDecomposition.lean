/-
Copyright (c) 2026 Jeremy Parker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy P Parker
-/
import Tengoku.Seed.Order.Cover
import Tengoku.Seed.Order.LatticeIntervals
import Tengoku.Seed.Order.Preorder.Chain

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Decomposing maximal chains at a cover

A maximal chain containing a cover `a ⋖ b` is exactly a maximal chain in
the lower interval `Iic a` together with a maximal chain in the upper
interval `Ici b`.  This general order-theoretic result is the first counting
step in the Hansen portal recurrence.
-/

open Set

namespace HansenCograph
namespace Flag

universe u

variable {P : Type u} [PartialOrder P]

/-- Restrict a maximal chain containing `a` to the lower interval at `a`.-/
noncomputable def restrictIic (s : Flag P) (a : P) (ha : a ∈ s) :
    Flag (Set.Iic a) where
  carrier := {x | x.1 ∈ s}
  Chain' := by
    intro x hx y hy hxy
    exact s.chain_le.total hx hy
  max_chain' := by
    intro t ht hsub
    apply Set.Subset.antisymm hsub
    intro x hxt
    have hx : x.1 ∈ s := (Flag.mem_iff_forall_le_or_ge).2 (by
      intro c hc
      rcases s.le_or_le ha hc with hac | hca
      · exact Or.inl (x.2.trans hac)
      · let c' : Set.Iic a := ⟨c, hca⟩
        have hc't : c' ∈ t := hsub hc
        rcases ht.total hxt hc't with hxc | hcx
        · exact Or.inl hxc
        · exact Or.inr hcx)
    exact hx

/-- Restrict a maximal chain containing `b` to the upper interval at `b`.-/
noncomputable def restrictIci (s : Flag P) (b : P) (hb : b ∈ s) :
    Flag (Set.Ici b) where
  carrier := {x | x.1 ∈ s}
  Chain' := by
    intro x hx y hy hxy
    exact s.chain_le.total hx hy
  max_chain' := by
    intro t ht hsub
    apply Set.Subset.antisymm hsub
    intro x hxt
    have hx : x.1 ∈ s := (Flag.mem_iff_forall_le_or_ge).2 (by
      intro c hc
      rcases s.le_or_le hb hc with hbc | hcb
      · let c' : Set.Ici b := ⟨c, hbc⟩
        have hc't : c' ∈ t := hsub hc
        rcases ht.total hxt hc't with hxc | hcx
        · exact Or.inl hxc
        · exact Or.inr hcx
      · exact Or.inr (hcb.trans x.2))
    exact hx

/-- Glue lower- and upper-interval maximal chains across a cover.-/
noncomputable def glueCover {a b : P} (hab : a ⋖ b)
    (lo : Flag (Set.Iic a)) (hi : Flag (Set.Ici b)) : Flag P where
  carrier := Subtype.val '' (lo : Set (Set.Iic a)) ∪
    Subtype.val '' (hi : Set (Set.Ici b))
  Chain' := by
    intro x hx y hy hxy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · rcases hx with ⟨x', hx', rfl⟩
      rcases hy with ⟨y', hy', rfl⟩
      exact lo.chain_le.total hx' hy'
    · rcases hx with ⟨x', hx', rfl⟩
      rcases hy with ⟨y', hy', rfl⟩
      exact Or.inl (x'.2.trans (hab.le.trans y'.2))
    · rcases hx with ⟨x', hx', rfl⟩
      rcases hy with ⟨y', hy', rfl⟩
      exact Or.inr (y'.2.trans (hab.le.trans x'.2))
    · rcases hx with ⟨x', hx', rfl⟩
      rcases hy with ⟨y', hy', rfl⟩
      exact hi.chain_le.total hx' hy'
  max_chain' := by
    intro t ht hsub
    apply Set.Subset.antisymm hsub
    intro c hc
    have ha : a ∈ t := hsub (Or.inl
      ⟨⟨a, le_rfl⟩, Flag.top_mem lo, rfl⟩)
    have hb : b ∈ t := hsub (Or.inr
      ⟨⟨b, le_rfl⟩, Flag.bot_mem hi, rfl⟩)
    by_cases hca : c ≤ a
    · apply Or.inl
      refine ⟨⟨c, hca⟩, ?_, rfl⟩
      apply (Flag.mem_iff_forall_le_or_ge).2
      intro x hx
      have hx' : x.1 ∈ t := hsub (Or.inl ⟨x, hx, rfl⟩)
      exact ht.total hc hx'
    by_cases hbc : b ≤ c
    · apply Or.inr
      refine ⟨⟨c, hbc⟩, ?_, rfl⟩
      apply (Flag.mem_iff_forall_le_or_ge).2
      intro x hx
      have hx' : x.1 ∈ t := hsub (Or.inr ⟨x, hx, rfl⟩)
      exact ht.total hc hx'
    have hac : a ≤ c := (ht.total ha hc).resolve_right hca
    have hcb : c ≤ b := (ht.total hc hb).resolve_right hbc
    rcases hab.eq_or_eq hac hcb with rfl | rfl
    · exact False.elim (hca le_rfl)
    · exact False.elim (hbc le_rfl)

/-- Maximal chains through a cover are parametrised by the two interval
maximal chains on either side of it.-/
noncomputable def throughCoverEquiv {a b : P} (hab : a ⋖ b) :
    Flag (Set.Iic a) × Flag (Set.Ici b) ≃
      {s : Flag P // a ∈ s ∧ b ∈ s} where
  toFun pair := ⟨glueCover hab pair.1 pair.2, by
    constructor
    · exact Or.inl ⟨⟨a, le_rfl⟩, Flag.top_mem pair.1, rfl⟩
    · exact Or.inr ⟨⟨b, le_rfl⟩, Flag.bot_mem pair.2, rfl⟩⟩
  invFun marked :=
    (restrictIic marked.1 a marked.2.1,
      restrictIci marked.1 b marked.2.2)
  left_inv pair := by
    apply Prod.ext
    · apply Flag.ext
      ext x
      constructor
      · intro hx
        rcases hx with ⟨y, hy, hxy⟩ | ⟨y, hy, hxy⟩
        · exact (Subtype.ext hxy) ▸ hy
        · exact False.elim ((not_le_of_gt hab.lt) (by
            calc
              b ≤ y.1 := y.2
              _ = x.1 := hxy
              _ ≤ a := x.2))
      · intro hx
        exact Or.inl ⟨x, hx, rfl⟩
    · apply Flag.ext
      ext x
      constructor
      · intro hx
        rcases hx with ⟨y, hy, hxy⟩ | ⟨y, hy, hxy⟩
        · exact False.elim ((not_le_of_gt hab.lt) (by
            calc
              b ≤ x.1 := x.2
              _ = y.1 := hxy.symm
              _ ≤ a := y.2))
        · exact (Subtype.ext hxy) ▸ hy
      · intro hx
        exact Or.inr ⟨x, hx, rfl⟩
  right_inv marked := by
    apply Subtype.ext
    apply Flag.ext
    ext c
    constructor
    · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) <;> exact hx
    · intro hc
      by_cases hca : c ≤ a
      · exact Or.inl ⟨⟨c, hca⟩, hc, rfl⟩
      by_cases hbc : b ≤ c
      · exact Or.inr ⟨⟨c, hbc⟩, hc, rfl⟩
      have hac : a ≤ c :=
        (marked.1.le_or_le marked.2.1 hc).resolve_right hca
      have hcb : c ≤ b :=
        (marked.1.le_or_le hc marked.2.2).resolve_right hbc
      rcases hab.eq_or_eq hac hcb with rfl | rfl
      · exact False.elim (hca le_rfl)
      · exact False.elim (hbc le_rfl)

end Flag
end HansenCograph
