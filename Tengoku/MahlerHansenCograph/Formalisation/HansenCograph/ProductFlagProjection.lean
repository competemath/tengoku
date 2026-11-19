/-
Copyright (c) 2026 Jeremy Parker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy P Parker
-/
import Tengoku.MahlerHansenCograph.Formalisation.HansenCograph.FlagRankedSequence
import Tengoku.Seed.Data.Finset.Max

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Projecting maximal chains in finite product orders

For nonempty finite partial orders, each coordinate projection of a maximal
chain in the product is again a maximal chain.  Restricting the original chain
to the product of those two projected flags again gives a maximal chain.
-/

open Set

namespace HansenCograph

universe u v

namespace Flag

/-- The first-coordinate projection of a maximal chain in a finite product is
again a maximal chain.-/
noncomputable def fstProjection
    {P : Type u} {Q : Type v}
    [PartialOrder P] [Finite P] [Nonempty P]
    [PartialOrder Q] [Finite Q] [Nonempty Q]
    (s : Flag (P × Q)) : Flag P := by
  classical
  letI : Fintype s := Fintype.ofFinite s
  have hsne : (s : Set (P × Q)).Nonempty :=
    s.maxChain.nonempty_iff.mp inferInstance
  letI : Nonempty s := hsne.to_subtype
  refine
    { carrier := Prod.fst '' (s : Set (P × Q))
      Chain' := ?_
      max_chain' := ?_ }
  · rintro x ⟨z, hz, rfl⟩ y ⟨w, hw, rfl⟩ _
    rcases s.chain_le.total hz hw with hzw | hwz
    · exact Or.inl hzw.1
    · exact Or.inr hwz.1
  · intro c hc hsc
    apply Set.Subset.antisymm hsc
    intro x hx
    let upper : Finset s := Finset.univ.filter fun z ↦ x ≤ z.1.1
    by_cases hu : upper.Nonempty
    · let z0 : s := upper.min' hu
      have hz0mem : z0 ∈ upper := upper.min'_mem hu
      have hxz0 : x ≤ z0.1.1 := (Finset.mem_filter.mp hz0mem).2
      have hcand : (x, z0.1.2) ∈ s := by
        apply (Flag.mem_iff_forall_le_or_ge).2
        intro z hz
        let zs : s := ⟨z, hz⟩
        rcases le_total z0 zs with hz0z | hzz0
        · left
          exact ⟨hxz0.trans hz0z.1, hz0z.2⟩
        · have hzp : z.1 ∈ c := hsc ⟨z, hz, rfl⟩
          rcases hc.total hx hzp with hxp | hpx
          · have hzupper : zs ∈ upper :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxp⟩
            have hz0z' : z0 ≤ zs := upper.min'_le zs hzupper
            left
            exact ⟨hxp, hz0z'.2⟩
          · right
            exact ⟨hpx, hzz0.2⟩
      exact ⟨(x, z0.1.2), hcand, rfl⟩
    · have huniv : (Finset.univ : Finset s).Nonempty :=
        Finset.univ_nonempty
      let z0 : s := (Finset.univ : Finset s).max' huniv
      have hcand : (x, z0.1.2) ∈ s := by
        apply (Flag.mem_iff_forall_le_or_ge).2
        intro z hz
        let zs : s := ⟨z, hz⟩
        have hzz0 : zs ≤ z0 :=
          (Finset.univ : Finset s).le_max' zs (Finset.mem_univ _)
        have hnot : ¬x ≤ z.1 := by
          intro hxz
          apply hu
          exact ⟨zs, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxz⟩⟩
        have hzp : z.1 ∈ c := hsc ⟨z, hz, rfl⟩
        have hpx : z.1 ≤ x := (hc.total hx hzp).resolve_left hnot
        right
        exact ⟨hpx, hzz0.2⟩
      exact ⟨(x, z0.1.2), hcand, rfl⟩

/--
@isnad1 id=iff.0h4v.s7.4755475b60dc from=translated src=- shape=05290d38 vocab=040bf5ab
-/
@[simp]
theorem mem_fstProjection_iff
    {P : Type u} {Q : Type v}
    [PartialOrder P] [Finite P] [Nonempty P]
    [PartialOrder Q] [Finite Q] [Nonempty Q]
    (s : Flag (P × Q)) (x : P) :
    x ∈ fstProjection s ↔ ∃ z ∈ s, z.1 = x :=
  Iff.rfl

/-- The second-coordinate projection, obtained from the first projection after
swapping the two factors.-/
noncomputable def sndProjection
    {P : Type u} {Q : Type v}
    [PartialOrder P] [Finite P] [Nonempty P]
    [PartialOrder Q] [Finite Q] [Nonempty Q]
    (s : Flag (P × Q)) : Flag Q :=
  fstProjection ((Flag.map (OrderIso.prodComm : P × Q ≃o Q × P)) s)

/--
@isnad1 id=iff.0h4v.s7.b8464cb9575b from=translated src=- shape=9dbcb605 vocab=42df5105
-/
@[simp]
theorem mem_sndProjection_iff
    {P : Type u} {Q : Type v}
    [PartialOrder P] [Finite P] [Nonempty P]
    [PartialOrder Q] [Finite Q] [Nonempty Q]
    (s : Flag (P × Q)) (y : Q) :
    y ∈ sndProjection s ↔ ∃ z ∈ s, z.2 = y := by
  constructor
  · rintro ⟨w, ⟨z, hz, hzw⟩, hwy⟩
    refine ⟨z, hz, ?_⟩
    rw [← hwy]
    exact congrArg Prod.fst hzw
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z.swap, ?_, rfl⟩
    exact ⟨z, hz, rfl⟩

/-- The original product flag, regarded as a flag in the product of its two
coordinate projections.-/
noncomputable def restrictToProjections
    {P : Type u} {Q : Type v}
    [PartialOrder P] [Finite P] [Nonempty P]
    [PartialOrder Q] [Finite Q] [Nonempty Q]
    (s : Flag (P × Q)) : Flag (fstProjection s × sndProjection s) where
  carrier := {z | (z.1.1, z.2.1) ∈ s}
  Chain' := by
    intro z hz w hw _
    rcases s.chain_le.total hz hw with hzw | hwz
    · exact Or.inl hzw
    · exact Or.inr hwz
  max_chain' := by
    intro c hc hsub
    apply Set.Subset.antisymm hsub
    intro z hz
    change (z.1.1, z.2.1) ∈ s
    apply (Flag.mem_iff_forall_le_or_ge).2
    intro a ha
    let a' : fstProjection s × sndProjection s :=
      (⟨a.1, (mem_fstProjection_iff s a.1).2 ⟨a, ha, rfl⟩⟩,
       ⟨a.2, (mem_sndProjection_iff s a.2).2 ⟨a, ha, rfl⟩⟩)
    have ha' : (a'.1.1, a'.2.1) ∈ s := by
      simpa [a'] using ha
    have hac : a' ∈ c := hsub ha'
    rcases hc.total hz hac with hza | haz
    · exact Or.inl hza
    · exact Or.inr haz

/--
@isnad1 id=iff.0h4v.s10.e8c996f8f6a2 from=translated src=- shape=326541d3 vocab=3e7c733c
-/
@[simp]
theorem mem_restrictToProjections_iff
    {P : Type u} {Q : Type v}
    [PartialOrder P] [Finite P] [Nonempty P]
    [PartialOrder Q] [Finite Q] [Nonempty Q]
    (s : Flag (P × Q)) (z : fstProjection s × sndProjection s) :
    z ∈ restrictToProjections s ↔ (z.1.1, z.2.1) ∈ s :=
  Iff.rfl

/-- Restriction to the projected factors changes only the ambient types, not
the elements of the chain.-/
noncomputable def restrictToProjectionsEquiv
    {P : Type u} {Q : Type v}
    [PartialOrder P] [Finite P] [Nonempty P]
    [PartialOrder Q] [Finite Q] [Nonempty Q]
    (s : Flag (P × Q)) : restrictToProjections s ≃ s where
  toFun z := ⟨(z.1.1.1, z.1.2.1), z.2⟩
  invFun z :=
    ⟨(⟨z.1.1, (mem_fstProjection_iff s z.1.1).2 ⟨z.1, z.2, rfl⟩⟩,
      ⟨z.1.2, (mem_sndProjection_iff s z.1.2).2 ⟨z.1, z.2, rfl⟩⟩),
     z.2⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext <;> rfl
  right_inv z := by
    apply Subtype.ext
    rfl

/--
@isnad1 id=eq.0h3v.s10.9c41d2e115d5 from=translated src=- shape=d621df72 vocab=80aeba75
-/
theorem card_restrictToProjections
    {P : Type u} {Q : Type v}
    [PartialOrder P] [Finite P] [Nonempty P]
    [PartialOrder Q] [Finite Q] [Nonempty Q]
    (s : Flag (P × Q)) :
    Nat.card (restrictToProjections s) = Nat.card s :=
  Nat.card_congr (restrictToProjectionsEquiv s)

end Flag

end HansenCograph
