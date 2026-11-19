/-
Copyright (c) 2026 Jeremy Parker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy P Parker
-/
import Tengoku.MahlerHansenCograph.Formalisation.HansenCograph.FlagProductShuffle

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Product shuffles for arbitrary finite partial orders

The bounded-order version is convenient for graded flags, but rooted upper
strata have no global top.  This file constructs the shuffle flag directly
from two arbitrary finite maximal chains, using a finite grid as the
maximality certificate.
-/

open Set

namespace HansenCograph

universe u v

def finRankedFlag (n : ℕ) : RankedFlag (Fin (n + 1)) n where
  toFun k := k
  map_zero := rfl
  map_last := rfl
  covBy_succ k := by
    rw [Fin.covBy_iff, Nat.covBy_iff_add_one_eq]
    rfl

noncomputable def Flag.productShuffle
    {P : Type u} {Q : Type v}
    [PartialOrder P] [Finite P]
    [PartialOrder Q] [Finite Q]
    (f : Flag P) (g : Flag Q)
    {n m : ℕ} (hf : Nat.card f = n + 1) (hg : Nat.card g = m + 1)
    (s : ShufflePath n m) : Flag (P × Q) := by
  classical
  letI : Fintype f := Fintype.ofFinite f
  letI : Fintype g := Fintype.ofFinite g
  have hf' : Fintype.card f = n + 1 := by
    simpa only [Nat.card_eq_fintype_card] using hf
  have hg' : Fintype.card g = m + 1 := by
    simpa only [Nat.card_eq_fintype_card] using hg
  let ef : Fin (n + 1) ≃o f := Fintype.orderIsoFinOfCardEq f hf'
  let eg : Fin (m + 1) ≃o g := Fintype.orderIsoFinOfCardEq g hg'
  let hfun : Fin (n + m + 1) → P × Q :=
    fun k ↦ ((ef (s.left k)).1, (eg (s.right k)).1)
  have hleft_succ (k : Fin (n + m)) :
      s.left k.castSucc ≤ s.left k.succ := by
    rcases s.step k with hstep | hstep
    · exact hstep.1.le
    · exact hstep.2.le
  have hright_succ (k : Fin (n + m)) :
      s.right k.castSucc ≤ s.right k.succ := by
    rcases s.step k with hstep | hstep
    · exact hstep.2.le
    · exact hstep.1.le
  have hleft_mono : Monotone s.left :=
    Fin.monotone_iff_le_succ.mpr hleft_succ
  have hright_mono : Monotone s.right :=
    Fin.monotone_iff_le_succ.mpr hright_succ
  let grid : Flag (Fin (n + 1) × Fin (m + 1)) :=
    (RankedFlag.prodOfShuffle (finRankedFlag n) (finRankedFlag m) s).toFlag
  refine {
    carrier := Set.range hfun
    Chain' := by
      intro x hx y hy hxy
      rcases hx with ⟨i, rfl⟩
      rcases hy with ⟨j, rfl⟩
      rcases le_total i j with hij | hji
      · exact Or.inl ⟨ef.monotone (hleft_mono hij),
          eg.monotone (hright_mono hij)⟩
      · exact Or.inr ⟨ef.monotone (hleft_mono hji),
          eg.monotone (hright_mono hji)⟩
    max_chain' := by
      intro t ht hsub
      apply Set.Subset.antisymm hsub
      intro z hz
      have hxmem : z.1 ∈ f := by
        apply (Flag.mem_iff_forall_le_or_ge).2
        intro c hc
        obtain ⟨i, hi⟩ := ef.surjective ⟨c, hc⟩
        obtain ⟨k, hk⟩ := s.left_surjective i
        have hpath : hfun k ∈ t := hsub ⟨k, rfl⟩
        have hval : (hfun k).1 = c := by
          have hi' : (ef i).1 = c := congrArg Subtype.val hi
          simpa [hfun, hk] using hi'
        by_cases heq : z = hfun k
        · exact Or.inl (by simpa [heq, hval])
        · rcases ht hz hpath heq with hle | hge
          · exact Or.inl (by simpa [hval] using hle.1)
          · exact Or.inr (by simpa [hval] using hge.1)
      have hymem : z.2 ∈ g := by
        apply (Flag.mem_iff_forall_le_or_ge).2
        intro c hc
        obtain ⟨j, hj⟩ := eg.surjective ⟨c, hc⟩
        obtain ⟨k, hk⟩ := s.right_surjective j
        have hpath : hfun k ∈ t := hsub ⟨k, rfl⟩
        have hval : (hfun k).2 = c := by
          have hj' : (eg j).1 = c := congrArg Subtype.val hj
          simpa [hfun, hk] using hj'
        by_cases heq : z = hfun k
        · exact Or.inl (by simpa [heq, hval])
        · rcases ht hz hpath heq with hle | hge
          · exact Or.inl (by simpa [hval] using hle.2)
          · exact Or.inr (by simpa [hval] using hge.2)
      obtain ⟨i, hi⟩ := ef.surjective ⟨z.1, hxmem⟩
      obtain ⟨j, hj⟩ := eg.surjective ⟨z.2, hymem⟩
      have hgrid : (i, j) ∈ grid := by
        apply (Flag.mem_iff_forall_le_or_ge).2
        intro q hq
        change q ∈ (RankedFlag.prodOfShuffle (finRankedFlag n)
          (finRankedFlag m) s).toFlag at hq
        obtain ⟨k, hk⟩ :=
          (RankedFlag.prodOfShuffle (finRankedFlag n)
            (finRankedFlag m) s).mem_toFlag_iff q |>.mp hq
        rw [← hk]
        have hpath : hfun k ∈ t := hsub ⟨k, rfl⟩
        by_cases heq : z = hfun k
        · have hki : s.left k = i := by
            apply ef.injective
            apply Subtype.ext
            simpa [hfun] using (congrArg Prod.fst heq).symm.trans
              (congrArg Subtype.val hi).symm
          have hkj : s.right k = j := by
            apply eg.injective
            apply Subtype.ext
            simpa [hfun] using (congrArg Prod.snd heq).symm.trans
              (congrArg Subtype.val hj).symm
          subst z
          subst i
          subst j
          exact Or.inl ⟨le_rfl, le_rfl⟩
        · rcases ht hz hpath heq with hle | hge
          · left
            change i ≤ s.left k ∧ j ≤ s.right k
            constructor
            · apply (ef.le_iff_le).mp
              change (ef i).1 ≤ (ef (s.left k)).1
              simpa [hfun, hi] using hle.1
            · apply (eg.le_iff_le).mp
              change (eg j).1 ≤ (eg (s.right k)).1
              simpa [hfun, hj] using hle.2
          · right
            change s.left k ≤ i ∧ s.right k ≤ j
            constructor
            · apply (ef.le_iff_le).mp
              change (ef (s.left k)).1 ≤ (ef i).1
              simpa [hfun, hi] using hge.1
            · apply (eg.le_iff_le).mp
              change (eg (s.right k)).1 ≤ (eg j).1
              simpa [hfun, hj] using hge.2
      change (i, j) ∈ (RankedFlag.prodOfShuffle (finRankedFlag n)
        (finRankedFlag m) s).toFlag at hgrid
      obtain ⟨k, hk⟩ :=
        (RankedFlag.prodOfShuffle (finRankedFlag n)
          (finRankedFlag m) s).mem_toFlag_iff (i, j) |>.mp hgrid
      refine ⟨k, ?_⟩
      apply Prod.ext
      · have hki := congrArg Prod.fst hk
        have hki' : s.left k = i := by
          simpa [RankedFlag.prodOfShuffle, finRankedFlag] using hki
        calc
          (hfun k).1 = (ef (s.left k)).1 := rfl
          _ = (ef i).1 := by rw [hki']
          _ = z.1 := congrArg Subtype.val hi
      · have hkj := congrArg Prod.snd hk
        have hkj' : s.right k = j := by
          simpa [RankedFlag.prodOfShuffle, finRankedFlag] using hkj
        calc
          (hfun k).2 = (eg (s.right k)).1 := rfl
          _ = (eg j).1 := by rw [hkj']
          _ = z.2 := congrArg Subtype.val hj
  }

/--
@isnad1 id=eq.2h7v.s7.f98655e74186 from=translated src=- shape=6057304c vocab=5c15d2a2
-/
theorem Flag.productShuffle_fst_range
    {P : Type u} {Q : Type v}
    [PartialOrder P] [Finite P]
    [PartialOrder Q] [Finite Q]
    (f : Flag P) (g : Flag Q)
    {n m : ℕ} (hf : Nat.card f = n + 1) (hg : Nat.card g = m + 1)
    (s : ShufflePath n m) :
    Prod.fst '' (Flag.productShuffle f g hf hg s).carrier = f := by
  classical
  letI : Fintype f := Fintype.ofFinite f
  letI : Fintype g := Fintype.ofFinite g
  have hf' : Fintype.card f = n + 1 := by
    simpa only [Nat.card_eq_fintype_card] using hf
  have hg' : Fintype.card g = m + 1 := by
    simpa only [Nat.card_eq_fintype_card] using hg
  let ef : Fin (n + 1) ≃o f := Fintype.orderIsoFinOfCardEq f hf'
  let eg : Fin (m + 1) ≃o g := Fintype.orderIsoFinOfCardEq g hg'
  change Prod.fst '' Set.range (fun k : Fin (n + m + 1) ↦
      ((ef (s.left k)).1, (eg (s.right k)).1)) = (f : Set P)
  ext x
  constructor
  · rintro ⟨z, ⟨k, rfl⟩, rfl⟩
    exact (ef (s.left k)).2
  · intro hx
    obtain ⟨i, hi⟩ := ef.surjective ⟨x, hx⟩
    obtain ⟨k, hk⟩ := s.left_surjective i
    refine ⟨((ef (s.left k)).1, (eg (s.right k)).1), ⟨k, rfl⟩, ?_⟩
    simpa [hk] using congrArg Subtype.val hi

/--
@isnad1 id=eq.2h7v.s7.faba1b0fb4ab from=translated src=- shape=7e5bd8fa vocab=177d4194
-/
theorem Flag.productShuffle_snd_range
    {P : Type u} {Q : Type v}
    [PartialOrder P] [Finite P]
    [PartialOrder Q] [Finite Q]
    (f : Flag P) (g : Flag Q)
    {n m : ℕ} (hf : Nat.card f = n + 1) (hg : Nat.card g = m + 1)
    (s : ShufflePath n m) :
    Prod.snd '' (Flag.productShuffle f g hf hg s).carrier = g := by
  classical
  letI : Fintype f := Fintype.ofFinite f
  letI : Fintype g := Fintype.ofFinite g
  have hf' : Fintype.card f = n + 1 := by
    simpa only [Nat.card_eq_fintype_card] using hf
  have hg' : Fintype.card g = m + 1 := by
    simpa only [Nat.card_eq_fintype_card] using hg
  let ef : Fin (n + 1) ≃o f := Fintype.orderIsoFinOfCardEq f hf'
  let eg : Fin (m + 1) ≃o g := Fintype.orderIsoFinOfCardEq g hg'
  change Prod.snd '' Set.range (fun k : Fin (n + m + 1) ↦
      ((ef (s.left k)).1, (eg (s.right k)).1)) = (g : Set Q)
  ext y
  constructor
  · rintro ⟨z, ⟨k, rfl⟩, rfl⟩
    exact (eg (s.right k)).2
  · intro hy
    obtain ⟨j, hj⟩ := eg.surjective ⟨y, hy⟩
    obtain ⟨k, hk⟩ := s.right_surjective j
    refine ⟨((ef (s.left k)).1, (eg (s.right k)).1), ⟨k, rfl⟩, ?_⟩
    simpa [hk] using congrArg Subtype.val hj

/--
@isnad1 id=injectiv.2h6v.s7.edcf25bcae5d from=translated src=- shape=a4110810 vocab=a913f091
-/
theorem Flag.productShuffle_injective_fixed
    {P : Type u} {Q : Type v}
    [PartialOrder P] [Finite P]
    [PartialOrder Q] [Finite Q]
    (f : Flag P) (g : Flag Q)
    {n m : ℕ} (hf : Nat.card f = n + 1) (hg : Nat.card g = m + 1) :
    Function.Injective (fun s : ShufflePath n m ↦
      Flag.productShuffle f g hf hg s) := by
  classical
  letI : Fintype f := Fintype.ofFinite f
  letI : Fintype g := Fintype.ofFinite g
  have hf' : Fintype.card f = n + 1 := by
    simpa only [Nat.card_eq_fintype_card] using hf
  have hg' : Fintype.card g = m + 1 := by
    simpa only [Nat.card_eq_fintype_card] using hg
  let ef : Fin (n + 1) ≃o f := Fintype.orderIsoFinOfCardEq f hf'
  let eg : Fin (m + 1) ≃o g := Fintype.orderIsoFinOfCardEq g hg'
  intro s t hst
  have hgrid :
      (RankedFlag.prodOfShuffle (finRankedFlag n) (finRankedFlag m) s).toFlag =
        (RankedFlag.prodOfShuffle (finRankedFlag n) (finRankedFlag m) t).toFlag := by
    apply Flag.ext
    ext q
    constructor
    · intro hq
      obtain ⟨k, hk⟩ :=
        (RankedFlag.prodOfShuffle (finRankedFlag n)
          (finRankedFlag m) s).mem_toFlag_iff q |>.mp hq
      have hz_s :
          ((ef q.1).1, (eg q.2).1) ∈
            Flag.productShuffle f g hf hg s := by
        change ((ef q.1).1, (eg q.2).1) ∈
          Set.range (fun j : Fin (n + m + 1) ↦
            ((ef (s.left j)).1, (eg (s.right j)).1))
        refine ⟨k, ?_⟩
        apply Prod.ext
        · simpa [RankedFlag.prodOfShuffle, finRankedFlag] using
            congrArg Prod.fst hk
        · simpa [RankedFlag.prodOfShuffle, finRankedFlag] using
            congrArg Prod.snd hk
      have hz :
          ((ef q.1).1, (eg q.2).1) ∈
            Flag.productShuffle f g hf hg t :=
        (congrArg (fun z : Flag (P × Q) ↦
          ((ef q.1).1, (eg q.2).1) ∈ z) hst).mp hz_s
      change ((ef q.1).1, (eg q.2).1) ∈
        Set.range (fun j : Fin (n + m + 1) ↦
          ((ef (t.left j)).1, (eg (t.right j)).1)) at hz
      obtain ⟨j, hj⟩ := hz
      refine ((RankedFlag.prodOfShuffle (finRankedFlag n)
        (finRankedFlag m) t).mem_toFlag_iff q).2 ⟨j, ?_⟩
      apply Prod.ext
      · have hj' := congrArg Prod.fst hj
        apply Fin.ext
        exact congrArg Fin.val (ef.injective (Subtype.ext hj'))
      · have hj' := congrArg Prod.snd hj
        apply Fin.ext
        exact congrArg Fin.val (eg.injective (Subtype.ext hj'))
    · intro hq
      obtain ⟨k, hk⟩ :=
        (RankedFlag.prodOfShuffle (finRankedFlag n)
          (finRankedFlag m) t).mem_toFlag_iff q |>.mp hq
      have hz_t :
          ((ef q.1).1, (eg q.2).1) ∈
            Flag.productShuffle f g hf hg t := by
        change ((ef q.1).1, (eg q.2).1) ∈
          Set.range (fun j : Fin (n + m + 1) ↦
            ((ef (t.left j)).1, (eg (t.right j)).1))
        refine ⟨k, ?_⟩
        apply Prod.ext
        · simpa [RankedFlag.prodOfShuffle, finRankedFlag] using
            congrArg Prod.fst hk
        · simpa [RankedFlag.prodOfShuffle, finRankedFlag] using
            congrArg Prod.snd hk
      have hz :
          ((ef q.1).1, (eg q.2).1) ∈
            Flag.productShuffle f g hf hg s :=
        (congrArg (fun z : Flag (P × Q) ↦
          ((ef q.1).1, (eg q.2).1) ∈ z) hst).mpr hz_t
      change ((ef q.1).1, (eg q.2).1) ∈
        Set.range (fun j : Fin (n + m + 1) ↦
          ((ef (s.left j)).1, (eg (s.right j)).1)) at hz
      obtain ⟨j, hj⟩ := hz
      refine ((RankedFlag.prodOfShuffle (finRankedFlag n)
        (finRankedFlag m) s).mem_toFlag_iff q).2 ⟨j, ?_⟩
      apply Prod.ext
      · have hj' := congrArg Prod.fst hj
        apply Fin.ext
        exact congrArg Fin.val (ef.injective (Subtype.ext hj'))
      · have hj' := congrArg Prod.snd hj
        apply Fin.ext
        exact congrArg Fin.val (eg.injective (Subtype.ext hj'))
  have hranked := RankedFlag.toFlag_injective hgrid
  have hranked' :
      (fun x : RankedFlag (Fin (n + 1)) n × RankedFlag (Fin (m + 1)) m ×
        ShufflePath n m ↦
        RankedFlag.prodOfShuffle x.1 x.2.1 x.2.2)
        (finRankedFlag n, finRankedFlag m, s) =
      (fun x : RankedFlag (Fin (n + 1)) n × RankedFlag (Fin (m + 1)) m ×
        ShufflePath n m ↦
        RankedFlag.prodOfShuffle x.1 x.2.1 x.2.2)
        (finRankedFlag n, finRankedFlag m, t) := hranked
  have hcode := RankedFlag.prodOfShuffle_injective hranked'
  exact congrArg (fun x : RankedFlag (Fin (n + 1)) n ×
      RankedFlag (Fin (m + 1)) m × ShufflePath n m ↦ x.2.2) hcode

end HansenCograph
