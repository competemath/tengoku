/-
Copyright (c) 2026 Jeremy Parker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy P Parker
-/
import Tengoku.MahlerHansenCograph.Formalisation.HansenCograph.FlagRankedSequence
import Tengoku.Seed.Data.Fintype.Order
import Lean.Elab.Tactic.Omega

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Cardinality of maximal chains in products of finite linear orders

A maximal chain in a product of two finite nonempty linear orders makes exactly
one cover step in one coordinate at a time.  Hence all such chains have the
same cardinality, independently of any ambient grading infrastructure.
-/

namespace HansenCograph

universe u v

namespace Flag

/-- A maximal chain in the product of two nonempty finite linear orders has
the sum of the two factor lengths, with the common endpoint counted once.
@isnad1 id=eq.2h5v.s7.508d934743e2 from=translated src=- shape=3eb76e85 vocab=585fe27f
-/
theorem prod_card_eq_of_card
    {P : Type u} {Q : Type v}
    [LinearOrder P] [Finite P] [Nonempty P]
    [LinearOrder Q] [Finite Q] [Nonempty Q]
    (s : Flag (P × Q)) {n m : ℕ}
    (hP : Nat.card P = n + 1) (hQ : Nat.card Q = m + 1) :
    Nat.card s = n + m + 1 := by
  classical
  let _ : Fintype P := Fintype.ofFinite P
  let _ : Fintype Q := Fintype.ofFinite Q
  let _ : BoundedOrder P := Fintype.toBoundedOrder P
  let _ : BoundedOrder Q := Fintype.toBoundedOrder Q
  let _ : Fintype s := Fintype.ofFinite s
  let _ : Nonempty s := ⟨⟨⊥, Flag.bot_mem s⟩⟩
  let t := Nat.card s - 1
  have hspos : 0 < Nat.card s := Nat.card_pos
  have hs : Nat.card s = t + 1 := by
    dsimp [t]
    omega
  have hs' : Fintype.card s = t + 1 := by
    simpa only [Nat.card_eq_fintype_card] using hs
  have hP' : Fintype.card P = n + 1 := by
    simpa only [Nat.card_eq_fintype_card] using hP
  have hQ' : Fintype.card Q = m + 1 := by
    simpa only [Nat.card_eq_fintype_card] using hQ
  let e : Fin (t + 1) ≃o s := Fintype.orderIsoFinOfCardEq s hs'
  let eP : Fin (n + 1) ≃o P := Fintype.orderIsoFinOfCardEq P hP'
  let eQ : Fin (m + 1) ≃o Q := Fintype.orderIsoFinOfCardEq Q hQ'
  let rank : Fin (t + 1) → ℕ := fun k ↦
    (eP.symm (e k).1.1).1 + (eQ.symm (e k).1.2).1
  have rank_zero : rank 0 = 0 := by
    have he0 : (e (0 : Fin (t + 1))).1 = (⊥ : P × Q) :=
      congrArg Subtype.val e.map_bot
    have hP0 : eP.symm (⊥ : P) = (0 : Fin (n + 1)) := eP.symm.map_bot
    have hQ0 : eQ.symm (⊥ : Q) = (0 : Fin (m + 1)) := eQ.symm.map_bot
    rw [show rank 0 =
      (eP.symm (e 0).1.1).1 + (eQ.symm (e 0).1.2).1 by rfl,
      he0]
    change (eP.symm (⊥ : P)).1 + (eQ.symm (⊥ : Q)).1 = 0
    rw [hP0, hQ0]
    rfl
  have rank_succ (k : Fin t) :
      rank k.succ = rank k.castSucc + 1 := by
    have hkFin : (k.castSucc : Fin (t + 1)) ⋖ k.succ := by
      rw [Fin.covBy_iff, Nat.covBy_iff_add_one_eq]
      rfl
    have hkSub : e k.castSucc ⋖ e k.succ :=
      (apply_covBy_apply_iff e).mpr hkFin
    have hk : (e k.castSucc).1 ⋖ (e k.succ).1 :=
      Flag.coe_covBy_coe.mpr hkSub
    rcases Prod.covBy_iff.mp hk with hkP | hkQ
    · have hcov : eP.symm (e k.castSucc).1.1 ⋖
          eP.symm (e k.succ).1.1 :=
        (apply_covBy_apply_iff eP.symm).mpr hkP.1
      have hstep := Nat.covBy_iff_add_one_eq.mp (Fin.covBy_iff.mp hcov)
      have heq := congrArg (fun q ↦ (eQ.symm q).1) hkP.2
      dsimp [rank]
      omega
    · have hcov : eQ.symm (e k.castSucc).1.2 ⋖
          eQ.symm (e k.succ).1.2 :=
        (apply_covBy_apply_iff eQ.symm).mpr hkQ.1
      have hstep := Nat.covBy_iff_add_one_eq.mp (Fin.covBy_iff.mp hcov)
      have heq := congrArg (fun p ↦ (eP.symm p).1) hkQ.2
      dsimp [rank]
      omega
  have rank_eq_val (k : Fin (t + 1)) : rank k = k.1 := by
    induction k using Fin.induction with
    | zero => exact rank_zero
    | succ k ih =>
        rw [rank_succ k, ih]
        rfl
  have rank_last : rank (Fin.last t) = n + m := by
    have helast : (e (Fin.last t)).1 = (⊤ : P × Q) :=
      congrArg Subtype.val e.map_top
    have hPtop : eP.symm (⊤ : P) = Fin.last n := eP.symm.map_top
    have hQtop : eQ.symm (⊤ : Q) = Fin.last m := eQ.symm.map_top
    rw [show rank (Fin.last t) =
      (eP.symm (e (Fin.last t)).1.1).1 +
        (eQ.symm (e (Fin.last t)).1.2).1 by rfl,
      helast]
    change (eP.symm (⊤ : P)).1 + (eQ.symm (⊤ : Q)).1 = n + m
    rw [hPtop, hQtop]
    rfl
  have ht : t = n + m := by
    have h := rank_eq_val (Fin.last t)
    rw [rank_last] at h
    simpa using h.symm
  omega

/-- Cardinality-only form of `Flag.prod_card_eq_of_card`.
@isnad1 id=eq.0h3v.s7.85ef03fd744a from=translated src=- shape=35c9caff vocab=74796bd9
-/
theorem prod_card_eq
    {P : Type u} {Q : Type v}
    [LinearOrder P] [Finite P] [Nonempty P]
    [LinearOrder Q] [Finite Q] [Nonempty Q]
    (s : Flag (P × Q)) :
    Nat.card s = Nat.card P + Nat.card Q - 1 := by
  have hPpos : 0 < Nat.card P := Nat.card_pos
  have hQpos : 0 < Nat.card Q := Nat.card_pos
  have h := prod_card_eq_of_card s
    (n := Nat.card P - 1) (m := Nat.card Q - 1)
    (by omega) (by omega)
  omega

end Flag

end HansenCograph
