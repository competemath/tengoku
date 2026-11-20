/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.ADEConnectedClassification
import Tengoku.Seed.Logic.Equiv.Fin.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266
namespace Lattice

def ADEBlockIndex : List ADEType → Type
  | [] => Empty
  | t :: ts => Fin t.rank ⊕ ADEBlockIndex ts

instance adeBlockIndexFintype : (ts : List ADEType) → Fintype (ADEBlockIndex ts)
  | [] => Fintype.ofEquiv Empty (Equiv.refl Empty)
  | _ :: ts => by
      let := adeBlockIndexFintype ts
      exact inferInstanceAs (Fintype (_ ⊕ ADEBlockIndex ts))

instance adeBlockIndexDecidableEq : (ts : List ADEType) → DecidableEq (ADEBlockIndex ts)
  | [] => inferInstanceAs (DecidableEq Empty)
  | _ :: ts => by
      let := adeBlockIndexDecidableEq ts
      exact inferInstanceAs (DecidableEq (_ ⊕ ADEBlockIndex ts))

def finADEBlockEquiv : (ts : List ADEType) →
    Fin (ADEType.rankSum ts) ≃ ADEBlockIndex ts
  | [] => Equiv.equivEmpty (Fin 0)
  | t :: ts => finSumFinEquiv.symm |>.trans
      (Equiv.sumCongr (Equiv.refl (Fin t.rank)) (finADEBlockEquiv ts))

def adeBlockPairing : (ts : List ADEType) → ADEBlockIndex ts → ADEBlockIndex ts → ℤ
  | [], i, _ => nomatch i
  | t :: _, Sum.inl i, Sum.inl j => t.gram i j
  | _ :: ts, Sum.inr i, Sum.inr j => adeBlockPairing ts i j
  | _ :: _, _, _ => 0

@[simp]
theorem finADEBlockEquiv_cons_castAdd
    (t : ADEType) (ts : List ADEType) (i : Fin t.rank) :
    finADEBlockEquiv (t :: ts) (Fin.castAdd (ADEType.rankSum ts) i) = Sum.inl i := by
  change (finSumFinEquiv.symm.trans
    (Equiv.sumCongr (Equiv.refl (Fin t.rank)) (finADEBlockEquiv ts)))
      (Fin.castAdd (ADEType.rankSum ts) i) = Sum.inl i
  simp

@[simp]
theorem finADEBlockEquiv_cons_natAdd
    (t : ADEType) (ts : List ADEType) (i : Fin (ADEType.rankSum ts)) :
    finADEBlockEquiv (t :: ts) (Fin.natAdd t.rank i) =
      Sum.inr (finADEBlockEquiv ts i) := by
  change (finSumFinEquiv.symm.trans
    (Equiv.sumCongr (Equiv.refl (Fin t.rank)) (finADEBlockEquiv ts)))
      (Fin.natAdd t.rank i) = Sum.inr (finADEBlockEquiv ts i)
  simp

theorem adeEntry_eq_adeBlockPairing : ∀ (ts : List ADEType)
    (i j : Fin (ADEType.rankSum ts)),
    adeEntry ts i.1 j.1 =
      adeBlockPairing ts (finADEBlockEquiv ts i) (finADEBlockEquiv ts j)
  | [], i, _ => Fin.elim0 i
  | t :: ts, i, j => by
      change Fin (t.rank + ADEType.rankSum ts) at i j
      generalize hi : finSumFinEquiv.symm i = ei
      generalize hj : finSumFinEquiv.symm j = ej
      cases ei with
      | inl i0 =>
          cases ej with
          | inl j0 =>
              have hi' : i = Fin.castAdd (ADEType.rankSum ts) i0 := by
                rw [← finSumFinEquiv.apply_symm_apply i, hi]
                rfl
              have hj' : j = Fin.castAdd (ADEType.rankSum ts) j0 := by
                rw [← finSumFinEquiv.apply_symm_apply j, hj]
                rfl
              subst i
              subst j
              rw [finADEBlockEquiv_cons_castAdd, finADEBlockEquiv_cons_castAdd]
              simp [adeEntry, adeBlockPairing, ADEType.gram]
          | inr j0 =>
              have hi' : i = Fin.castAdd (ADEType.rankSum ts) i0 := by
                rw [← finSumFinEquiv.apply_symm_apply i, hi]
                rfl
              have hj' : j = Fin.natAdd t.rank j0 := by
                rw [← finSumFinEquiv.apply_symm_apply j, hj]
                rfl
              subst i
              subst j
              have hbi : finADEBlockEquiv (t :: ts)
                  (Fin.castAdd (ADEType.rankSum ts) i0) = Sum.inl i0 := by
                exact finADEBlockEquiv_cons_castAdd t ts i0
              have hbj : finADEBlockEquiv (t :: ts) (Fin.natAdd t.rank j0) =
                  Sum.inr (finADEBlockEquiv ts j0) := by
                change (Equiv.sumCongr (Equiv.refl (Fin t.rank)) (finADEBlockEquiv ts))
                    (finSumFinEquiv.symm (Fin.natAdd t.rank j0)) = _
                rw [hj]
                rfl
              calc
                adeEntry (t :: ts) _ _ = 0 := by simp [adeEntry, i0.isLt]
                _ = adeBlockPairing (t :: ts)
                    (finADEBlockEquiv (t :: ts) (Fin.castAdd (ADEType.rankSum ts) i0))
                    (finADEBlockEquiv (t :: ts) (Fin.natAdd t.rank j0)) := by
                  rw [hbi, hbj]
                  rfl
      | inr i0 =>
          cases ej with
          | inl j0 =>
              have hi' : i = Fin.natAdd t.rank i0 := by
                rw [← finSumFinEquiv.apply_symm_apply i, hi]
                rfl
              have hj' : j = Fin.castAdd (ADEType.rankSum ts) j0 := by
                rw [← finSumFinEquiv.apply_symm_apply j, hj]
                rfl
              subst i
              subst j
              have hbi : finADEBlockEquiv (t :: ts) (Fin.natAdd t.rank i0) =
                  Sum.inr (finADEBlockEquiv ts i0) := by
                change (Equiv.sumCongr (Equiv.refl (Fin t.rank)) (finADEBlockEquiv ts))
                    (finSumFinEquiv.symm (Fin.natAdd t.rank i0)) = _
                rw [hi]
                rfl
              have hbj : finADEBlockEquiv (t :: ts)
                  (Fin.castAdd (ADEType.rankSum ts) j0) = Sum.inl j0 := by
                exact finADEBlockEquiv_cons_castAdd t ts j0
              calc
                adeEntry (t :: ts) _ _ = 0 := by simp [adeEntry, j0.isLt]
                _ = adeBlockPairing (t :: ts)
                    (finADEBlockEquiv (t :: ts) (Fin.natAdd t.rank i0))
                    (finADEBlockEquiv (t :: ts) (Fin.castAdd (ADEType.rankSum ts) j0)) := by
                  rw [hbi, hbj]
                  rfl
          | inr j0 =>
              have hi' : i = Fin.natAdd t.rank i0 := by
                rw [← finSumFinEquiv.apply_symm_apply i, hi]
                rfl
              have hj' : j = Fin.natAdd t.rank j0 := by
                rw [← finSumFinEquiv.apply_symm_apply j, hj]
                rfl
              subst i
              subst j
              have hbi : finADEBlockEquiv (t :: ts) (Fin.natAdd t.rank i0) =
                  Sum.inr (finADEBlockEquiv ts i0) := by
                change (Equiv.sumCongr (Equiv.refl (Fin t.rank)) (finADEBlockEquiv ts))
                    (finSumFinEquiv.symm (Fin.natAdd t.rank i0)) = _
                rw [hi]
                rfl
              have hbj : finADEBlockEquiv (t :: ts) (Fin.natAdd t.rank j0) =
                  Sum.inr (finADEBlockEquiv ts j0) := by
                change (Equiv.sumCongr (Equiv.refl (Fin t.rank)) (finADEBlockEquiv ts))
                    (finSumFinEquiv.symm (Fin.natAdd t.rank j0)) = _
                rw [hj]
                rfl
              calc
                adeEntry (t :: ts) _ _ = adeEntry ts i0.1 j0.1 := by simp [adeEntry]
                _ = adeBlockPairing ts (finADEBlockEquiv ts i0)
                    (finADEBlockEquiv ts j0) := adeEntry_eq_adeBlockPairing ts i0 j0
                _ = adeBlockPairing (t :: ts)
                    (finADEBlockEquiv (t :: ts) (Fin.natAdd t.rank i0))
                    (finADEBlockEquiv (t :: ts) (Fin.natAdd t.rank j0)) := by
                  rw [hbi, hbj]
                  rfl

theorem adeGram_apply_eq_adeBlockPairing (ts : List ADEType)
    (i j : Fin (ADEType.rankSum ts)) :
    (adeGram ts).2 i j =
      adeBlockPairing ts (finADEBlockEquiv ts i) (finADEBlockEquiv ts j) :=
  adeEntry_eq_adeBlockPairing ts i j

end Lattice
end SRG266
