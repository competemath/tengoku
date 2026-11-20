/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.ADEBlockCoordinates

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

/--
@isnad1 id=ex.1h2v.s6.1af0b0bc9a3c from=translated src=- shape=aa9cae57 vocab=1926b955
-/
theorem exists_adeBlock_equiv_of_perm {ts us : List ADEType} (p : ts.Perm us) :
    ∃ e : ADEBlockIndex ts ≃ ADEBlockIndex us,
      ∀ i j, adeBlockPairing ts i j = adeBlockPairing us (e i) (e j) := by
  induction p with
  | nil => exact ⟨Equiv.refl _, fun _ _ => rfl⟩
  | cons t _ ih =>
      obtain ⟨e, he⟩ := ih
      refine ⟨Equiv.sumCongr (Equiv.refl (Fin t.rank)) e, ?_⟩
      intro i j
      cases i with
      | inl i => cases j <;> rfl
      | inr i =>
          cases j with
          | inl j => rfl
          | inr j => exact he i j
  | swap t u ts =>
      let e : Fin u.rank ⊕ (Fin t.rank ⊕ ADEBlockIndex ts) ≃
          Fin t.rank ⊕ (Fin u.rank ⊕ ADEBlockIndex ts) :=
        (Equiv.sumAssoc _ _ _).symm |>.trans
          ((Equiv.sumCongr (Equiv.sumComm _ _) (Equiv.refl _)).trans
            (Equiv.sumAssoc _ _ _))
      refine ⟨e, ?_⟩
      intro i j
      rcases i with i | i | i <;> rcases j with j | j | j <;> rfl
  | trans _ _ ih₁ ih₂ =>
      obtain ⟨e, he⟩ := ih₁
      obtain ⟨f, hf⟩ := ih₂
      exact ⟨e.trans f, fun i j => (he i j).trans (hf (e i) (e j))⟩

end SRG266.Lattice
