import Tengoku.Rank3kum.Rank3KUM.TwoGap.Final
import Tengoku.Seed.Combinatorics.Matroid.Minor.Delete
import Tengoku.Seed.Logic.Equiv.Set
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Rank3KUM

open Set

noncomputable section

variable {α : Type*}

/-- Add a natural offset to a finite cyclic index.-/
def cyclicIndex (n : ℕ) (hn : 0 < n) (i : Fin n) (j : ℕ) : Fin n :=
  ⟨(i.val + j) % n, Nat.mod_lt _ hn⟩

/--
@isnad1 id=eq.1h3v.s5.6055e807e036 from=translated src=- shape=bf4d4cbe vocab=e01ce091
-/
@[simp] theorem cyclicIndex_val
    (n : ℕ) (hn : 0 < n) (i : Fin n) (j : ℕ) :
    (cyclicIndex n hn i j).val = (i.val + j) % n := by
  rfl

/--
@isnad1 id=eq.1h2v.s4.f5489435c442 from=translated src=- shape=3e166a12 vocab=1490af81
-/
@[simp] theorem cyclicIndex_zero
    (n : ℕ) (hn : 0 < n) (i : Fin n) :
    cyclicIndex n hn i 0 = i := by
  apply Fin.ext
  simp [cyclicIndex, Nat.mod_eq_of_lt i.isLt]

/-- A cyclic enumeration whose every three consecutive elements form a basis.-/
def CyclicBasisOrder3
    (M : Matroid α) {E : Set α} {n : ℕ}
    (hn : 0 < n) (σ : Fin n ≃ E) : Prop :=
  ∀ i : Fin n,
    M.IsBase
      ({(σ i : α),
        (σ (cyclicIndex n hn i 1) : α),
        (σ (cyclicIndex n hn i 2) : α)} : Set α)

/-- Append a disjoint three-element block after an enumeration.-/
def appendBlockOrder
    {E D : Set α} {m : ℕ}
    (hED : Disjoint E D)
    (small : Fin m ≃ E)
    (block : Fin 3 ≃ D) :
    Fin (m + 3) ≃ (E ∪ D : Set α) := by
  classical
  exact finSumFinEquiv.symm.trans
    ((Equiv.sumCongr small block).trans
      (Equiv.Set.union hED).symm)

/--
@isnad1 id=eq.1h7v.s8.945aa16aed98 from=translated src=- shape=b2954166 vocab=225fe39e
-/
@[simp] theorem appendBlockOrder_old
    {E D : Set α} {m : ℕ}
    (hED : Disjoint E D)
    (small : Fin m ≃ E)
    (block : Fin 3 ≃ D)
    (i : Fin m) :
    ((appendBlockOrder hED small block (Fin.castAdd 3 i) :
        (E ∪ D : Set α)) : α) =
      (small i : α) := by
  classical
  simp [appendBlockOrder]

/--
@isnad1 id=eq.1h7v.s8.465337203435 from=translated src=- shape=3adeeecd vocab=528b1538
-/
@[simp] theorem appendBlockOrder_block
    {E D : Set α} {m : ℕ}
    (hED : Disjoint E D)
    (small : Fin m ≃ E)
    (block : Fin 3 ≃ D)
    (i : Fin 3) :
    ((appendBlockOrder hED small block (Fin.natAdd m i) :
        (E ∪ D : Set α)) : α) =
      (block i : α) := by
  classical
  simp [appendBlockOrder]

/-- A basis of a rank-preserving deletion is also a basis of the original rank-three matroid.
@isnad1 id=isbase.3h4v.s5.dc439d9a88f3 from=translated src=- shape=20478472 vocab=29f8d00f
-/
theorem isBase_of_delete_isBase_rank3
    (M : Matroid α) {D B : Set α}
    (hRank : M.eRank = 3)
    (hDelRank : (Matroid.delete M D).eRank = 3)
    (hB : (Matroid.delete M D).IsBase B) :
    M.IsBase B := by
  have hI : M.Indep B := hB.indep.of_delete
  have hcard : B.encard = 3 :=
    hB.encard_eq_eRank.trans hDelRank
  have hfin : B.Finite := Set.finite_of_encard_eq_coe hcard
  apply hI.isBase_of_eRk_ge hfin
  exact (hRank.trans (hcard.symm.trans hI.eRk_eq_encard.symm)).le

end

end Rank3KUM
