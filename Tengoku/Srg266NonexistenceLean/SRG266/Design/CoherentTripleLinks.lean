/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Design.BlockGraph

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.QuasiSymmetric

namespace ConcreteQSD56

variable (Q : ConcreteQSD56)

def blocksThroughTriple (p q r : Fin 56) : Finset (Fin 210) :=
  Finset.univ.filter fun B =>
    Q.matrix p B = 1 ∧ Q.matrix q B = 1 ∧ Q.matrix r B = 1

def tripleMultiplicity (p q r : Fin 56) : ℕ :=
  (Q.blocksThroughTriple p q r).card

theorem tripleMultiplicity_swap (p q r : Fin 56) :
    Q.tripleMultiplicity p q r = Q.tripleMultiplicity q p r := by
  unfold tripleMultiplicity
  apply congrArg Finset.card
  ext B
  simp only [blocksThroughTriple, Finset.mem_filter, Finset.mem_univ, true_and]
  tauto

theorem tripleMultiplicity_rotate (p q r : Fin 56) :
    Q.tripleMultiplicity p q r = Q.tripleMultiplicity q r p := by
  unfold tripleMultiplicity
  apply congrArg Finset.card
  ext B
  simp only [blocksThroughTriple, Finset.mem_filter, Finset.mem_univ, true_and]
  tauto

def sparseTriple (p q r : Fin 56) : Prop :=
  p ≠ q ∧ p ≠ r ∧ q ≠ r ∧ Q.tripleMultiplicity p q r = 1

theorem sparseTriple_swap (p q r : Fin 56) :
    Q.sparseTriple p q r ↔ Q.sparseTriple q p r := by
  simp only [sparseTriple, ne_eq]
  rw [Q.tripleMultiplicity_swap p q r]
  tauto

theorem sparseTriple_rotate (p q r : Fin 56) :
    Q.sparseTriple p q r ↔ Q.sparseTriple q r p := by
  simp only [sparseTriple, ne_eq]
  rw [Q.tripleMultiplicity_rotate p q r]
  tauto

theorem derived_pairMult_eq_tripleMultiplicity (z : Fin 56)
    (p q : Punctured z) :
    (Q.derived45 z).pairMult p q = Q.tripleMultiplicity z p.val q.val := by
  classical
  rw [Derived45.pairMult, pairCount]
  simp only [ConcreteQSD56.derived45, mem_restrictedBlock]
  have hcard :
      (Finset.univ.filter fun i : Fin 45 =>
        Q.matrix (p : Fin 56) (Q.derivedEnum z i) = 1 ∧
          Q.matrix (q : Fin 56) (Q.derivedEnum z i) = 1).card =
      ((Q.derivedIndex z).filter fun B =>
        Q.matrix (p : Fin 56) B = 1 ∧ Q.matrix (q : Fin 56) B = 1).card :=
    card_filter_of_enum (Q.derivedEnum z) (Q.derivedIndex z)
      derivedEnum_injective derivedEnum_range
        (fun B : Fin 210 =>
          Q.matrix (p : Fin 56) B = 1 ∧ Q.matrix (q : Fin 56) B = 1)
  rw [hcard]
  unfold tripleMultiplicity
  apply congrArg Finset.card
  ext B
  simp only [Finset.mem_filter, mem_derivedIndex, blocksThroughTriple,
    Finset.mem_univ, true_and]

theorem tripleMultiplicity_cases {p q r : Fin 56}
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    Q.tripleMultiplicity p q r = 1 ∨ Q.tripleMultiplicity p q r = 2 := by
  let q' : Punctured p :=
    ⟨q, Finset.mem_erase.mpr ⟨hpq.symm, Finset.mem_univ q⟩⟩
  let r' : Punctured p :=
    ⟨r, Finset.mem_erase.mpr ⟨hpr.symm, Finset.mem_univ r⟩⟩
  have hne : q' ≠ r' := fun h => hqr (congrArg Subtype.val h)
  have h := (Q.derived45 p).pairMult_cases hne
  rw [Q.derived_pairMult_eq_tripleMultiplicity p q' r'] at h
  exact h

noncomputable def tripleLink (z : Fin 56) : SimpleGraph (Punctured z) :=
  (Q.derived45 z).blockGraph

theorem tripleLink_adj_iff_sparseTriple {z : Fin 56} {p q : Punctured z} :
    (Q.tripleLink z).Adj p q ↔ Q.sparseTriple z p.val q.val := by
  rw [tripleLink, Derived45.blockGraph_adj,
    Q.derived_pairMult_eq_tripleMultiplicity z p q]
  have hpz : p.val ≠ z := (Finset.mem_erase.mp p.2).1
  have hqz : q.val ≠ z := (Finset.mem_erase.mp q.2).1
  constructor
  · rintro ⟨hpq, hmult⟩
    exact ⟨hpz.symm, hqz.symm, fun h => hpq (Subtype.ext h), hmult⟩
  · rintro ⟨-, -, hpq, hmult⟩
    exact ⟨fun h => hpq (congrArg Subtype.val h), hmult⟩

theorem tripleLink_isSRGWith (z : Fin 56) :
    @SimpleGraph.IsSRGWith (Punctured z) _ (Q.tripleLink z)
      ((Q.derived45 z).instDecidableRelAdjBlockGraph) 55 18 9 4 := by
  exact (Q.derived45 z).blockGraph_isSRGWith

end ConcreteQSD56

end SRG266.QuasiSymmetric
