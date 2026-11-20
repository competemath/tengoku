/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Seed.Combinatorics.Enumerative.DoubleCounting
import Tengoku.Seed.Data.Finset.Powerset
import Tengoku.Seed.Data.Fintype.Card
import Tengoku.Seed.Tactic.NormNum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped BigOperators

namespace SRG266.QuasiSymmetric

theorem no_steinerQuadruple_on12 {α : Type*} [DecidableEq α]
    (X : Finset α) (hX : X.card = 12) (blocks : Finset (Finset α))
    (hsize : ∀ B ∈ blocks, B.card = 4)
    (hinside : ∀ B ∈ blocks, B ⊆ X)
    (htriple : ∀ T : Finset α, T ⊆ X → T.card = 3 →
      (blocks.filter fun B => T ⊆ B).card = 1) : False := by
  classical
  obtain ⟨a,haX⟩ := Finset.card_pos.mp (by omega : 0 < X.card)
  let through := blocks.filter fun B => a ∈ B
  let pairs := (X.erase a).powersetCard 2
  have hpairs : pairs.card = 55 := by
    rw [Finset.card_powersetCard,Finset.card_erase_of_mem haX,hX]
    decide
  have hleft : ∀ B ∈ through, (pairs.filter fun T => T ⊆ B).card = 3 := by
    intro B hB
    have hb := Finset.mem_filter.mp hB
    have heq : pairs.filter (fun T => T ⊆ B) = (B.erase a).powersetCard 2 := by
      ext T
      simp only [pairs, Finset.mem_filter, Finset.mem_powersetCard]
      constructor
      · rintro ⟨⟨hT, hcard⟩, hsub⟩
        refine ⟨?_, hcard⟩
        intro x hx
        exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp (hT hx)).1, hsub hx⟩
      · rintro ⟨hT, hcard⟩
        refine ⟨⟨?_, hcard⟩, ?_⟩
        · intro x hx
          exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp (hT hx)).1,
            hinside B hb.1 (Finset.mem_of_mem_erase (hT hx))⟩
        · intro x hx
          exact Finset.mem_of_mem_erase (hT hx)
    rw [heq, Finset.card_powersetCard, Finset.card_erase_of_mem hb.2, hsize B hb.1]
    decide
  have hright : ∀ T ∈ pairs, (through.filter fun B => T ⊆ B).card = 1 := by
    intro T hT
    have ht := Finset.mem_powersetCard.mp hT
    have ha : a ∉ T := by
      intro ha
      exact Finset.notMem_erase a X (ht.1 ha)
    have hi : (insert a T).card = 3 := by
      rw [Finset.card_insert_of_notMem ha, ht.2]
    have hiX : insert a T ⊆ X := Finset.insert_subset_iff.mpr
      ⟨haX,fun _ hx => Finset.mem_of_mem_erase (ht.1 hx)⟩
    have h := htriple (insert a T) hiX hi
    have heq : through.filter (fun B => T ⊆ B) =
        blocks.filter (fun B => insert a T ⊆ B) := by
      ext B
      simp [through, Finset.insert_subset_iff, and_assoc]
    rw [heq]
    exact h
  have hcount := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := through) (t := pairs) (fun B T => T ⊆ B)
  simp only [Finset.bipartiteAbove, Finset.bipartiteBelow] at hcount
  rw [Finset.sum_congr rfl hleft, Finset.sum_congr rfl hright] at hcount
  simp only [Finset.sum_const, Nat.nsmul_eq_mul, mul_one, hpairs] at hcount
  omega

theorem no_steinerQuadruple12
    (blocks : Finset (Finset (Fin 12)))
    (hsize : ∀ B ∈ blocks, B.card = 4)
    (htriple : ∀ T : Finset (Fin 12), T.card = 3 →
      (blocks.filter fun B => T ⊆ B).card = 1) : False :=
  no_steinerQuadruple_on12 Finset.univ (by decide) blocks hsize
    (fun _ _ => Finset.subset_univ _) (fun T _ hT => htriple T hT)

end SRG266.QuasiSymmetric
