/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Seed.Algebra.Order.BigOperators.Group.Finset
import Tengoku.Seed.Algebra.BigOperators.Fin
import Tengoku.Seed.Algebra.Order.Ring.Int

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

open scoped BigOperators

theorem sum_on_embedding_le_sum {m n : ℕ} (z : Fin n → ℤ)
    (hz : ∀ i, 0 ≤ z i) (f : Fin m ↪ Fin n) :
    (∑ i, z (f i)) ≤ ∑ j, z j := by
  classical
  calc
    _ = ∑ j ∈ Finset.univ.image f, z j :=
      (Finset.sum_image (fun i _ j _ h => f.injective h)).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun j _ _ => hz j)

theorem binary_constant_block_bounds {m n : ℕ} (z : Fin n → ℤ)
    (a t : ℤ) (f : Fin m ↪ Fin n) (hsum : (∑ i, z i) = a)
    (hbinary : ∀ i, z i = 0 ∨ z i = 1) (hconst : ∀ i, z (f i) = t) :
    (m : ℤ)*t ≤ a ∧ (m : ℤ)*(1-t) ≤ (n : ℤ)-a := by
  have hlow := sum_on_embedding_le_sum z (fun i => by rcases hbinary i with h | h <;> omega) f
  have hhigh := sum_on_embedding_le_sum (fun i => 1-z i)
    (fun i => by rcases hbinary i with h | h <;> omega) f
  simpa only [hconst, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Finset.sum_sub_distrib, hsum, mul_one] using And.intro hlow hhigh

theorem binary_twelve_constant_block {m : ℕ} (hm : 4 ≤ m)
    (z : Fin 12 → ℤ) (a t : ℤ) (f : Fin m ↪ Fin 12)
    (hsum : (∑ i, z i) = a) (hbinary : ∀ i, z i = 0 ∨ z i = 1)
    (hconst : ∀ i, z (f i) = t) (ha : a = 9 ∨ a = 1) :
    (a = 9 ∧ t = 1) ∨ (a = 1 ∧ t = 0) := by
  have hb := hbinary (f ⟨0, by omega⟩)
  rw [hconst] at hb
  obtain ⟨hlow, hhigh⟩ := binary_constant_block_bounds z a t f hsum hbinary hconst
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all
  all_goals omega

end SRG266.Lattice
