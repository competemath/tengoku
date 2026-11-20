/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.ADEPathShape

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

open scoped Matrix BigOperators Classical

theorem sum_fin_ite_val_eq (n k : ℕ) (w : Fin n → ℤ) :
    (∑ j : Fin n, if j.1 = k then w j else 0) =
      if h : k < n then w ⟨k, h⟩ else 0 := by
  by_cases hk : k < n
  · have he (j : Fin n) : j.1 = k ↔ j = ⟨k, hk⟩ := by
      simp only [Fin.ext_iff]
    simp [he, hk]
  · have he (j : Fin n) : j.1 ≠ k := by omega
    simp [he, hk]

def dDominantVector (n : ℕ) (i : Fin n) : ℤ :=
  if i.1 = 0 ∨ n ≤ i.1 + 2 then 1 else 2

theorem gramDEntry_sparse {n : ℕ} (hn : 4 ≤ n) (i j : Fin n) :
    gramDEntry n i.1 j.1 =
      (if j = i then 2 else 0) -
      (if i.1 + 3 ≤ n then (if j.1 = i.1 + 1 then 1 else 0) else 0) -
      (if 0 < i.1 ∧ i.1 + 2 ≤ n then (if j.1 = i.1 - 1 then 1 else 0) else 0) -
      (if i.1 + 3 = n then (if j.1 = n - 1 then 1 else 0) else 0) -
      (if i.1 + 1 = n then (if j.1 = n - 3 then 1 else 0) else 0) := by
  simp only [gramDEntry, Fin.ext_iff]
  split_ifs <;> omega

theorem gramD_mulVec_dDominantVector (n : ℕ) (hn : 4 ≤ n) (i : Fin n) :
    (gramD n *ᵥ dDominantVector n) i = if i.1 = 1 then 1 else 0 := by
  classical
  simp only [Matrix.mulVec, dotProduct, gramD]
  simp_rw [gramDEntry_sparse hn, sub_mul, ite_mul, one_mul, zero_mul]
  simp only [Finset.sum_sub_distrib, Finset.sum_ite_irrel]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  simp_rw [sum_fin_ite_val_eq]
  have hp : i.1 - 1 < n := by omega
  have hl : n - 1 < n := by omega
  have hf : n - 3 < n := by omega
  simp only [Finset.sum_const_zero, dite_eq_left hp, dite_eq_left hl, dite_eq_left hf]
  simp only [dDominantVector]
  repeat' first | omega | split

theorem sum_dDominantVector (n : ℕ) (hn : 4 ≤ n) :
    (∑ i, dDominantVector n i) = 2 * (n : ℤ) - 3 := by
  have hformula (i : Fin n) : dDominantVector n i =
      2 - (if i.1 = 0 then 1 else 0) -
        (if i.1 = n - 2 then 1 else 0) -
        (if i.1 = n - 1 then 1 else 0) := by
    simp only [dDominantVector]
    split_ifs <;> omega
  simp_rw [hformula, Finset.sum_sub_distrib, sum_fin_ite_val_eq]
  have h0 : 0 < n := by omega
  have h2 : n - 2 < n := by omega
  have h1 : n - 1 < n := by omega
  simp only [dite_eq_left h0, dite_eq_left h2, dite_eq_left h1, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem dDominantVector_norm_two (n : ℕ) (hn : 4 ≤ n) :
    Matrix.toBilin' (gramD n) (dDominantVector n) (dDominantVector n) = 2 := by
  rw [Matrix.toBilin'_apply']
  simp only [dotProduct]
  simp_rw [gramD_mulVec_dDominantVector n hn, mul_ite, mul_one, mul_zero]
  rw [sum_fin_ite_val_eq]
  have h1 : 1 < n := by omega
  have h3 : ¬ n ≤ 3 := by omega
  norm_num [h1, dDominantVector, h3]

end SRG266.Lattice
