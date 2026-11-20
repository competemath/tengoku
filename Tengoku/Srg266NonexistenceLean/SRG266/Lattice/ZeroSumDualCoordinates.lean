/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.CenteredIntegerMinimum
import Tengoku.Seed.Data.Fin.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

open scoped BigOperators

/--
@isnad1 id=ex.2h2v.s8.9f26f5c3a6d9 from=translated src=- shape=7c964bff vocab=62ca4c71
-/
theorem exists_centered_integer_coordinates (n : ℕ) (x : Fin (n+1) → ℚ)
    (hsum : (∑ i, x i) = 0)
    (hdiff : ∀ i : Fin n, x i.castSucc-x i.succ ∈ (1 : Submodule ℤ ℚ)) :
    ∃ a : ℤ, 0 ≤ a ∧ a ≤ n ∧ ∃ z : Fin (n+1) → ℤ,
      (∑ i, z i) = a ∧ ∀ i, x i = (z i : ℚ)-(a : ℚ)/((n : ℚ)+1) := by
  have hbase : ∀ i, x i-x 0 ∈ (1 : Submodule ℤ ℚ) := by
    intro i
    induction i using Fin.induction with
    | zero => simp
    | succ i ih =>
        have h := (1 : Submodule ℤ ℚ).sub_mem ih (hdiff i)
        convert h using 1
        ring
  choose d hd using (fun i => mem_one_iff.mp (hbase i))
  let s : ℤ := ∑ i, d i
  let c : ℤ := s/((n : ℤ)+1)
  let a : ℤ := s%((n : ℤ)+1)
  let z : Fin (n+1) → ℤ := fun i => d i-c
  have hnZ : 0 < (n : ℤ)+1 := by omega
  have ha : 0 ≤ a ∧ a ≤ n := by
    have h0 := Int.emod_nonneg s (ne_of_gt hnZ)
    have h1 := Int.emod_lt_of_pos s hnZ
    change 0 ≤ s%((n : ℤ)+1) ∧ s%((n : ℤ)+1) ≤ n
    omega
  have hs : s = ((n : ℤ)+1)*c+a := (Int.mul_ediv_add_emod s ((n : ℤ)+1)).symm
  have hsQ : (s : ℚ) = -((n : ℚ)+1)*x 0 := by
    change ((∑ i, d i : ℤ) : ℚ) = _
    push_cast
    simp_rw [hd]
    rw [Finset.sum_sub_distrib, hsum]
    simp
    ring
  have heQ : (s : ℚ) = ((n : ℚ)+1)*(c : ℚ)+(a : ℚ) := by exact_mod_cast hs
  have hn : (n : ℚ)+1 ≠ 0 := by positivity
  refine ⟨a, ha.1, ha.2, z, ?_, ?_⟩
  · dsimp only [z]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    change s-((n : ℤ)+1)*c = a
    omega
  · intro i
    change x i = ((d i-c : ℤ) : ℚ)-(a : ℚ)/((n : ℚ)+1)
    push_cast
    rw [hd i]
    field_simp
    nlinarith

/--
@isnad1 id=mem.0h4v.s7.416e8249fde8 from=translated src=- shape=729f679b vocab=edfcc7fd
-/
theorem centered_coordinates_adjacent_integral {n : ℕ} (z : Fin (n+1) → ℤ) (a : ℤ)
    (i : Fin n) :
    ((z i.castSucc : ℚ)-(a : ℚ)/((n : ℚ)+1))-
      ((z i.succ : ℚ)-(a : ℚ)/((n : ℚ)+1)) ∈ (1 : Submodule ℤ ℚ) := by
  refine mem_one_iff.mpr ⟨z i.castSucc-z i.succ, ?_⟩
  push_cast
  ring

end SRG266.Lattice
