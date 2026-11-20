/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.ADEDominantD

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

open scoped Matrix BigOperators Classical

def HasDominantVector {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) (h : ℤ) : Prop :=
  ∃ z : ι → ℤ, (∀ i, 0 ≤ z i) ∧ Matrix.toBilin' A z z = 2 ∧
    (∀ i, 0 ≤ (A *ᵥ z) i) ∧ (∑ i, z i) = h

theorem gramA_mulVec_one (n : ℕ) (i : Fin n) :
    (gramA n *ᵥ (fun _ => (1 : ℤ))) i =
      (if i.1 = 0 then 1 else 0) + (if i.1 + 1 = n then 1 else 0) := by
  rw [← graphCartanMatrix_pathGraph, graphCartanMatrix_eq_two_sub_adjMatrix,
    Matrix.sub_mulVec]
  simp only [Pi.sub_apply, Matrix.mulVec_diagonal, mul_one]
  simp only [Matrix.mulVec, dotProduct, SimpleGraph.adjMatrix_apply, mul_one]
  rw [pathGraph_sum_adj_indicator]
  split_ifs <;> omega

theorem gramA_hasDominantVector (n : ℕ) (hn : 1 ≤ n) :
    HasDominantVector (gramA n) n := by
  refine ⟨fun _ => 1, by intro i; norm_num, ?_, ?_, by simp⟩
  · rw [Matrix.toBilin'_apply']
    simp only [dotProduct, one_mul]
    simp_rw [gramA_mulVec_one]
    rw [Finset.sum_add_distrib]
    have hlast (i : Fin n) : i.1 + 1 = n ↔ i.1 = n - 1 := by omega
    simp_rw [hlast, sum_fin_ite_val_eq]
    have h0 : 0 < n := by omega
    have h1 : n - 1 < n := by omega
    simp [h0, h1]
  · intro i
    rw [gramA_mulVec_one]
    split_ifs <;> norm_num

theorem gramD_hasDominantVector (n : ℕ) (hn : 4 ≤ n) :
    HasDominantVector (gramD n) (2 * (n : ℤ) - 3) := by
  refine ⟨dDominantVector n, ?_, dDominantVector_norm_two n hn, ?_,
    sum_dDominantVector n hn⟩
  · intro i
    simp only [dDominantVector]
    split_ifs <;> norm_num
  · intro i
    rw [gramD_mulVec_dDominantVector n hn]
    split_ifs <;> norm_num

def e6DominantVector : Fin 6 → ℤ := ![1, 2, 3, 2, 1, 2]
def e7DominantVector : Fin 7 → ℤ := ![2, 3, 4, 3, 2, 1, 2]
def e8DominantVector : Fin 8 → ℤ := ![2, 4, 6, 5, 4, 3, 2, 3]

theorem gramE_mulVec_e6DominantVector :
    gramE 6 *ᵥ e6DominantVector = ![0, 0, 0, 0, 0, 1] := by
  ext i
  fin_cases i <;>
    norm_num [Matrix.mulVec, dotProduct, gramE, gramEEntry, e6DominantVector,
      Fin.sum_univ_succ]

theorem gramE6_hasDominantVector :
    HasDominantVector (gramE 6) 11 := by
  refine ⟨e6DominantVector, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num [e6DominantVector]
  · rw [Matrix.toBilin'_apply', gramE_mulVec_e6DominantVector]
    norm_num [dotProduct, e6DominantVector, Fin.sum_univ_succ]
  · intro i
    rw [gramE_mulVec_e6DominantVector]
    fin_cases i <;> norm_num
  · norm_num [e6DominantVector, Fin.sum_univ_succ]

theorem gramE_mulVec_e7DominantVector :
    gramE 7 *ᵥ e7DominantVector = ![1, 0, 0, 0, 0, 0, 0] := by
  ext i
  fin_cases i <;>
    norm_num [Matrix.mulVec, dotProduct, gramE, gramEEntry, e7DominantVector,
      Fin.sum_univ_succ]

theorem gramE7_hasDominantVector :
    HasDominantVector (gramE 7) 17 := by
  refine ⟨e7DominantVector, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num [e7DominantVector]
  · rw [Matrix.toBilin'_apply', gramE_mulVec_e7DominantVector]
    norm_num [dotProduct, e7DominantVector, Fin.sum_univ_succ]
  · intro i
    rw [gramE_mulVec_e7DominantVector]
    fin_cases i <;> norm_num
  · norm_num [e7DominantVector, Fin.sum_univ_succ]

theorem gramE_mulVec_e8DominantVector :
    gramE 8 *ᵥ e8DominantVector = ![0, 0, 0, 0, 0, 0, 1, 0] := by
  ext i
  fin_cases i <;>
    norm_num [Matrix.mulVec, dotProduct, gramE, gramEEntry, e8DominantVector,
      Fin.sum_univ_succ]

theorem gramE8_hasDominantVector :
    HasDominantVector (gramE 8) 29 := by
  refine ⟨e8DominantVector, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num [e8DominantVector]
  · rw [Matrix.toBilin'_apply', gramE_mulVec_e8DominantVector]
    norm_num [dotProduct, e8DominantVector, Fin.sum_univ_succ]
  · intro i
    rw [gramE_mulVec_e8DominantVector]
    fin_cases i <;> norm_num
  · norm_num [e8DominantVector, Fin.sum_univ_succ]

def ADEType.dominantHeight : ADEType → ℤ
  | .A n => n
  | .D n => 2 * (n : ℤ) - 3
  | .E6 => 11
  | .E7 => 17
  | .E8 => 29

theorem ADEType.hasDominantVector (t : ADEType) (ht : t.IsRegular) :
    HasDominantVector t.gram t.dominantHeight := by
  cases t with
  | A n => exact gramA_hasDominantVector n ht
  | D n => exact gramD_hasDominantVector n ht
  | E6 => exact gramE6_hasDominantVector
  | E7 => exact gramE7_hasDominantVector
  | E8 => exact gramE8_hasDominantVector

theorem ADEType.dominantHeight_eq_eleven_iff (t : ADEType) :
    t.dominantHeight = 11 ↔ t = .A 11 ∨ t = .D 7 ∨ t = .E6 := by
  cases t <;> simp [dominantHeight] <;> omega

end SRG266.Lattice
