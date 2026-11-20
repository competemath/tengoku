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

/--
@isnad1 id=eq.0h2v.s6.d5cdde0350ed from=translated src=- shape=e9fd8109 vocab=6b1587a7
-/
theorem gramA_mulVec_one (n : ℕ) (i : Fin n) :
    (gramA n *ᵥ (fun _ => (1 : ℤ))) i =
      (if i.1 = 0 then 1 else 0) + (if i.1 + 1 = n then 1 else 0) := by
  rw [← graphCartanMatrix_pathGraph, graphCartanMatrix_eq_two_sub_adjMatrix,
    Matrix.sub_mulVec]
  simp only [Pi.sub_apply, Matrix.mulVec_diagonal, mul_one]
  simp only [Matrix.mulVec, dotProduct, SimpleGraph.adjMatrix_apply, mul_one]
  rw [pathGraph_sum_adj_indicator]
  split_ifs <;> omega

/--
@isnad1 id=hasdomin.1h1v.s4.351b08c15e63 from=translated src=- shape=e7998fc0 vocab=b3c9f905
-/
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

/--
@isnad1 id=hasdomin.1h1v.s5.63d582d1c1d5 from=translated src=- shape=369c3101 vocab=c670a2f7
-/
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

/--
@isnad1 id=eq.0h0v.s7.d33b91a37cbc from=translated src=- shape=4c35eb2c vocab=a86b49f6
-/
theorem gramE_mulVec_e6DominantVector :
    gramE 6 *ᵥ e6DominantVector = ![0, 0, 0, 0, 0, 1] := by
  ext i
  fin_cases i <;>
    norm_num [Matrix.mulVec, dotProduct, gramE, gramEEntry, e6DominantVector,
      Fin.sum_univ_succ]

/--
@isnad1 id=hasdomin.0h0v.s4.1a0f37cea5d6 from=translated src=- shape=369af620 vocab=c9f0ca3a
-/
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

/--
@isnad1 id=eq.0h0v.s7.c2b30d7196bb from=translated src=- shape=c5be4d07 vocab=bf884339
-/
theorem gramE_mulVec_e7DominantVector :
    gramE 7 *ᵥ e7DominantVector = ![1, 0, 0, 0, 0, 0, 0] := by
  ext i
  fin_cases i <;>
    norm_num [Matrix.mulVec, dotProduct, gramE, gramEEntry, e7DominantVector,
      Fin.sum_univ_succ]

/--
@isnad1 id=hasdomin.0h0v.s4.fb25de128fca from=translated src=- shape=369af620 vocab=c9f0ca3a
-/
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

/--
@isnad1 id=eq.0h0v.s7.c0dd6bbe61cf from=translated src=- shape=d80e307a vocab=d70cd005
-/
theorem gramE_mulVec_e8DominantVector :
    gramE 8 *ᵥ e8DominantVector = ![0, 0, 0, 0, 0, 0, 1, 0] := by
  ext i
  fin_cases i <;>
    norm_num [Matrix.mulVec, dotProduct, gramE, gramEEntry, e8DominantVector,
      Fin.sum_univ_succ]

/--
@isnad1 id=hasdomin.0h0v.s4.08b9c630d2e8 from=translated src=- shape=369af620 vocab=c9f0ca3a
-/
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

/--
@isnad1 id=hasdomin.1h1v.s4.5c19d03b22bf from=translated src=- shape=041dc7c8 vocab=6a0d32f7
-/
theorem ADEType.hasDominantVector (t : ADEType) (ht : t.IsRegular) :
    HasDominantVector t.gram t.dominantHeight := by
  cases t with
  | A n => exact gramA_hasDominantVector n ht
  | D n => exact gramD_hasDominantVector n ht
  | E6 => exact gramE6_hasDominantVector
  | E7 => exact gramE7_hasDominantVector
  | E8 => exact gramE8_hasDominantVector

/--
@isnad1 id=iff.0h1v.s5.c21aa36abc94 from=translated src=- shape=8f7cad0e vocab=f22f364a
-/
theorem ADEType.dominantHeight_eq_eleven_iff (t : ADEType) :
    t.dominantHeight = 11 ↔ t = .A 11 ∨ t = .D 7 ∨ t = .E6 := by
  cases t <;> simp [dominantHeight] <;> omega

end SRG266.Lattice
