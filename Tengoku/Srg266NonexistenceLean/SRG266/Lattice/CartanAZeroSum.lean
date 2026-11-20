/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.ADEGram
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.IntegerCoordinates
import Tengoku.Seed.LinearAlgebra.Finsupp.LinearCombination
import Tengoku.Seed.LinearAlgebra.Matrix.BilinearForm

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

open scoped BigOperators

def aSimpleVector {n : ℕ} (i : Fin n) : Fin (n+1) → ℚ :=
  Pi.single i.castSucc 1-Pi.single i.succ 1

theorem aSimpleVector_pair {n : ℕ} (i : Fin n) (x : Fin (n+1) → ℚ) :
    standardRatForm (n+1) (aSimpleVector i) x = x i.castSucc-x i.succ := by
  simp [aSimpleVector, standardRatForm_apply, Pi.single_apply, ite_mul]

theorem aSimpleVector_gram {n : ℕ} (i j : Fin n) :
    standardRatForm (n+1) (aSimpleVector i) (aSimpleVector j) = (gramA n i j : ℚ) := by
  rw [aSimpleVector_pair]
  simp only [aSimpleVector, Pi.sub_apply, Pi.single_apply, Fin.ext_iff,
    Fin.val_castSucc, Fin.val_succ, gramA, gramAEntry]
  split_ifs <;> norm_num <;> omega

theorem aSimpleVector_sum {n : ℕ} (i : Fin n) : (∑ j, aSimpleVector i j) = 0 := by
  simp [aSimpleVector, Finset.sum_sub_distrib]

noncomputable def cartanAZeroSum (n : ℕ) : (Fin n → ℚ) →ₗ[ℚ] (Fin (n+1) → ℚ) :=
  Fintype.linearCombination ℚ aSimpleVector

@[simp]
theorem cartanAZeroSum_single {n : ℕ} (i : Fin n) :
    cartanAZeroSum n (Pi.single i 1) = aSimpleVector i := by
  simp [cartanAZeroSum]

theorem cartanAZeroSum_sum (n : ℕ) (u : Fin n → ℚ) :
    (∑ j, cartanAZeroSum n u j) = 0 := by
  change (∑ j, (∑ i, u i • aSimpleVector i) j) = 0
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, aSimpleVector_sum, mul_zero, Finset.sum_const_zero]

end SRG266.Lattice
