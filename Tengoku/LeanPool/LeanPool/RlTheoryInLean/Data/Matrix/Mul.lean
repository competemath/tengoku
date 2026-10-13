/-
Copyright (c) 2026 Shangtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shangtong Zhang
-/
module

public import Tengoku

/-!
# LeanPool.RlTheoryInLean.Data.Matrix.Mul
-/

@[expose] public section

open Finset Real

namespace Matrix

variable {m n β : Type*} [Fintype m]

section square

variable {A : Matrix m m ℝ}

lemma dotProduct_transpose_mulVec_real (x y : m → ℝ) :
   x ⬝ᵥ Aᵀ *ᵥ y = y ⬝ᵥ A *ᵥ x := by
  simpa using Matrix.dotProduct_transpose_mulVec (A := A) (x := x) (y := y)

lemma vecMul_diagonal_dotProduct
  [DecidableEq m] (d x y : m → ℝ) :
  x ᵥ* Matrix.diagonal d ⬝ᵥ y = ∑ i, d i * x i * y i := by
  simp only [dotProduct, vecMul, diagonal, of_apply, mul_ite, mul_zero, sum_ite_eq', mem_univ,
    ↓reduceIte]
  apply sum_congr rfl
  ring_nf
  simp

end square

end Matrix
