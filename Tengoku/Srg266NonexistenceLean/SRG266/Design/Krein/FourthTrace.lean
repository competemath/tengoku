/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Design.Krein.CubicGram
import Tengoku.Seed.LinearAlgebra.Matrix.Trace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped BigOperators Matrix

namespace SRG266.QuasiSymmetric.TripleDesign57

variable {P B : Type*} [Fintype P] [DecidableEq P] [Fintype B] [DecidableEq B]
    (D : TripleDesign57 P B)

local notation "V" => KreinVertex (P := P) (B := B)

theorem rectangular_gram_square_trace {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (M : Matrix α β ℤ) :
    Matrix.trace ((M * M.transpose)^2) = Matrix.trace ((M.transpose * M)^2) := by
  simpa only [pow_two, Matrix.mul_assoc] using
    (Matrix.trace_mul_comm M (M.transpose * M * M.transpose))

theorem commonCount_comm (T : Finset V) (x y : V) :
    D.commonCount T x y = D.commonCount T y x := by simp [commonCount, and_comm]

theorem natCast_square_sub_nonneg (n : ℕ) : 0 ≤ (n : ℤ)^2 - n := by
  by_cases h : n = 0
  · simp [h]
  · have h1 : (1 : ℤ) ≤ n := by omega
    nlinarith

end SRG266.QuasiSymmetric.TripleDesign57
