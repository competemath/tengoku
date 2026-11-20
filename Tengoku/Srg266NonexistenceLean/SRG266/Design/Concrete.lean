/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.CocliqueDesign

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped BigOperators Matrix

namespace SRG266.QuasiSymmetric

def ConcreteQSD56 : Type :=
  { M : Matrix (Fin 56) (Fin 210) ℤ //
      (∀ p B, M p B * M p B = M p B) ∧
      (∀ p q, (M * M.transpose) p q = if p = q then 45 else 9) ∧
      (∀ B, incidenceColumnSum M B = 12) ∧
      (∀ B D, B ≠ D → (M.transpose * M) B D = 0 ∨ (M.transpose * M) B D = 3) }

namespace ConcreteQSD56

variable (Q : ConcreteQSD56)

def matrix : Matrix (Fin 56) (Fin 210) ℤ := Q.1

theorem binary (p : Fin 56) (B : Fin 210) :
    Q.matrix p B * Q.matrix p B = Q.matrix p B := Q.2.1 p B

theorem point_gram (p q : Fin 56) :
    (Q.matrix * Q.matrix.transpose) p q = if p = q then 45 else 9 := Q.2.2.1 p q

theorem block_size (B : Fin 210) : incidenceColumnSum Q.matrix B = 12 :=
  Q.2.2.2.1 B

theorem block_intersections {B D : Fin 210} (h : B ≠ D) :
    (Q.matrix.transpose * Q.matrix) B D = 0 ∨
      (Q.matrix.transpose * Q.matrix) B D = 3 := Q.2.2.2.2 B D h

theorem entry_cases (p : Fin 56) (B : Fin 210) :
    Q.matrix p B = 0 ∨ Q.matrix p B = 1 := by
  have h := Q.binary p B
  have hfactor : Q.matrix p B * (Q.matrix p B - 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp hfactor with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (by linarith)

theorem row_sum (p : Fin 56) : ∑ B, Q.matrix p B = 45 :=
  incidence_row_sum_eq_forty_five Q.matrix Q.binary Q.point_gram p

end ConcreteQSD56

universe u

end SRG266.QuasiSymmetric
