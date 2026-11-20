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

/--
@isnad1 id=eq.0h3v.s5.75c442e28483 from=translated src=- shape=891d9146 vocab=75b774ed
-/
theorem binary (p : Fin 56) (B : Fin 210) :
    Q.matrix p B * Q.matrix p B = Q.matrix p B := Q.2.1 p B

/--
@isnad1 id=eq.0h3v.s7.78ac256e501c from=translated src=- shape=fa47f87c vocab=068a24c4
-/
theorem point_gram (p q : Fin 56) :
    (Q.matrix * Q.matrix.transpose) p q = if p = q then 45 else 9 := Q.2.2.1 p q

/--
@isnad1 id=eq.0h2v.s5.8773c9422cef from=translated src=- shape=0bfbe2dd vocab=33866ad7
-/
theorem block_size (B : Fin 210) : incidenceColumnSum Q.matrix B = 12 :=
  Q.2.2.2.1 B

/--
@isnad1 id=or.1h3v.s7.fb3bf9e70bcb from=translated src=- shape=0af2f18c vocab=ccd2390f
-/
theorem block_intersections {B D : Fin 210} (h : B ≠ D) :
    (Q.matrix.transpose * Q.matrix) B D = 0 ∨
      (Q.matrix.transpose * Q.matrix) B D = 3 := Q.2.2.2.2 B D h

/--
@isnad1 id=or.0h3v.s5.f23050b685a6 from=translated src=- shape=3e1b7568 vocab=38c439ad
-/
theorem entry_cases (p : Fin 56) (B : Fin 210) :
    Q.matrix p B = 0 ∨ Q.matrix p B = 1 := by
  have h := Q.binary p B
  have hfactor : Q.matrix p B * (Q.matrix p B - 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp hfactor with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (by linarith)

/--
@isnad1 id=eq.0h2v.s5.4b29a148d9ee from=translated src=- shape=326666f1 vocab=ba547b9d
-/
theorem row_sum (p : Fin 56) : ∑ B, Q.matrix p B = 45 :=
  incidence_row_sum_eq_forty_five Q.matrix Q.binary Q.point_gram p

end ConcreteQSD56

universe u

end SRG266.QuasiSymmetric
