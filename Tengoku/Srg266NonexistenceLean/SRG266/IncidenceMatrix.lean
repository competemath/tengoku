/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.LocalDesign

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped BigOperators Matrix

namespace SRG266

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def localIncidenceMatrix (x : V) :
    Matrix (FirstSubconstituent G x) (SecondSubconstituent G x) ℤ :=
  fun p B => if p ∈ localBlock G x B then 1 else 0

def allOnesMatrix {m n R : Type*} [One R] : Matrix m n R :=
  fun _ _ => 1

/--
@isnad1 id=eq.0h5v.s4.7319537583d5 from=translated src=- shape=fb088e82 vocab=960605cf
-/
@[simp]
theorem allOnesMatrix_apply {m n R : Type*} [One R] (i : m) (j : n) :
    (allOnesMatrix : Matrix m n R) i j = 1 :=
  rfl

/--
@isnad1 id=eq.1h4v.s6.ca6deb01713b from=translated src=- shape=319fac27 vocab=6e0f54c1
-/
theorem localIncidenceMatrix_row_sum
    (hG : IsHypothetical G) (x : V) (p : FirstSubconstituent G x) :
    ∑ B, localIncidenceMatrix G x p B = 44 := by
  calc
    ∑ B, localIncidenceMatrix G x p B =
        ((blocksThrough G x p).card : ℤ) := by
      simp [localIncidenceMatrix, blocksThrough]
    _ = 44 := by
      rw [blocksThrough_card G hG x p]
      norm_num

/--
@isnad1 id=eq.1h4v.s6.cd4889462685 from=translated src=- shape=bb02e035 vocab=3fa5e87d
-/
theorem localIncidenceMatrix_column_sum
    (hG : IsHypothetical G) (x : V) (B : SecondSubconstituent G x) :
    ∑ p, localIncidenceMatrix G x p B = 9 := by
  calc
    ∑ p, localIncidenceMatrix G x p B = ((localBlock G x B).card : ℤ) := by
      simp only [localIncidenceMatrix, Finset.sum_boole]
      norm_cast
      apply congrArg Finset.card
      ext p
      simp
    _ = 9 := by
      rw [localBlock_card G hG x B]
      norm_num

/--
@isnad1 id=eq.1h3v.s7.b0aabc7e9156 from=translated src=- shape=2850a1ac vocab=95831873
-/
@[simp]
theorem localIncidenceMatrix_mulVec_one
    (hG : IsHypothetical G) (x : V) :
    localIncidenceMatrix G x *ᵥ (1 : SecondSubconstituent G x → ℤ) = 44 := by
  funext p
  rw [Matrix.mulVec_apply_eq_sum]
  simp only [Pi.one_apply, mul_one]
  exact localIncidenceMatrix_row_sum G hG x p

/--
@isnad1 id=eq.1h3v.s7.edf1fee81885 from=translated src=- shape=37dfb971 vocab=47455c65
-/
@[simp]
theorem localIncidenceMatrix_transpose_mulVec_one
    (hG : IsHypothetical G) (x : V) :
    (localIncidenceMatrix G x)ᵀ *ᵥ (1 : FirstSubconstituent G x → ℤ) = 9 := by
  funext B
  rw [Matrix.mulVec_apply_eq_sum]
  simp only [Matrix.transpose_apply, Pi.one_apply, mul_one]
  exact localIncidenceMatrix_column_sum G hG x B

/--
@isnad1 id=eq.1h5v.s7.64ef56135dba from=translated src=- shape=a0d2b281 vocab=56907b12
-/
theorem localIncidence_mul_transpose_apply
    (hG : IsHypothetical G) (x : V)
    (p q : FirstSubconstituent G x) :
    (localIncidenceMatrix G x * (localIncidenceMatrix G x)ᵀ) p q =
      if p = q then 44 else 8 := by
  rw [Matrix.mul_apply]
  by_cases hpq : p = q
  · subst q
    simp only [Matrix.transpose_apply, ite_eq_left]
    calc
      ∑ B, localIncidenceMatrix G x p B * localIncidenceMatrix G x p B =
          ∑ B, localIncidenceMatrix G x p B := by
        apply Finset.sum_congr rfl
        intro B _
        simp [localIncidenceMatrix]
      _ = 44 := localIncidenceMatrix_row_sum G hG x p
  · simp only [Matrix.transpose_apply, ite_eq_right hpq]
    calc
      ∑ B, localIncidenceMatrix G x p B * localIncidenceMatrix G x q B =
          ((blocksThroughPair G x p q).card : ℤ) := by
        simp only [localIncidenceMatrix, ite_zero_mul_ite_zero, one_mul,
          Finset.sum_boole]
        norm_cast
      _ = 8 := by
        rw [blocksThroughPair_card G hG x hpq]
        norm_num

/--
@isnad1 id=eq.1h3v.s9.0f11859ed888 from=translated src=- shape=6fb07753 vocab=27abc2f9
-/
theorem localIncidence_mul_transpose
    (hG : IsHypothetical G) (x : V) :
    localIncidenceMatrix G x * (localIncidenceMatrix G x)ᵀ =
      (36 : ℤ) •
          (1 : Matrix (FirstSubconstituent G x) (FirstSubconstituent G x) ℤ) +
        (8 : ℤ) • allOnesMatrix := by
  ext p q
  rw [localIncidence_mul_transpose_apply G hG x p q]
  by_cases hpq : p = q
  · subst q
    simp [Algebra.smul_def, Matrix.mul_apply, Matrix.ofNat_apply]
  · simp [Algebra.smul_def, Matrix.mul_apply, Matrix.ofNat_apply, hpq]

def blockIntersection (x : V) (B C : SecondSubconstituent G x) : ℕ :=
  (localBlock G x B ∩ localBlock G x C).card

def localIntersectionMatrix (x : V) :
    Matrix (SecondSubconstituent G x) (SecondSubconstituent G x) ℤ :=
  (localIncidenceMatrix G x)ᵀ * localIncidenceMatrix G x

/--
@isnad1 id=eq.1h3v.s7.b60b4f2d818c from=translated src=- shape=cd9c03c9 vocab=c1f4a423
-/
@[simp]
theorem localIntersectionMatrix_mulVec_one
    (hG : IsHypothetical G) (x : V) :
    localIntersectionMatrix G x *ᵥ (1 : SecondSubconstituent G x → ℤ) = 396 := by
  rw [localIntersectionMatrix, ← Matrix.mulVec_mulVec,
    localIncidenceMatrix_mulVec_one G hG x]
  funext B
  rw [Matrix.mulVec_apply_eq_sum]
  change (∑ p, localIncidenceMatrix G x p B * 44) = 396
  calc
    (∑ p, localIncidenceMatrix G x p B * 44) =
        (∑ p, localIncidenceMatrix G x p B) * 44 := by rw [Finset.sum_mul]
    _ = 9 * 44 := by rw [localIncidenceMatrix_column_sum G hG x B]
    _ = 396 := by norm_num

/--
@isnad1 id=eq.0h5v.s5.eb0ea895bfdb from=translated src=- shape=779be289 vocab=86ebac05
-/
theorem localIntersectionMatrix_apply
    (x : V) (B C : SecondSubconstituent G x) :
    localIntersectionMatrix G x B C = blockIntersection G x B C := by
  rw [localIntersectionMatrix, Matrix.mul_apply]
  simp only [Matrix.transpose_apply, localIncidenceMatrix, ite_zero_mul_ite_zero, one_mul,
    Finset.sum_boole]
  norm_cast
  apply congrArg Finset.card
  ext p
  simp

/--
@isnad1 id=eq.1h4v.s5.b465c0d2b80d from=translated src=- shape=de33ca30 vocab=3ab2de47
-/
@[simp]
theorem blockIntersection_self
    (hG : IsHypothetical G) (x : V) (B : SecondSubconstituent G x) :
    blockIntersection G x B B = 9 := by
  simp [blockIntersection, localBlock_card G hG x B]

/--
@isnad1 id=eq.1h4v.s5.69a3cda0a442 from=translated src=- shape=de33ca30 vocab=bed31623
-/
@[simp]
theorem localIntersectionMatrix_diagonal
    (hG : IsHypothetical G) (x : V) (B : SecondSubconstituent G x) :
    localIntersectionMatrix G x B B = 9 := by
  rw [localIntersectionMatrix_apply, blockIntersection_self G hG x B]
  norm_num

end SRG266
