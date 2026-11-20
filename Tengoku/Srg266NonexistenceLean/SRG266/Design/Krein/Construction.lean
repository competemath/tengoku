/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Design.OnePointExtension57

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped BigOperators Matrix

namespace SRG266.QuasiSymmetric.TripleDesign57

variable {P B : Type*} [Fintype P] [DecidableEq P] [Fintype B] [DecidableEq B]
    (D : TripleDesign57 P B)

def incidence : Matrix P B ℤ := fun p b => if p ∈ D.block b then 1 else 0

def disjointness : Matrix B B ℤ :=
  fun b c => if (D.block b ∩ D.block c).card = 0 then 1 else 0

/--
@isnad1 id=eq.0h4v.s5.911f3cc79680 from=translated src=- shape=b9cbe6b2 vocab=d022894c
-/
theorem incidence_row_sum (p : P) : ∑ b, D.incidence p b = 56 := by
  simp [incidence, Finset.sum_boole, D.replication]

/--
@isnad1 id=eq.0h4v.s5.70f23600545d from=translated src=- shape=4f7bb0c9 vocab=d022894c
-/
theorem incidence_column_sum (b : B) : ∑ p, D.incidence p b = 12 := by
  simp [incidence, D.block_size]

/--
@isnad1 id=eq.0h5v.s6.c313031af71e from=translated src=- shape=b2508c6b vocab=b1feb0d4
-/
theorem incidence_point_gram_apply (p q : P) :
    (D.incidence * D.incidence.transpose) p q = if p = q then 56 else 11 := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, incidence,
    ite_zero_mul_ite_zero, one_mul, Finset.sum_boole]
  by_cases hpq : p = q
  · subst q
    simp [D.replication]
  · rw [D.point_pair p q hpq, ite_eq_right hpq]
    norm_num

/--
@isnad1 id=eq.0h3v.s7.66f04c8a4b2f from=translated src=- shape=667750f3 vocab=271da7d4
-/
theorem incidence_point_gram :
    D.incidence * D.incidence.transpose =
      (45 : ℤ) • (1 : Matrix P P ℤ) + (11 : ℤ) • allOnesMatrix := by
  ext p q
  rw [D.incidence_point_gram_apply]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, allOnesMatrix_apply,
    Matrix.one_apply, mul_one]
  by_cases hpq : p = q <;> simp [hpq]

/--
@isnad1 id=eq.0h5v.s6.12377eb987de from=translated src=- shape=65121c46 vocab=8df2218b
-/
theorem incidence_block_gram_apply (b c : B) :
    (D.incidence.transpose * D.incidence) b c = (D.block b ∩ D.block c).card := by
  simp [Matrix.mul_apply, incidence, Finset.inter_comm]

/--
@isnad1 id=eq.0h4v.s5.5fb263fa9468 from=translated src=- shape=fa2cec74 vocab=f7104c5e
-/
theorem disjointness_diag (b : B) : D.disjointness b b = 0 := by
  simp [disjointness, D.block_size]

/--
@isnad1 id=eq.0h5v.s5.e558a8917df8 from=translated src=- shape=4e3fea52 vocab=f7104c5e
-/
theorem disjointness_comm (b c : B) : D.disjointness b c = D.disjointness c b := by
  simp [disjointness, Finset.inter_comm]

/--
@isnad1 id=eq.0h3v.s8.c52d2b51ecc2 from=translated src=- shape=f5cdc22a vocab=edadc670
-/
theorem incidence_block_gram :
    D.incidence.transpose * D.incidence =
      (9 : ℤ) • (1 : Matrix B B ℤ) + (3 : ℤ) • allOnesMatrix -
        (3 : ℤ) • D.disjointness := by
  ext b c
  rw [D.incidence_block_gram_apply]
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    allOnesMatrix_apply, Matrix.one_apply, mul_one]
  by_cases hbc : b = c
  · subst c
    simp [D.disjointness_diag, D.block_size]
  · rcases D.block_intersections b c hbc with hz | ht
    · simp [hz, disjointness, hbc]
    · simp [ht, disjointness, hbc]

/--
@isnad1 id=eq.0h3v.s6.c6e878633012 from=translated src=- shape=9e9d305b vocab=2479f912
-/
theorem incidence_mul_ones :
    D.incidence * (allOnesMatrix : Matrix B B ℤ) =
      (56 : ℤ) • (allOnesMatrix : Matrix P B ℤ) := by
  ext p b
  simpa [Matrix.mul_apply, allOnesMatrix] using D.incidence_row_sum p

/--
@isnad1 id=eq.0h3v.s6.f6d1c31b2403 from=translated src=- shape=e2716f02 vocab=2479f912
-/
theorem ones_mul_incidence :
    (allOnesMatrix : Matrix P P ℤ) * D.incidence =
      (12 : ℤ) • (allOnesMatrix : Matrix P B ℤ) := by
  ext p b
  simpa [Matrix.mul_apply, allOnesMatrix] using D.incidence_column_sum b

/--
@isnad1 id=eq.0h3v.s6.0efa823a92f4 from=translated src=- shape=c963f319 vocab=4c6f7705
-/
theorem incidence_transpose_mul_rect_ones :
    D.incidence.transpose * (allOnesMatrix : Matrix P B ℤ) =
      (12 : ℤ) • (allOnesMatrix : Matrix B B ℤ) := by
  ext b c
  simpa [Matrix.mul_apply, allOnesMatrix] using D.incidence_column_sum b

/--
@isnad1 id=eq.0h4v.s5.aea9fecca7b3 from=translated src=- shape=5f5e8d6d vocab=de48abd7
-/
theorem disjointness_row_sum (b : B) : ∑ c, D.disjointness b c = 45 := by
  have hgram : (D.incidence.transpose * D.incidence) *
      (allOnesMatrix : Matrix B B ℤ) = (672 : ℤ) • allOnesMatrix := by
    rw [Matrix.mul_assoc, D.incidence_mul_ones, Matrix.mul_smul,
      D.incidence_transpose_mul_rect_ones]
    module
  rw [D.incidence_block_gram] at hgram
  have h := congrFun (congrFun hgram b) b
  simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul, allOnesMatrix_apply, mul_one, Matrix.one_apply,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at h
  simp [D.index_card] at h
  omega

/--
@isnad1 id=eq.0h3v.s6.3e2cd5ff691d from=translated src=- shape=c5536343 vocab=d52e10b4
-/
theorem disjointness_mul_ones : D.disjointness * (allOnesMatrix : Matrix B B ℤ) =
    (45 : ℤ) • allOnesMatrix := by
  ext b c
  simpa [Matrix.mul_apply, allOnesMatrix] using D.disjointness_row_sum b

/--
@isnad1 id=eq.0h3v.s6.472a1a80991c from=translated src=- shape=cc2d0a91 vocab=d52e10b4
-/
theorem ones_mul_disjointness : (allOnesMatrix : Matrix B B ℤ) * D.disjointness =
    (45 : ℤ) • allOnesMatrix := by
  ext b c
  simpa [Matrix.mul_apply, allOnesMatrix, D.disjointness_comm c] using D.disjointness_row_sum c

/--
@isnad1 id=eq.0h3v.s7.59e0e7c54363 from=translated src=- shape=2dda556e vocab=f9c3c320
-/
theorem incidence_mul_disjointness : D.incidence * D.disjointness =
    (12 : ℤ) • ((allOnesMatrix : Matrix P B ℤ) - D.incidence) := by
  have h := Matrix.mul_assoc D.incidence D.incidence.transpose D.incidence
  rw [D.incidence_point_gram, D.incidence_block_gram] at h
  simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_sub,
    Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, D.ones_mul_incidence,
    D.incidence_mul_ones] at h
  ext p b
  have he := congrFun (congrFun h p) b
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul, allOnesMatrix_apply] at he ⊢
  omega

/--
@isnad1 id=eq.0h3v.s8.fdb74542c03a from=translated src=- shape=f3269d21 vocab=271da7d4
-/
theorem block_gram_square :
    (D.incidence.transpose * D.incidence) * (D.incidence.transpose * D.incidence) =
      (45 : ℤ) • (D.incidence.transpose * D.incidence) +
        (1584 : ℤ) • (allOnesMatrix : Matrix B B ℤ) := by
  have houter : D.incidence.transpose * (allOnesMatrix : Matrix P P ℤ) * D.incidence =
      (144 : ℤ) • (allOnesMatrix : Matrix B B ℤ) := by
    rw [Matrix.mul_assoc, D.ones_mul_incidence, Matrix.mul_smul,
      D.incidence_transpose_mul_rect_ones]
    module
  calc
    _ = D.incidence.transpose * (D.incidence * D.incidence.transpose) * D.incidence := by
      simp [Matrix.mul_assoc]
    _ = _ := by
      rw [D.incidence_point_gram, Matrix.mul_add, Matrix.add_mul,
        Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul]
      simp only [Matrix.mul_one, Matrix.smul_mul, houter]
      module

/--
@isnad1 id=eq.0h3v.s8.caaa07fb469f from=translated src=- shape=18ad7ee8 vocab=a583714d
-/
theorem disjointness_square : D.disjointness * D.disjointness =
    (36 : ℤ) • (1 : Matrix B B ℤ) - (9 : ℤ) • D.disjointness +
      (9 : ℤ) • allOnesMatrix := by
  let S := D.incidence.transpose * D.incidence
  let A := D.disjointness
  let J : Matrix B B ℤ := allOnesMatrix
  have htarget : S = (9 : ℤ) • 1 + (3 : ℤ) • J - (3 : ℤ) • A := D.incidence_block_gram
  have hSS : S * S = (45 : ℤ) • S + (1584 : ℤ) • J := D.block_gram_square
  have hAJ : A * J = (45 : ℤ) • J := D.disjointness_mul_ones
  have hJA : J * A = (45 : ℤ) • J := D.ones_mul_disjointness
  have hJJ : J * J = (266 : ℤ) • J := by
    ext b c
    simp [J, Matrix.mul_apply, allOnesMatrix, D.index_card]
  have hscaled : (9 : ℤ) • (A * A) - (324 : ℤ) • 1 +
      (81 : ℤ) • A - (81 : ℤ) • J = 0 := by
    calc
      _ = S * S - (45 : ℤ) • S - (1584 : ℤ) • J := by
        rw [htarget]
        noncomm_ring [hAJ, hJA, hJJ]
      _ = 0 := by rw [hSS]; module
  ext b c
  have h := congrFun (congrFun hscaled b) c
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply,
    Matrix.add_apply, Matrix.zero_apply] at h ⊢
  change (A * A) b c = 36 * (1 : Matrix B B ℤ) b c - 9 * A b c + 9 * J b c
  omega

abbrev KreinVertex := Option (P ⊕ B)

def kreinAdj : KreinVertex (P := P) (B := B) → KreinVertex (P := P) (B := B) → Prop
  | none, some (Sum.inl _) => True
  | some (Sum.inl _), none => True
  | some (Sum.inl p), some (Sum.inr b) => p ∈ D.block b
  | some (Sum.inr b), some (Sum.inl p) => p ∈ D.block b
  | some (Sum.inr b), some (Sum.inr c) => (D.block b ∩ D.block c).card = 0
  | _, _ => False

def kreinGraph : SimpleGraph (KreinVertex (P := P) (B := B)) where
  Adj := D.kreinAdj
  symm := ⟨by
    rintro (_ | (p | b)) (_ | (q | c)) <;> simp [kreinAdj, Finset.inter_comm]⟩
  loopless := ⟨by rintro (_ | (p | b)) <;> simp [kreinAdj, D.block_size]⟩

instance : DecidableRel D.kreinGraph.Adj := by
  rintro (_ | (p | b)) (_ | (q | c)) <;>
    simp only [kreinGraph, kreinAdj] <;> infer_instance

def kreinMatrix : Matrix (KreinVertex (P := P) (B := B)) (KreinVertex (P := P) (B := B)) ℤ
  | none, some (Sum.inl _) => 1
  | some (Sum.inl _), none => 1
  | some (Sum.inl p), some (Sum.inr b) => D.incidence p b
  | some (Sum.inr b), some (Sum.inl p) => D.incidence p b
  | some (Sum.inr b), some (Sum.inr c) => D.disjointness b c
  | _, _ => 0

/--
@isnad1 id=eq.0h5v.s7.4276993578b0 from=translated src=- shape=15c7b1e9 vocab=a9005955
-/
theorem kreinMatrix_square_apply (x y : KreinVertex (P := P) (B := B)) :
    (D.kreinMatrix * D.kreinMatrix) x y =
      45 * (if x = y then 1 else 0) + 12 - 12 * D.kreinMatrix x y := by
  rw [Matrix.mul_apply, Fintype.sum_option, Fintype.sum_sum_type]
  rcases x with _ | (p | b) <;> rcases y with _ | (q | c)
  all_goals simp only [kreinMatrix, mul_zero, zero_mul, mul_one, one_mul,
    zero_add, add_zero, Finset.sum_const_zero]
  · simp [D.point_card]
  · simp
  · simpa using D.incidence_column_sum c
  · simp
  · have h := D.incidence_point_gram_apply p q
    simp only [Matrix.mul_apply, Matrix.transpose_apply] at h
    rw [h]
    by_cases hpq : p = q <;> simp [hpq]
  · have h := congrFun (congrFun D.incidence_mul_disjointness p) c
    simpa [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.sub_apply, allOnesMatrix, mul_sub] using h
  · simpa using D.incidence_column_sum b
  · have h := congrFun (congrFun D.incidence_mul_disjointness q) b
    simpa [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.sub_apply, allOnesMatrix, mul_sub, D.disjointness_comm b, mul_comm] using h
  · have hG := congrFun (congrFun D.incidence_block_gram b) c
    have hA := congrFun (congrFun D.disjointness_square b) c
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      smul_eq_mul, allOnesMatrix_apply, Matrix.one_apply, Matrix.mul_apply,
      Matrix.transpose_apply] at hG hA
    rw [hG, hA]
    by_cases hbc : b = c <;> simp [hbc] <;> ring

end SRG266.QuasiSymmetric.TripleDesign57

namespace SRG266.QuasiSymmetric.ConcreteQSD56

end SRG266.QuasiSymmetric.ConcreteQSD56
