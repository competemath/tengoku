/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.LocalGraph

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped Matrix

namespace SRG266

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def localGramMatrix (x : V) :
    Matrix (SecondSubconstituent G x) (SecondSubconstituent G x) ℤ :=
  fun B C =>
    (if B = C then 9 else 0) + 3 - localIntersectionMatrix G x B C -
      if (secondSubconstituentGraph G x).Adj B C then 3 else 0

/--
@isnad1 id=eq.0h5v.s5.883eef0a4cca from=translated src=- shape=2daeeee1 vocab=e421d614
-/
theorem blockIntersection_comm
    (x : V) (B C : SecondSubconstituent G x) :
    blockIntersection G x B C = blockIntersection G x C B := by
  simp [blockIntersection, Finset.inter_comm]

/--
@isnad1 id=eq.0h5v.s5.0e6119e49af0 from=translated src=- shape=2daeeee1 vocab=3962a965
-/
theorem localIntersectionMatrix_comm
    (x : V) (B C : SecondSubconstituent G x) :
    localIntersectionMatrix G x B C = localIntersectionMatrix G x C B := by
  rw [localIntersectionMatrix_apply, localIntersectionMatrix_apply,
    blockIntersection_comm G x B C]

/--
@isnad1 id=eq.0h5v.s5.5678314b50bd from=translated src=- shape=2daeeee1 vocab=7fa6388d
-/
theorem localGramMatrix_comm
    (x : V) (B C : SecondSubconstituent G x) :
    localGramMatrix G x B C = localGramMatrix G x C B := by
  rw [localGramMatrix, localGramMatrix, localIntersectionMatrix_comm G x B C]
  simp only [eq_comm, SimpleGraph.adj_comm]

/--
@isnad1 id=issymm.0h3v.s5.f2c279055a13 from=translated src=- shape=9bbb9fae vocab=f7d00b9d
-/
theorem localGramMatrix_isSymm (x : V) :
    (localGramMatrix G x).IsSymm :=
  Matrix.IsSymm.ext fun B C => (localGramMatrix_comm G x B C).symm

/--
@isnad1 id=eq.1h4v.s5.e0d7419e2441 from=translated src=- shape=de33ca30 vocab=80742f4f
-/
@[simp]
theorem localGramMatrix_diagonal
    (hG : IsHypothetical G) (x : V) (B : SecondSubconstituent G x) :
    localGramMatrix G x B B = 3 := by
  simp [localGramMatrix, localIntersectionMatrix_diagonal G hG x B]

/--
@isnad1 id=eq.2h5v.s6.2d8d15fe6b25 from=translated src=- shape=d34ac22b vocab=38a41d82
-/
theorem localGramMatrix_of_adj
    (hG : IsHypothetical G) (x : V)
    {B C : SecondSubconstituent G x}
    (hBC : (secondSubconstituentGraph G x).Adj B C) :
    localGramMatrix G x B C = 0 := by
  have hne : B ≠ C := (secondSubconstituentGraph G x).ne_of_adj hBC
  have hGBC : G.Adj (B : V) (C : V) := hBC
  simp [localGramMatrix, hne, hGBC, localIntersectionMatrix_of_adj G hG x hBC]

/--
@isnad1 id=eq.2h5v.s6.2d3ec6291e9d from=translated src=- shape=37d7d773 vocab=57ce4a86
-/
theorem localGramMatrix_of_not_adj
    (x : V) {B C : SecondSubconstituent G x}
    (hne : B ≠ C) (hBC : ¬(secondSubconstituentGraph G x).Adj B C) :
    localGramMatrix G x B C = 3 - (blockIntersection G x B C : ℤ) := by
  have hGBC : ¬G.Adj (B : V) (C : V) := hBC
  simp [localGramMatrix, hne, hGBC, localIntersectionMatrix_apply]

/--
@isnad1 id=eq.2h5v.s7.1ab33f5d738f from=translated src=- shape=9f94b638 vocab=500fe335
-/
theorem localGramMatrix_off_diagonal
    (hG : IsHypothetical G) (x : V)
    {B C : SecondSubconstituent G x} (hne : B ≠ C) :
    localGramMatrix G x B C =
      if (secondSubconstituentGraph G x).Adj B C then 0
      else 3 - (blockIntersection G x B C : ℤ) := by
  by_cases hBC : (secondSubconstituentGraph G x).Adj B C
  · rw [ite_eq_left hBC, localGramMatrix_of_adj G hG x hBC]
  · rw [ite_eq_right hBC, localGramMatrix_of_not_adj G x hne hBC]

/--
@isnad1 id=eq.1h4v.s6.beaba1b3ebb7 from=translated src=- shape=2d7bc580 vocab=cf103914
-/
theorem localGramMatrix_row_sum
    (hG : IsHypothetical G) (x : V) (B : SecondSubconstituent G x) :
    ∑ C, localGramMatrix G x B C = 165 := by
  have hdiag : (∑ C : SecondSubconstituent G x,
      if B = C then (9 : ℤ) else 0) = 9 := by
    simp
  have hconst : (∑ _C : SecondSubconstituent G x, (3 : ℤ)) = 660 := by
    simp [secondSubconstituent_card G hG x]
  have hS : (∑ C, localIntersectionMatrix G x B C) = 396 := by
    have h := congrFun (localIntersectionMatrix_mulVec_one G hG x) B
    simpa [Matrix.mulVec_apply_eq_sum] using h
  have hHrow : (∑ C, localAdjacencyMatrix G x B C) = 36 := by
    have h := congrFun (localAdjacencyMatrix_mulVec_one G hG x) B
    simpa [Matrix.mulVec_apply_eq_sum] using h
  have hH : (∑ C : SecondSubconstituent G x,
      if (secondSubconstituentGraph G x).Adj B C then (3 : ℤ) else 0) = 108 := by
    calc
      (∑ C : SecondSubconstituent G x,
          if (secondSubconstituentGraph G x).Adj B C then (3 : ℤ) else 0) =
          3 * ∑ C, localAdjacencyMatrix G x B C := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro C _
        by_cases hBC : (secondSubconstituentGraph G x).Adj B C <;>
          simp [localAdjacencyMatrix]
      _ = 108 := by rw [hHrow]; norm_num
  change (∑ C, ((if B = C then (9 : ℤ) else 0) + 3 -
    localIntersectionMatrix G x B C -
    if (secondSubconstituentGraph G x).Adj B C then 3 else 0)) = 165
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    hdiag, hconst, hS, hH]
  norm_num

/--
@isnad1 id=eq.1h3v.s7.cbc087f815e9 from=translated src=- shape=cd9c03c9 vocab=c610237f
-/
@[simp]
theorem localGramMatrix_mulVec_one
    (hG : IsHypothetical G) (x : V) :
    localGramMatrix G x *ᵥ (1 : SecondSubconstituent G x → ℤ) = 165 := by
  funext B
  rw [Matrix.mulVec_apply_eq_sum]
  simp only [Pi.one_apply, mul_one]
  exact localGramMatrix_row_sum G hG x B

def localKMatrix (x : V) :
    Matrix (SecondSubconstituent G x) (SecondSubconstituent G x) ℤ :=
  fun B C => localGramMatrix G x B C - 1

/--
@isnad1 id=eq.1h4v.s5.3be4fdd68d62 from=translated src=- shape=de33ca30 vocab=2be25f72
-/
@[simp]
theorem localKMatrix_diagonal
    (hG : IsHypothetical G) (x : V) (B : SecondSubconstituent G x) :
    localKMatrix G x B B = 2 := by
  simp [localKMatrix, localGramMatrix_diagonal G hG x B]

/--
@isnad1 id=eq.2h5v.s6.6ebc2a3bb3fb from=translated src=- shape=5de8a2fa vocab=b896b5e9
-/
theorem localKMatrix_of_adj
    (hG : IsHypothetical G) (x : V)
    {B C : SecondSubconstituent G x}
    (hBC : (secondSubconstituentGraph G x).Adj B C) :
    localKMatrix G x B C = -1 := by
  rw [localKMatrix, localGramMatrix_of_adj G hG x hBC]
  norm_num

/--
@isnad1 id=eq.2h5v.s6.607cc8aad317 from=translated src=- shape=37d7d773 vocab=7f8e43c0
-/
theorem localKMatrix_of_not_adj
    (x : V) {B C : SecondSubconstituent G x}
    (hne : B ≠ C) (hBC : ¬(secondSubconstituentGraph G x).Adj B C) :
    localKMatrix G x B C = 2 - (blockIntersection G x B C : ℤ) := by
  rw [localKMatrix, localGramMatrix_of_not_adj G x hne hBC]
  ring

/--
@isnad1 id=eq.1h4v.s6.bb264445953d from=translated src=- shape=d7bb87a7 vocab=7ddafc1e
-/
theorem localKMatrix_row_sum
    (hG : IsHypothetical G) (x : V) (B : SecondSubconstituent G x) :
    ∑ C, localKMatrix G x B C = -55 := by
  simp only [localKMatrix]
  rw [Finset.sum_sub_distrib, localGramMatrix_row_sum G hG x B]
  simp [secondSubconstituent_card G hG x]

/--
@isnad1 id=eq.1h3v.s7.148c90570c0e from=translated src=- shape=ebd9d348 vocab=29e2f293
-/
@[simp]
theorem localKMatrix_mulVec_one
    (hG : IsHypothetical G) (x : V) :
    localKMatrix G x *ᵥ (1 : SecondSubconstituent G x → ℤ) = -55 := by
  funext B
  rw [Matrix.mulVec_apply_eq_sum]
  simp only [Pi.one_apply, mul_one]
  exact localKMatrix_row_sum G hG x B

end SRG266
