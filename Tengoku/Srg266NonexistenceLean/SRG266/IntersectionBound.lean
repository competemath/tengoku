/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Projector

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped Matrix

namespace SRG266

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/--
@isnad1 id=eq.0h5v.s5.f496806c4482 from=translated src=- shape=2daeeee1 vocab=ec1106a4
-/
theorem localKMatrix_comm
    (x : V) (B C : SecondSubconstituent G x) :
    localKMatrix G x B C = localKMatrix G x C B := by
  simp only [localKMatrix]
  rw [localGramMatrix_comm G x B C]

/--
@isnad1 id=eq.0h3v.s7.c27ccb3c82a6 from=translated src=- shape=30c2c3d5 vocab=41cf5a44
-/
theorem localKMatrix_eq_linear_combination
    (x : V) :
    localKMatrix G x =
      localGramMatrix G x -
        (allOnesMatrix :
          Matrix (SecondSubconstituent G x)
            (SecondSubconstituent G x) ℤ) := by
  ext B C
  simp [localKMatrix]

/--
@isnad1 id=eq.1h3v.s8.630052f7a8c7 from=translated src=- shape=e922a337 vocab=9b1d7ac8
-/
theorem localKMatrix_sq
    (hG : IsHypothetical G) (x : V) :
    localKMatrix G x * localKMatrix G x =
      (45 : ℕ) • localKMatrix G x +
        (25 : ℕ) •
          (allOnesMatrix :
            Matrix (SecondSubconstituent G x)
              (SecondSubconstituent G x) ℤ) := by
  let J :
      Matrix (SecondSubconstituent G x) (SecondSubconstituent G x) ℤ :=
    allOnesMatrix
  let L := localGramMatrix G x
  let K := localKMatrix G x
  have hK : K = L - J := by
    simpa [K, L, J] using localKMatrix_eq_linear_combination G x
  have hLL : L * L = (45 : ℕ) • L + (90 : ℕ) • J := by
    simpa [L, J] using localGramMatrix_sq G hG x
  have hLJ : L * J = (165 : ℕ) • J := by
    simpa [L, J] using localGram_mul_allOnes G hG x
  have hJL : J * L = (165 : ℕ) • J := by
    simpa [L, J] using allOnes_mul_localGram G hG x
  have hJJ : J * J = (220 : ℕ) • J := by
    simpa [J] using allOnesMatrix_sq G hG x
  change K * K = (45 : ℕ) • K + (25 : ℕ) • J
  rw [hK]
  calc
    (L - J) * (L - J) = L * L - (L * J + J * L) + J * J := by
      noncomm_ring
    _ = (45 : ℕ) • (L - J) + (25 : ℕ) • J := by
      rw [hLL, hLJ, hJL, hJJ]
      noncomm_ring

/--
@isnad1 id=eq.1h5v.s7.7f6582f78057 from=translated src=- shape=4e49b031 vocab=41fb3ec0
-/
theorem localKMatrix_sq_apply
    (hG : IsHypothetical G) (x : V)
    (B C : SecondSubconstituent G x) :
    (localKMatrix G x * localKMatrix G x) B C =
      45 * localKMatrix G x B C + 25 := by
  have h := congrFun (congrFun (localKMatrix_sq G hG x) B) C
  change
    (localKMatrix G x * localKMatrix G x) B C =
      ((45 : ℕ) • localKMatrix G x) B C +
        ((25 : ℕ) •
          (allOnesMatrix :
            Matrix (SecondSubconstituent G x)
              (SecondSubconstituent G x) ℤ)) B C at h
  rw [nsmulMatrix_apply, nsmulMatrix_apply] at h
  simpa using h

def integerPotential (z : ℤ) : ℤ :=
  z * (z + 1) / 2

/--
@isnad1 id=eq.0h1v.s5.1c408a58def0 from=translated src=- shape=b5988a5f vocab=b9f7814c
-/
theorem two_mul_integerPotential (z : ℤ) :
    2 * integerPotential z = z * z + z := by
  have hdiv := Int.ediv_mul_cancel (Int.two_dvd_mul_add_one z)
  rw [integerPotential, mul_comm 2]
  calc
    z * (z + 1) / 2 * 2 = z * (z + 1) := hdiv
    _ = z * z + z := by ring

/--
@isnad1 id=le.4h2v.s6.a1d42372b2fe from=translated src=- shape=d686ce17 vocab=6218ce40
-/
theorem integerPotential_pair_nonneg
    {a b : ℤ}
    (haLower : -2 ≤ a) (haUpper : a ≤ 2)
    (hbLower : -2 ≤ b) (hbUpper : b ≤ 2) :
    0 ≤ integerPotential a + integerPotential b + a * b := by
  interval_cases a <;> interval_cases b <;>
    norm_num [integerPotential]

/--
@isnad1 id=and.2h5v.s6.a5b034c59068 from=translated src=- shape=b83138eb vocab=bcdf6b3b
-/
theorem localKMatrix_bounds
    (hG : IsHypothetical G) (x : V)
    {B C : SecondSubconstituent G x}
    (hne : B ≠ C) :
    -2 ≤ localKMatrix G x B C ∧ localKMatrix G x B C ≤ 2 := by
  by_cases hBC : (secondSubconstituentGraph G x).Adj B C
  · rw [localKMatrix_of_adj G hG x hBC]
    norm_num
  · rw [localKMatrix_of_not_adj G x hne hBC]
    have hcap := blockIntersection_le_four G hG x hne
    have hnonneg : 0 ≤ (blockIntersection G x B C : ℤ) := by positivity
    constructor <;> omega

/--
@isnad1 id=le.3h6v.s7.0ffefdbc9073 from=translated src=- shape=aee7322f vocab=d6e5f876
-/
theorem localPotentialSummand_nonneg
    (hG : IsHypothetical G) (x : V)
    {B C D : SecondSubconstituent G x}
    (hBD : B ≠ D) (hCD : C ≠ D) :
    0 ≤
      integerPotential (localKMatrix G x B D) +
        integerPotential (localKMatrix G x C D) +
        localKMatrix G x B D * localKMatrix G x C D -
        localAdjacencyMatrix G x B D * localAdjacencyMatrix G x D C := by
  by_cases hDB : (secondSubconstituentGraph G x).Adj D B
  · by_cases hDC : (secondSubconstituentGraph G x).Adj D C
    · have hBDadj : (secondSubconstituentGraph G x).Adj B D := hDB.symm
      have hCDadj : (secondSubconstituentGraph G x).Adj C D := hDC.symm
      have hGDB : G.Adj (D : V) (B : V) := hDB
      have hGDC : G.Adj (D : V) (C : V) := hDC
      have hGBD : G.Adj (B : V) (D : V) := hGDB.symm
      have hHprod :
          localAdjacencyMatrix G x B D * localAdjacencyMatrix G x D C = 1 := by
        simp [localAdjacencyMatrix, hGBD, hGDC]
      rw [localKMatrix_of_adj G hG x hBDadj,
        localKMatrix_of_adj G hG x hCDadj, hHprod]
      norm_num [integerPotential]
    · have hzero :
          localAdjacencyMatrix G x B D * localAdjacencyMatrix G x D C = 0 := by
        have hGDC : ¬G.Adj (D : V) (C : V) := hDC
        simp [localAdjacencyMatrix, hGDC]
      rw [hzero, sub_zero]
      exact integerPotential_pair_nonneg
        (localKMatrix_bounds G hG x hBD).1
        (localKMatrix_bounds G hG x hBD).2
        (localKMatrix_bounds G hG x hCD).1
        (localKMatrix_bounds G hG x hCD).2
  · have hzero :
        localAdjacencyMatrix G x B D * localAdjacencyMatrix G x D C = 0 := by
      have hGDB : ¬G.Adj (D : V) (B : V) := hDB
      have hGBD : ¬G.Adj (B : V) (D : V) := fun h => hGDB h.symm
      simp [localAdjacencyMatrix, hGBD]
    rw [hzero, sub_zero]
    exact integerPotential_pair_nonneg
      (localKMatrix_bounds G hG x hBD).1
      (localKMatrix_bounds G hG x hBD).2
      (localKMatrix_bounds G hG x hCD).1
      (localKMatrix_bounds G hG x hCD).2

def otherLocalIndices
    (x : V) (B C : SecondSubconstituent G x) :
    Finset (SecondSubconstituent G x) :=
  (Finset.univ.erase B).erase C

/--
@isnad1 id=iff.0h6v.s6.55588e662002 from=translated src=- shape=41b8aab7 vocab=70c5eac9
-/
@[simp]
theorem mem_otherLocalIndices
    (x : V) (B C D : SecondSubconstituent G x) :
    D ∈ otherLocalIndices G x B C ↔ D ≠ B ∧ D ≠ C := by
  simp [otherLocalIndices, and_comm]

/--
@isnad1 id=eq.1h6v.s7.bb27cc356d4f from=translated src=- shape=2a35b365 vocab=764dfc79
-/
theorem sum_otherLocalIndices
    (x : V) {B C : SecondSubconstituent G x}
    (hne : B ≠ C)
    (f : SecondSubconstituent G x → ℤ) :
    ∑ D ∈ otherLocalIndices G x B C, f D =
      (∑ D, f D) - f B - f C := by
  rw [otherLocalIndices,
    Finset.sum_erase_eq_sub (by simp [hne.symm]),
    Finset.sum_erase_eq_sub (by simp)]

/--
@isnad1 id=eq.1h4v.s6.5930a0483bab from=translated src=- shape=e54718eb vocab=e648a274
-/
theorem sum_localKMatrix_sq
    (hG : IsHypothetical G) (x : V)
    (B : SecondSubconstituent G x) :
    ∑ D, localKMatrix G x B D * localKMatrix G x B D = 115 := by
  calc
    (∑ D, localKMatrix G x B D * localKMatrix G x B D) =
        (localKMatrix G x * localKMatrix G x) B B := by
      rw [Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro D _
      rw [localKMatrix_comm G x D B]
    _ = 45 * localKMatrix G x B B + 25 :=
      localKMatrix_sq_apply G hG x B B
    _ = 115 := by
      rw [localKMatrix_diagonal G hG x B]
      norm_num

/--
@isnad1 id=eq.1h4v.s6.b0ddca6469d9 from=translated src=- shape=3c93e0db vocab=4c6fea7a
-/
theorem sum_integerPotential_localKMatrix
    (hG : IsHypothetical G) (x : V)
    (B : SecondSubconstituent G x) :
    ∑ D, integerPotential (localKMatrix G x B D) = 30 := by
  have htwice :
      2 * (∑ D, integerPotential (localKMatrix G x B D)) =
        ∑ D, (localKMatrix G x B D * localKMatrix G x B D +
          localKMatrix G x B D) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro D _
    exact two_mul_integerPotential (localKMatrix G x B D)
  rw [Finset.sum_add_distrib, sum_localKMatrix_sq G hG x B,
    localKMatrix_row_sum G hG x B] at htwice
  omega

/--
@isnad1 id=eq.3h5v.s6.338fdd726414 from=translated src=- shape=92d59fe2 vocab=3b6f1db1
-/
theorem localKMatrix_eq_neg_two_of_intersection_four
    (x : V) {B C : SecondSubconstituent G x}
    (hne : B ≠ C)
    (hBC : ¬(secondSubconstituentGraph G x).Adj B C)
    (hinter : blockIntersection G x B C = 4) :
    localKMatrix G x B C = -2 := by
  rw [localKMatrix_of_not_adj G x hne hBC, hinter]
  norm_num

/--
@isnad1 id=eq.4h5v.s6.a3ac9ac4bbbd from=translated src=- shape=c7eddffe vocab=fea68f60
-/
theorem sum_other_integerPotential_eq_twenty_six
    (hG : IsHypothetical G) (x : V)
    {B C : SecondSubconstituent G x}
    (hne : B ≠ C)
    (hBC : ¬(secondSubconstituentGraph G x).Adj B C)
    (hinter : blockIntersection G x B C = 4) :
    ∑ D ∈ otherLocalIndices G x B C,
        integerPotential (localKMatrix G x B D) = 26 := by
  rw [sum_otherLocalIndices G x hne,
    sum_integerPotential_localKMatrix G hG x B,
    localKMatrix_diagonal G hG x B,
    localKMatrix_eq_neg_two_of_intersection_four G x hne hBC hinter]
  norm_num [integerPotential]

/--
@isnad1 id=eq.4h5v.s6.876273042aba from=translated src=- shape=12e01e74 vocab=fea68f60
-/
theorem sum_other_integerPotential_symm_eq_twenty_six
    (hG : IsHypothetical G) (x : V)
    {B C : SecondSubconstituent G x}
    (hne : B ≠ C)
    (hBC : ¬(secondSubconstituentGraph G x).Adj B C)
    (hinter : blockIntersection G x B C = 4) :
    ∑ D ∈ otherLocalIndices G x B C,
        integerPotential (localKMatrix G x C D) = 26 := by
  rw [sum_otherLocalIndices G x hne,
    sum_integerPotential_localKMatrix G hG x C]
  have hCB : ¬(secondSubconstituentGraph G x).Adj C B := by
    simpa [SimpleGraph.adj_comm] using hBC
  have hinterCB : blockIntersection G x C B = 4 := by
    rw [blockIntersection_comm G x C B, hinter]
  rw [localKMatrix_eq_neg_two_of_intersection_four G x hne.symm hCB hinterCB,
    localKMatrix_diagonal G hG x C]
  norm_num [integerPotential]

/--
@isnad1 id=eq.4h5v.s7.6dc787c58612 from=translated src=- shape=f99674a1 vocab=aaa6416a
-/
theorem sum_other_localKMatrix_product_eq_neg_fifty_seven
    (hG : IsHypothetical G) (x : V)
    {B C : SecondSubconstituent G x}
    (hne : B ≠ C)
    (hBC : ¬(secondSubconstituentGraph G x).Adj B C)
    (hinter : blockIntersection G x B C = 4) :
    ∑ D ∈ otherLocalIndices G x B C,
        localKMatrix G x B D * localKMatrix G x C D = -57 := by
  have hKBC :
      localKMatrix G x B C = -2 :=
    localKMatrix_eq_neg_two_of_intersection_four G x hne hBC hinter
  have hfull :
      (∑ D, localKMatrix G x B D * localKMatrix G x C D) = -65 := by
    calc
      (∑ D, localKMatrix G x B D * localKMatrix G x C D) =
          (localKMatrix G x * localKMatrix G x) B C := by
        rw [Matrix.mul_apply]
        apply Finset.sum_congr rfl
        intro D _
        rw [localKMatrix_comm G x D C]
      _ = 45 * localKMatrix G x B C + 25 :=
        localKMatrix_sq_apply G hG x B C
      _ = -65 := by rw [hKBC]; norm_num
  rw [sum_otherLocalIndices G x hne, hfull,
    localKMatrix_diagonal G hG x B,
    localKMatrix_diagonal G hG x C,
    localKMatrix_comm G x C B, hKBC]
  norm_num

/--
@isnad1 id=eq.4h5v.s7.1ce96cb875fb from=translated src=- shape=cbece5c3 vocab=aa8d8c06
-/
theorem sum_other_localAdjacencyMatrix_product_eq_five
    (hG : IsHypothetical G) (x : V)
    {B C : SecondSubconstituent G x}
    (hne : B ≠ C)
    (hBC : ¬(secondSubconstituentGraph G x).Adj B C)
    (hinter : blockIntersection G x B C = 4) :
    ∑ D ∈ otherLocalIndices G x B C,
        localAdjacencyMatrix G x B D * localAdjacencyMatrix G x D C = 5 := by
  have hfull :
      (∑ D,
        localAdjacencyMatrix G x B D * localAdjacencyMatrix G x D C) = 5 := by
    calc
      (∑ D,
          localAdjacencyMatrix G x B D * localAdjacencyMatrix G x D C) =
          (localAdjacencyMatrix G x * localAdjacencyMatrix G x) B C := by
        rw [Matrix.mul_apply]
      _ = if B = C then 36
          else if (secondSubconstituentGraph G x).Adj B C then 0
          else 9 - (blockIntersection G x B C : ℤ) :=
        localAdjacencyMatrix_sq_apply G hG x B C
      _ = 5 := by
        rw [ite_eq_right hne, ite_eq_right hBC, hinter]
        norm_num
  rw [sum_otherLocalIndices G x hne, hfull]
  have hBB : localAdjacencyMatrix G x B B = 0 := by
    simp [localAdjacencyMatrix]
  have hCC : localAdjacencyMatrix G x C C = 0 := by
    simp [localAdjacencyMatrix]
  rw [hBB, hCC]
  norm_num

/--
@isnad1 id=eq.4h5v.s7.2a1c68872d5f from=translated src=- shape=5028a2cb vocab=118148ca
-/
theorem sum_other_localPotentialSummand_eq_neg_ten
    (hG : IsHypothetical G) (x : V)
    {B C : SecondSubconstituent G x}
    (hne : B ≠ C)
    (hBC : ¬(secondSubconstituentGraph G x).Adj B C)
    (hinter : blockIntersection G x B C = 4) :
    ∑ D ∈ otherLocalIndices G x B C,
        (integerPotential (localKMatrix G x B D) +
          integerPotential (localKMatrix G x C D) +
          localKMatrix G x B D * localKMatrix G x C D -
          localAdjacencyMatrix G x B D * localAdjacencyMatrix G x D C) =
      -10 := by
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib,
    sum_other_integerPotential_eq_twenty_six G hG x hne hBC hinter,
    sum_other_integerPotential_symm_eq_twenty_six G hG x hne hBC hinter,
    sum_other_localKMatrix_product_eq_neg_fifty_seven G hG x hne hBC hinter,
    sum_other_localAdjacencyMatrix_product_eq_five G hG x hne hBC hinter]
  norm_num

/--
@isnad1 id=ne.2h5v.s6.2ef8d4e0853b from=translated src=- shape=6332221a vocab=3ab2de47
-/
theorem blockIntersection_ne_four
    (hG : IsHypothetical G) (x : V)
    {B C : SecondSubconstituent G x}
    (hne : B ≠ C) :
    blockIntersection G x B C ≠ 4 := by
  intro hinter
  have hBC : ¬(secondSubconstituentGraph G x).Adj B C := by
    intro hadj
    have hzero := blockIntersection_of_adj G hG x hadj
    omega
  have hnonneg :
      0 ≤ ∑ D ∈ otherLocalIndices G x B C,
        (integerPotential (localKMatrix G x B D) +
          integerPotential (localKMatrix G x C D) +
          localKMatrix G x B D * localKMatrix G x C D -
          localAdjacencyMatrix G x B D * localAdjacencyMatrix G x D C) := by
    apply Finset.sum_nonneg
    intro D hD
    rw [mem_otherLocalIndices] at hD
    exact localPotentialSummand_nonneg G hG x hD.1.symm hD.2.symm
  rw [sum_other_localPotentialSummand_eq_neg_ten G hG x hne hBC hinter] at hnonneg
  omega

/--
@isnad1 id=le.2h5v.s6.f97120f40355 from=translated src=- shape=99746e7e vocab=58103005
-/
theorem blockIntersection_le_three
    (hG : IsHypothetical G) (x : V)
    {B C : SecondSubconstituent G x}
    (hne : B ≠ C) :
    blockIntersection G x B C ≤ 3 := by
  have hcap := blockIntersection_le_four G hG x hne
  have hneFour := blockIntersection_ne_four G hG x hne
  omega

/--
@isnad1 id=and.1h5v.s6.e0577c62d600 from=translated src=- shape=e4fa9e12 vocab=717dde6a
-/
theorem localGramMatrix_bounds
    (hG : IsHypothetical G) (x : V)
    (B C : SecondSubconstituent G x) :
    0 ≤ localGramMatrix G x B C ∧ localGramMatrix G x B C ≤ 3 := by
  by_cases hEq : B = C
  · subst C
    rw [localGramMatrix_diagonal G hG x B]
    norm_num
  · by_cases hBC : (secondSubconstituentGraph G x).Adj B C
    · rw [localGramMatrix_of_adj G hG x hBC]
      norm_num
    · rw [localGramMatrix_of_not_adj G x hEq hBC]
      have hcap := blockIntersection_le_three G hG x hEq
      have hnonneg : 0 ≤ (blockIntersection G x B C : ℤ) := by positivity
      constructor <;> omega

/--
@isnad1 id=or.1h5v.s6.1e971de2b26f from=translated src=- shape=b319a3c8 vocab=80742f4f
-/
theorem localGramMatrix_entry_cases
    (hG : IsHypothetical G) (x : V)
    (B C : SecondSubconstituent G x) :
    localGramMatrix G x B C = 0 ∨
      localGramMatrix G x B C = 1 ∨
      localGramMatrix G x B C = 2 ∨
      localGramMatrix G x B C = 3 := by
  have hbounds := localGramMatrix_bounds G hG x B C
  omega

end SRG266
