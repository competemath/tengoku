/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.LocalSpectrum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped Matrix

namespace SRG266

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def GramEquivalent (x : V)
    (B C : SecondSubconstituent G x) : Prop :=
  ∀ D, localGramMatrix G x B D = localGramMatrix G x C D

/--
@isnad1 id=gramequi.0h4v.s5.e8a28d2d54bb from=translated src=- shape=a7581b69 vocab=5780df33
-/
@[refl]
theorem GramEquivalent.refl (x : V)
    (B : SecondSubconstituent G x) :
    GramEquivalent G x B B :=
  fun _ => rfl

/--
@isnad1 id=gramequi.1h5v.s5.32732c59b802 from=translated src=- shape=b9d2a78b vocab=5780df33
-/
@[symm]
theorem GramEquivalent.symm (x : V)
    {B C : SecondSubconstituent G x}
    (h : GramEquivalent G x B C) :
    GramEquivalent G x C B :=
  fun D => (h D).symm

/--
@isnad1 id=gramequi.2h6v.s6.aa773205ae8b from=translated src=- shape=06156a4e vocab=5780df33
-/
@[trans]
theorem GramEquivalent.trans (x : V)
    {B C D : SecondSubconstituent G x}
    (hBC : GramEquivalent G x B C)
    (hCD : GramEquivalent G x C D) :
    GramEquivalent G x B D :=
  fun E => (hBC E).trans (hCD E)

/--
@isnad1 id=iff.1h5v.s6.09b83af1c42b from=translated src=- shape=dacfd7c8 vocab=39759e17
-/
theorem gramEquivalent_iff_entry_eq_three
    (hG : IsHypothetical G) (x : V)
    (B C : SecondSubconstituent G x) :
    GramEquivalent G x B C ↔ localGramMatrix G x B C = 3 := by
  constructor
  · intro h
    calc
      localGramMatrix G x B C = localGramMatrix G x C C := h C
      _ = 3 := localGramMatrix_diagonal G hG x C
  · intro hBC D
    have hBB :
        ∑ E, localGramMatrix G x B E * localGramMatrix G x B E = 225 := by
      calc
        (∑ E, localGramMatrix G x B E * localGramMatrix G x B E) =
            (localGramMatrix G x * localGramMatrix G x) B B := by
          rw [Matrix.mul_apply]
          apply Finset.sum_congr rfl
          intro E _
          rw [localGramMatrix_comm G x E B]
        _ = 45 * localGramMatrix G x B B + 90 :=
          localGramMatrix_sq_apply G hG x B B
        _ = 225 := by rw [localGramMatrix_diagonal G hG x B]; norm_num
    have hCC :
        ∑ E, localGramMatrix G x C E * localGramMatrix G x C E = 225 := by
      calc
        (∑ E, localGramMatrix G x C E * localGramMatrix G x C E) =
            (localGramMatrix G x * localGramMatrix G x) C C := by
          rw [Matrix.mul_apply]
          apply Finset.sum_congr rfl
          intro E _
          rw [localGramMatrix_comm G x E C]
        _ = 45 * localGramMatrix G x C C + 90 :=
          localGramMatrix_sq_apply G hG x C C
        _ = 225 := by rw [localGramMatrix_diagonal G hG x C]; norm_num
    have hBCsum :
        ∑ E, localGramMatrix G x B E * localGramMatrix G x C E = 225 := by
      calc
        (∑ E, localGramMatrix G x B E * localGramMatrix G x C E) =
            (localGramMatrix G x * localGramMatrix G x) B C := by
          rw [Matrix.mul_apply]
          apply Finset.sum_congr rfl
          intro E _
          rw [localGramMatrix_comm G x E C]
        _ = 45 * localGramMatrix G x B C + 90 :=
          localGramMatrix_sq_apply G hG x B C
        _ = 225 := by rw [hBC]; norm_num
    have hsum :
        ∑ E, (localGramMatrix G x B E - localGramMatrix G x C E) ^ 2 = 0 := by
      calc
        (∑ E, (localGramMatrix G x B E -
            localGramMatrix G x C E) ^ 2) =
            (∑ E, localGramMatrix G x B E * localGramMatrix G x B E) +
              (∑ E, localGramMatrix G x C E * localGramMatrix G x C E) -
              2 * (∑ E,
                localGramMatrix G x B E * localGramMatrix G x C E) := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib,
            ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro E _
          ring
        _ = 0 := by rw [hBB, hCC, hBCsum]; norm_num
    have hzero :
        (localGramMatrix G x B D - localGramMatrix G x C D) ^ 2 = 0 := by
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun E (_ : E ∈ (Finset.univ :
          Finset (SecondSubconstituent G x))) =>
          sq_nonneg (localGramMatrix G x B E -
            localGramMatrix G x C E))).mp hsum D (Finset.mem_univ D)
    nlinarith [sq_nonneg
      (localGramMatrix G x B D - localGramMatrix G x C D)]

noncomputable def gramClass (x : V) (B : SecondSubconstituent G x) :
    Finset (SecondSubconstituent G x) := by
  classical
  exact Finset.univ.filter fun C => GramEquivalent G x B C

/--
@isnad1 id=iff.0h5v.s6.da846b287c38 from=translated src=- shape=6906c8cb vocab=88901e32
-/
@[simp]
theorem mem_gramClass (x : V)
    (B C : SecondSubconstituent G x) :
    C ∈ gramClass G x B ↔ GramEquivalent G x B C := by
  classical
  simp [gramClass]

/--
@isnad1 id=mem.0h4v.s6.546ab806783d from=translated src=- shape=87124066 vocab=31a0aa2d
-/
@[simp]
theorem mem_gramClass_self (x : V)
    (B : SecondSubconstituent G x) :
    B ∈ gramClass G x B := by
  rw [mem_gramClass]

/--
@isnad1 id=gramequi.2h6v.s7.823ccab7a9cb from=translated src=- shape=23632e4e vocab=88901e32
-/
theorem gramEquivalent_of_mem_gramClass
    (x : V) (B : SecondSubconstituent G x)
    {C D : SecondSubconstituent G x}
    (hC : C ∈ gramClass G x B)
    (hD : D ∈ gramClass G x B) :
    GramEquivalent G x C D :=
  GramEquivalent.trans G x
    (GramEquivalent.symm G x ((mem_gramClass G x B C).mp hC))
    ((mem_gramClass G x B D).mp hD)

/--
@isnad1 id=disjoint.3h5v.s6.6a81e739e7e8 from=translated src=- shape=9d1ed10c vocab=6068315a
-/
theorem localBlocks_disjoint_of_gramEquivalent
    (hG : IsHypothetical G) (x : V)
    {B C : SecondSubconstituent G x}
    (hne : B ≠ C) (hEq : GramEquivalent G x B C) :
    Disjoint (localBlock G x B) (localBlock G x C) := by
  have hentry :
      localGramMatrix G x B C = 3 :=
    (gramEquivalent_iff_entry_eq_three G hG x B C).mp hEq
  have hnotadj : ¬(secondSubconstituentGraph G x).Adj B C := by
    intro hadj
    have hzero := localGramMatrix_of_adj G hG x hadj
    omega
  have hinter :
      blockIntersection G x B C = 0 := by
    have hformula := localGramMatrix_of_not_adj G x hne hnotadj
    have hcast : (blockIntersection G x B C : ℤ) = 0 := by omega
    exact_mod_cast hcast
  rw [Finset.disjoint_iff_inter_eq_empty]
  exact Finset.card_eq_zero.mp (by simpa [blockIntersection] using hinter)

/--
@isnad1 id=pairwise.1h4v.s6.3c6945c15b42 from=translated src=- shape=e256a7ba vocab=a30b0ff6
-/
theorem gramClass_pairwiseDisjoint
    (hG : IsHypothetical G) (x : V)
    (B : SecondSubconstituent G x) :
    ((gramClass G x B : Finset (SecondSubconstituent G x)) :
      Set (SecondSubconstituent G x)).PairwiseDisjoint (localBlock G x) := by
  intro C hC D hD hne
  exact localBlocks_disjoint_of_gramEquivalent G hG x hne
    (gramEquivalent_of_mem_gramClass G x B hC hD)

/--
@isnad1 id=le.1h4v.s5.290d68662562 from=translated src=- shape=0d3167f8 vocab=94b50484
-/
theorem gramClass_card_le_five
    (hG : IsHypothetical G) (x : V)
    (B : SecondSubconstituent G x) :
    (gramClass G x B).card ≤ 5 := by
  classical
  have hcard :=
    Finset.card_biUnion (gramClass_pairwiseDisjoint G hG x B)
  have hsum :
      ∑ C ∈ gramClass G x B, (localBlock G x C).card =
        (gramClass G x B).card * 9 := by
    exact Finset.sum_const_nat fun C _ => localBlock_card G hG x C
  have hunion :
      ((gramClass G x B).biUnion (localBlock G x)).card ≤ 45 := by
    calc
      ((gramClass G x B).biUnion (localBlock G x)).card ≤
          Fintype.card (FirstSubconstituent G x) :=
        Finset.card_le_univ _
      _ = 45 := firstSubconstituent_card G hG x
  rw [hcard, hsum] at hunion
  omega

noncomputable def zeroGramIndices (x : V)
    (B : SecondSubconstituent G x) :
    Finset (SecondSubconstituent G x) := by
  classical
  exact Finset.univ.filter fun D => localGramMatrix G x B D = 0

/--
@isnad1 id=iff.0h5v.s6.770fd52938c4 from=translated src=- shape=95d30840 vocab=939b7f41
-/
@[simp]
theorem mem_zeroGramIndices (x : V)
    (B D : SecondSubconstituent G x) :
    D ∈ zeroGramIndices G x B ↔ localGramMatrix G x B D = 0 := by
  classical
  simp [zeroGramIndices]

/--
@isnad1 id=eq.1h4v.s6.a37d3944dfb1 from=translated src=- shape=16b4a2b5 vocab=b80db79d
-/
theorem sum_localGramMatrix_row_sq
    (hG : IsHypothetical G) (x : V)
    (B : SecondSubconstituent G x) :
    ∑ D, localGramMatrix G x B D ^ 2 = 225 := by
  calc
    (∑ D, localGramMatrix G x B D ^ 2) =
        (localGramMatrix G x * localGramMatrix G x) B B := by
      rw [Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro D _
      rw [localGramMatrix_comm G x D B]
      ring
    _ = 45 * localGramMatrix G x B B + 90 :=
      localGramMatrix_sq_apply G hG x B B
    _ = 225 := by rw [localGramMatrix_diagonal G hG x B]; norm_num

/--
@isnad1 id=eq.1h4v.s6.ec35013c1bda from=translated src=- shape=13572a41 vocab=1c9df702
-/
theorem zeroGramIndices_card_add_gramClass_card
    (hG : IsHypothetical G) (x : V)
    (B : SecondSubconstituent G x) :
    (zeroGramIndices G x B).card + (gramClass G x B).card = 85 := by
  classical
  let L : SecondSubconstituent G x → ℤ :=
    fun D => localGramMatrix G x B D
  have hpoint (D : SecondSubconstituent G x) :
      2 * (if L D = 0 then (1 : ℤ) else 0) =
        2 - 3 * L D + L D ^ 2 -
          2 * (if L D = 3 then (1 : ℤ) else 0) := by
    rcases localGramMatrix_entry_cases G hG x B D with
      hzero | hone | htwo | hthree
    · simp [L, hzero]
    · simp [L, hone]
    · simp [L, htwo]
    · simp [L, hthree]
  have hzeroCount :
      ∑ D, (if L D = 0 then (1 : ℤ) else 0) =
        ((zeroGramIndices G x B).card : ℤ) := by
    simp [L, zeroGramIndices]
  have hthreeCount :
      ∑ D, (if L D = 3 then (1 : ℤ) else 0) =
        ((gramClass G x B).card : ℤ) := by
    calc
      (∑ D, (if L D = 3 then (1 : ℤ) else 0)) =
          ∑ D, (if GramEquivalent G x B D then (1 : ℤ) else 0) := by
        apply Finset.sum_congr rfl
        intro D _
        rw [gramEquivalent_iff_entry_eq_three G hG x B D]
        simp [L]
      _ = ((gramClass G x B).card : ℤ) := by
        simp [gramClass]
  have hidentity :
      2 * ((zeroGramIndices G x B).card : ℤ) =
        440 - 3 * 165 + 225 -
          2 * ((gramClass G x B).card : ℤ) := by
    calc
      2 * ((zeroGramIndices G x B).card : ℤ) =
          ∑ D, 2 * (if L D = 0 then (1 : ℤ) else 0) := by
        rw [← hzeroCount, Finset.mul_sum]
      _ = ∑ D, (2 - 3 * L D + L D ^ 2 -
          2 * (if L D = 3 then (1 : ℤ) else 0)) := by
        apply Finset.sum_congr rfl
        intro D _
        exact hpoint D
      _ = 440 - 3 * 165 + 225 -
          2 * ((gramClass G x B).card : ℤ) := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
          Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          hthreeCount]
        change
          (∑ _D : SecondSubconstituent G x, (2 : ℤ)) -
              3 * (∑ D, localGramMatrix G x B D) +
              ∑ D, localGramMatrix G x B D ^ 2 -
              2 * ((gramClass G x B).card : ℤ) =
            440 - 3 * 165 + 225 -
              2 * ((gramClass G x B).card : ℤ)
        rw [localGramMatrix_row_sum G hG x B,
          sum_localGramMatrix_row_sq G hG x B]
        simp [secondSubconstituent_card G hG x]
  exact_mod_cast (show
    ((zeroGramIndices G x B).card : ℤ) +
        (gramClass G x B).card = 85 by omega)

noncomputable def classAdjacencySet (x : V)
    (B D : SecondSubconstituent G x) :
    Finset (SecondSubconstituent G x) := by
  classical
  exact (gramClass G x B).filter fun C =>
    (secondSubconstituentGraph G x).Adj C D

noncomputable def classNonneighborSet (x : V)
    (B D : SecondSubconstituent G x) :
    Finset (SecondSubconstituent G x) := by
  classical
  exact (gramClass G x B).filter fun C =>
    ¬(secondSubconstituentGraph G x).Adj C D

/--
@isnad1 id=iff.0h6v.s7.e9665bcac49b from=translated src=- shape=4a0fcd5f vocab=f17ac599
-/
@[simp]
theorem mem_classAdjacencySet (x : V)
    (B D C : SecondSubconstituent G x) :
    C ∈ classAdjacencySet G x B D ↔
      C ∈ gramClass G x B ∧
        (secondSubconstituentGraph G x).Adj C D := by
  classical
  simp [classAdjacencySet]

/--
@isnad1 id=iff.0h6v.s7.8bf2d57c0215 from=translated src=- shape=6d9453a0 vocab=e1625a13
-/
@[simp]
theorem mem_classNonneighborSet (x : V)
    (B D C : SecondSubconstituent G x) :
    C ∈ classNonneighborSet G x B D ↔
      C ∈ gramClass G x B ∧
        ¬(secondSubconstituentGraph G x).Adj C D := by
  classical
  simp [classNonneighborSet]

/--
@isnad1 id=eq.0h5v.s6.99658ef1d1da from=translated src=- shape=f744ff5d vocab=8c829895
-/
theorem classAdjacency_card_add_nonneighbor_card
    (x : V) (B D : SecondSubconstituent G x) :
    (classAdjacencySet G x B D).card +
        (classNonneighborSet G x B D).card =
      (gramClass G x B).card := by
  classical
  simpa [classAdjacencySet, classNonneighborSet] using
    (Finset.card_filter_add_card_filter_not
      (s := gramClass G x B)
      (p := fun C => (secondSubconstituentGraph G x).Adj C D))

/--
@isnad1 id=eq.4h6v.s7.a2f30eaa1a7a from=translated src=- shape=31608823 vocab=df8a0d8f
-/
theorem classMember_intersection_eq_three_of_zeroGram_not_adj
    (hG : IsHypothetical G) (x : V)
    {B C D : SecondSubconstituent G x}
    (hC : C ∈ gramClass G x B)
    (hD : D ∈ zeroGramIndices G x B)
    (hnot : ¬(secondSubconstituentGraph G x).Adj C D) :
    blockIntersection G x C D = 3 := by
  have hrow :
      localGramMatrix G x B D = localGramMatrix G x C D :=
    (mem_gramClass G x B C).mp hC D
  have hzeroB :
      localGramMatrix G x B D = 0 :=
    (mem_zeroGramIndices G x B D).mp hD
  have hzeroC : localGramMatrix G x C D = 0 := hrow ▸ hzeroB
  have hne : C ≠ D := by
    intro hCD
    subst D
    rw [localGramMatrix_diagonal G hG x C] at hzeroC
    norm_num at hzeroC
  have hformula := localGramMatrix_of_not_adj G x hne hnot
  have hcast : (blockIntersection G x C D : ℤ) = 3 := by omega
  exact_mod_cast hcast

/--
@isnad1 id=le.2h5v.s6.0aa8dacc874a from=translated src=- shape=5d2ca0d4 vocab=daf42b5d
-/
theorem classNonneighborSet_card_le_three
    (hG : IsHypothetical G) (x : V)
    (B D : SecondSubconstituent G x)
    (hD : D ∈ zeroGramIndices G x B) :
    (classNonneighborSet G x B D).card ≤ 3 := by
  classical
  let pieces : SecondSubconstituent G x →
      Finset (FirstSubconstituent G x) :=
    fun C => localBlock G x C ∩ localBlock G x D
  have hpair :
      ((classNonneighborSet G x B D :
          Finset (SecondSubconstituent G x)) :
        Set (SecondSubconstituent G x)).PairwiseDisjoint pieces := by
    intro C hC E hE hne
    have hCclass := (mem_classNonneighborSet G x B D C).mp hC |>.1
    have hEclass := (mem_classNonneighborSet G x B D E).mp hE |>.1
    have hdisjoint :=
      localBlocks_disjoint_of_gramEquivalent G hG x hne
        (gramEquivalent_of_mem_gramClass G x B hCclass hEclass)
    exact hdisjoint.mono Finset.inter_subset_left Finset.inter_subset_left
  have hpieceCard :
      ∀ C ∈ classNonneighborSet G x B D, (pieces C).card = 3 := by
    intro C hC
    have hmem := (mem_classNonneighborSet G x B D C).mp hC
    exact classMember_intersection_eq_three_of_zeroGram_not_adj
      G hG x hmem.1 hD hmem.2
  have hcard :=
    Finset.card_biUnion hpair
  have hsubset :
      (classNonneighborSet G x B D).biUnion pieces ⊆ localBlock G x D := by
    intro p hp
    rcases Finset.mem_biUnion.mp hp with ⟨C, _hC, hpC⟩
    exact (Finset.mem_inter.mp hpC).2
  have hunion :
      ((classNonneighborSet G x B D).biUnion pieces).card ≤ 9 := by
    calc
      ((classNonneighborSet G x B D).biUnion pieces).card ≤
          (localBlock G x D).card :=
        Finset.card_le_card hsubset
      _ = 9 := localBlock_card G hG x D
  have hsum :
      ∑ C ∈ classNonneighborSet G x B D, (pieces C).card =
        (classNonneighborSet G x B D).card * 3 :=
    Finset.sum_const_nat hpieceCard
  rw [hcard, hsum] at hunion
  omega

/--
@isnad1 id=le.2h5v.s7.8f6992062dc5 from=translated src=- shape=d8e4c17a vocab=fb0f7eb5
-/
theorem classAdjacencySet_card_lower_bound
    (hG : IsHypothetical G) (x : V)
    (B D : SecondSubconstituent G x)
    (hD : D ∈ zeroGramIndices G x B) :
    (gramClass G x B).card ≤
      (classAdjacencySet G x B D).card + 3 := by
  have hpartition := classAdjacency_card_add_nonneighbor_card G x B D
  have hnon := classNonneighborSet_card_le_three G hG x B D hD
  omega

noncomputable def classAdjacencyWeight (x : V)
    (B D : SecondSubconstituent G x) : ℤ :=
  ((classAdjacencySet G x B D).card : ℤ)

/--
@isnad1 id=eq.0h5v.s6.e2ea3aed71a9 from=translated src=- shape=24086672 vocab=a17aedb0
-/
theorem classAdjacencyWeight_eq_matrix_sum
    (x : V) (B D : SecondSubconstituent G x) :
    classAdjacencyWeight G x B D =
      ∑ C ∈ gramClass G x B, localAdjacencyMatrix G x C D := by
  classical
  simp [classAdjacencyWeight, classAdjacencySet, localAdjacencyMatrix]

/--
@isnad1 id=eq.2h5v.s6.84f9f96e0182 from=translated src=- shape=6f447e22 vocab=a6e486ce
-/
theorem classAdjacencyWeight_eq_zero_of_not_mem
    (hG : IsHypothetical G) (x : V)
    (B D : SecondSubconstituent G x)
    (hD : D ∉ zeroGramIndices G x B) :
    classAdjacencyWeight G x B D = 0 := by
  rw [classAdjacencyWeight_eq_matrix_sum]
  apply Finset.sum_eq_zero
  intro C hC
  by_cases hCD : (secondSubconstituentGraph G x).Adj C D
  · have hrow :
        localGramMatrix G x B D = localGramMatrix G x C D :=
      (mem_gramClass G x B C).mp hC D
    have hzeroC := localGramMatrix_of_adj G hG x hCD
    have hzeroB : localGramMatrix G x B D = 0 := hrow.trans hzeroC
    exact False.elim (hD ((mem_zeroGramIndices G x B D).mpr hzeroB))
  · have hGCD : ¬G.Adj (C : V) (D : V) := hCD
    simp [localAdjacencyMatrix, hGCD]

/--
@isnad1 id=eq.1h4v.s7.68004265a706 from=translated src=- shape=177f0310 vocab=f2bde7ed
-/
theorem sum_classAdjacencyWeight
    (hG : IsHypothetical G) (x : V)
    (B : SecondSubconstituent G x) :
    ∑ D, classAdjacencyWeight G x B D =
      36 * (gramClass G x B).card := by
  classical
  calc
    (∑ D, classAdjacencyWeight G x B D) =
        ∑ D, ∑ C ∈ gramClass G x B,
          localAdjacencyMatrix G x C D := by
      apply Finset.sum_congr rfl
      intro D _
      exact classAdjacencyWeight_eq_matrix_sum G x B D
    _ = ∑ C ∈ gramClass G x B, ∑ D,
          localAdjacencyMatrix G x C D := by
      rw [Finset.sum_comm]
    _ = ∑ _C ∈ gramClass G x B, (36 : ℤ) := by
      apply Finset.sum_congr rfl
      intro C _
      have hrow := congrFun (localAdjacencyMatrix_mulVec_one G hG x) C
      simpa [Matrix.mulVec_apply_eq_sum] using hrow
    _ = 36 * (gramClass G x B).card := by
      simp
      ring

/--
@isnad1 id=eq.1h4v.s6.38780e74e3cf from=translated src=- shape=456dd9a2 vocab=0b69ba2b
-/
theorem sum_zeroGram_classAdjacencyWeight
    (hG : IsHypothetical G) (x : V)
    (B : SecondSubconstituent G x) :
    ∑ D ∈ zeroGramIndices G x B, classAdjacencyWeight G x B D =
      36 * (gramClass G x B).card := by
  classical
  calc
    (∑ D ∈ zeroGramIndices G x B, classAdjacencyWeight G x B D) =
        ∑ D, classAdjacencyWeight G x B D := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro D _hDuniv hDnot
      exact classAdjacencyWeight_eq_zero_of_not_mem G hG x B D hDnot
    _ = 36 * (gramClass G x B).card :=
      sum_classAdjacencyWeight G hG x B

/--
@isnad1 id=eq.3h6v.s8.7d8eb2c060d0 from=translated src=- shape=64629e3c vocab=6f24074f
-/
theorem localAdjacencyMatrix_sq_of_mem_gramClass
    (hG : IsHypothetical G) (x : V)
    (B : SecondSubconstituent G x)
    {C E : SecondSubconstituent G x}
    (hC : C ∈ gramClass G x B)
    (hE : E ∈ gramClass G x B) :
    (localAdjacencyMatrix G x * localAdjacencyMatrix G x) C E =
      if C = E then 36 else 9 := by
  by_cases hCE : C = E
  · rw [ite_eq_left hCE, hCE]
    simpa using localAdjacencyMatrix_sq_apply G hG x E E
  · rw [ite_eq_right hCE, localAdjacencyMatrix_sq_apply G hG x C E,
      ite_eq_right hCE]
    have hEq := gramEquivalent_of_mem_gramClass G x B hC hE
    have hnotadj : ¬(secondSubconstituentGraph G x).Adj C E := by
      intro hadj
      have hthree :=
        (gramEquivalent_iff_entry_eq_three G hG x C E).mp hEq
      have hzero := localGramMatrix_of_adj G hG x hadj
      omega
    rw [ite_eq_right hnotadj]
    have hdisjoint :=
      localBlocks_disjoint_of_gramEquivalent G hG x hCE hEq
    have hinter : blockIntersection G x C E = 0 := by
      rw [blockIntersection, Finset.card_eq_zero,
        ← Finset.disjoint_iff_inter_eq_empty]
      exact hdisjoint
    rw [hinter]
    norm_num

/--
@isnad1 id=eq.1h4v.s7.3ec6b13e0db8 from=translated src=- shape=111457ec vocab=88f040e2
-/
theorem sum_classAdjacencyWeight_sq
    (hG : IsHypothetical G) (x : V)
    (B : SecondSubconstituent G x) :
    ∑ D, classAdjacencyWeight G x B D ^ 2 =
      9 * (gramClass G x B).card ^ 2 +
        27 * (gramClass G x B).card := by
  classical
  let S := gramClass G x B
  let H := localAdjacencyMatrix G x
  have hexpand (D : SecondSubconstituent G x) :
      classAdjacencyWeight G x B D ^ 2 =
        ∑ C ∈ S, ∑ E ∈ S, H C D * H E D := by
    rw [classAdjacencyWeight_eq_matrix_sum]
    change (∑ C ∈ S, H C D) ^ 2 =
      ∑ C ∈ S, ∑ E ∈ S, H C D * H E D
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro C _
    rw [Finset.mul_sum]
  calc
    (∑ D, classAdjacencyWeight G x B D ^ 2) =
        ∑ D, ∑ C ∈ S, ∑ E ∈ S, H C D * H E D := by
      apply Finset.sum_congr rfl
      intro D _
      exact hexpand D
    _ = ∑ C ∈ S, ∑ E ∈ S, ∑ D, H C D * H E D := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro C _
      rw [Finset.sum_comm]
    _ = ∑ C ∈ S, ∑ E ∈ S, (H * H) C E := by
      apply Finset.sum_congr rfl
      intro C _
      apply Finset.sum_congr rfl
      intro E _
      rw [Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro D _
      change
        localAdjacencyMatrix G x C D * localAdjacencyMatrix G x E D =
          localAdjacencyMatrix G x C D * localAdjacencyMatrix G x D E
      congr 1
      simp [localAdjacencyMatrix, SimpleGraph.adj_comm]
    _ = ∑ C ∈ S, ∑ E ∈ S, (if C = E then (36 : ℤ) else 9) := by
      apply Finset.sum_congr rfl
      intro C hC
      apply Finset.sum_congr rfl
      intro E hE
      exact localAdjacencyMatrix_sq_of_mem_gramClass G hG x B hC hE
    _ = ∑ _C ∈ S, (9 * (S.card : ℤ) + 27) := by
      apply Finset.sum_congr rfl
      intro C hC
      calc
        (∑ E ∈ S, (if C = E then (36 : ℤ) else 9)) =
            ∑ E ∈ S, (9 + if C = E then (27 : ℤ) else 0) := by
          apply Finset.sum_congr rfl
          intro E _
          by_cases hCE : C = E <;> simp [hCE]
        _ = 9 * (S.card : ℤ) + 27 := by
          rw [Finset.sum_add_distrib]
          simp [hC]
          ring
    _ = 9 * (gramClass G x B).card ^ 2 +
        27 * (gramClass G x B).card := by
      simp [S]
      ring

/--
@isnad1 id=eq.1h4v.s7.518e7b49f5d7 from=translated src=- shape=642dc44d vocab=5afd3593
-/
theorem sum_zeroGram_classAdjacencyWeight_sq
    (hG : IsHypothetical G) (x : V)
    (B : SecondSubconstituent G x) :
    ∑ D ∈ zeroGramIndices G x B,
        classAdjacencyWeight G x B D ^ 2 =
      9 * (gramClass G x B).card ^ 2 +
        27 * (gramClass G x B).card := by
  classical
  calc
    (∑ D ∈ zeroGramIndices G x B,
        classAdjacencyWeight G x B D ^ 2) =
        ∑ D, classAdjacencyWeight G x B D ^ 2 := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro D _hDuniv hDnot
      rw [classAdjacencyWeight_eq_zero_of_not_mem G hG x B D hDnot]
      norm_num
    _ = 9 * (gramClass G x B).card ^ 2 +
        27 * (gramClass G x B).card :=
      sum_classAdjacencyWeight_sq G hG x B

private theorem quadratic_four_nonnegative
    (n : ℕ) (hlower : 1 ≤ n) (hupper : n ≤ 4) :
    0 ≤ (n : ℤ) ^ 2 - 3 * n + 2 := by
  interval_cases n <;> norm_num

private theorem quadratic_five_nonnegative
    (n : ℕ) (hlower : 2 ≤ n) (hupper : n ≤ 5) :
    0 ≤ (n : ℤ) ^ 2 - 5 * n + 6 := by
  interval_cases n <;> norm_num

/--
@isnad1 id=ne.1h4v.s5.532ff1ad7875 from=translated src=- shape=0d3167f8 vocab=866fb790
-/
theorem gramClass_card_ne_four
    (hG : IsHypothetical G) (x : V)
    (B : SecondSubconstituent G x) :
    (gramClass G x B).card ≠ 4 := by
  classical
  intro hclass
  have hzeroCard :
      (zeroGramIndices G x B).card = 81 := by
    have hpartition :=
      zeroGramIndices_card_add_gramClass_card G hG x B
    omega
  have hfirst :
      ∑ D ∈ zeroGramIndices G x B,
          classAdjacencyWeight G x B D = 144 := by
    rw [sum_zeroGram_classAdjacencyWeight G hG x B, hclass]
    norm_num
  have hsecond :
      ∑ D ∈ zeroGramIndices G x B,
          classAdjacencyWeight G x B D ^ 2 = 252 := by
    rw [sum_zeroGram_classAdjacencyWeight_sq G hG x B, hclass]
    norm_num
  have hnonnegative :
      0 ≤ ∑ D ∈ zeroGramIndices G x B,
        (classAdjacencyWeight G x B D ^ 2 -
          3 * classAdjacencyWeight G x B D + 2) := by
    apply Finset.sum_nonneg
    intro D hD
    rw [classAdjacencyWeight]
    apply quadratic_four_nonnegative
    · have hlower :=
        classAdjacencySet_card_lower_bound G hG x B D hD
      omega
    · have hsubset :
          classAdjacencySet G x B D ⊆ gramClass G x B := by
        intro C hC
        exact (mem_classAdjacencySet G x B D C).mp hC |>.1
      have hle := Finset.card_le_card hsubset
      omega
  have hexact :
      ∑ D ∈ zeroGramIndices G x B,
        (classAdjacencyWeight G x B D ^ 2 -
          3 * classAdjacencyWeight G x B D + 2) = -18 := by
    calc
      (∑ D ∈ zeroGramIndices G x B,
          (classAdjacencyWeight G x B D ^ 2 -
            3 * classAdjacencyWeight G x B D + 2)) =
          (∑ D ∈ zeroGramIndices G x B,
            classAdjacencyWeight G x B D ^ 2) -
          3 * (∑ D ∈ zeroGramIndices G x B,
            classAdjacencyWeight G x B D) +
          2 * (zeroGramIndices G x B).card := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum]
        simp
        ring
      _ = -18 := by rw [hfirst, hsecond, hzeroCard]; norm_num
  rw [hexact] at hnonnegative
  norm_num at hnonnegative

/--
@isnad1 id=ne.1h4v.s5.5b85b0560e4f from=translated src=- shape=0d3167f8 vocab=866fb790
-/
theorem gramClass_card_ne_five
    (hG : IsHypothetical G) (x : V)
    (B : SecondSubconstituent G x) :
    (gramClass G x B).card ≠ 5 := by
  classical
  intro hclass
  have hzeroCard :
      (zeroGramIndices G x B).card = 80 := by
    have hpartition :=
      zeroGramIndices_card_add_gramClass_card G hG x B
    omega
  have hfirst :
      ∑ D ∈ zeroGramIndices G x B,
          classAdjacencyWeight G x B D = 180 := by
    rw [sum_zeroGram_classAdjacencyWeight G hG x B, hclass]
    norm_num
  have hsecond :
      ∑ D ∈ zeroGramIndices G x B,
          classAdjacencyWeight G x B D ^ 2 = 360 := by
    rw [sum_zeroGram_classAdjacencyWeight_sq G hG x B, hclass]
    norm_num
  have hnonnegative :
      0 ≤ ∑ D ∈ zeroGramIndices G x B,
        (classAdjacencyWeight G x B D ^ 2 -
          5 * classAdjacencyWeight G x B D + 6) := by
    apply Finset.sum_nonneg
    intro D hD
    rw [classAdjacencyWeight]
    apply quadratic_five_nonnegative
    · have hlower :=
        classAdjacencySet_card_lower_bound G hG x B D hD
      omega
    · have hsubset :
          classAdjacencySet G x B D ⊆ gramClass G x B := by
        intro C hC
        exact (mem_classAdjacencySet G x B D C).mp hC |>.1
      have hle := Finset.card_le_card hsubset
      omega
  have hexact :
      ∑ D ∈ zeroGramIndices G x B,
        (classAdjacencyWeight G x B D ^ 2 -
          5 * classAdjacencyWeight G x B D + 6) = -60 := by
    calc
      (∑ D ∈ zeroGramIndices G x B,
          (classAdjacencyWeight G x B D ^ 2 -
            5 * classAdjacencyWeight G x B D + 6)) =
          (∑ D ∈ zeroGramIndices G x B,
            classAdjacencyWeight G x B D ^ 2) -
          5 * (∑ D ∈ zeroGramIndices G x B,
            classAdjacencyWeight G x B D) +
          6 * (zeroGramIndices G x B).card := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum]
        simp
        ring
      _ = -60 := by rw [hfirst, hsecond, hzeroCard]; norm_num
  rw [hexact] at hnonnegative
  norm_num at hnonnegative

/--
@isnad1 id=le.1h4v.s5.322c8ea45736 from=translated src=- shape=0d3167f8 vocab=94b50484
-/
theorem gramClass_card_le_three
    (hG : IsHypothetical G) (x : V)
    (B : SecondSubconstituent G x) :
    (gramClass G x B).card ≤ 3 := by
  have hle := gramClass_card_le_five G hG x B
  have hneFour := gramClass_card_ne_four G hG x B
  have hneFive := gramClass_card_ne_five G hG x B
  omega

noncomputable def gramEntryIndices (x : V)
    (B : SecondSubconstituent G x) (k : ℤ) :
    Finset (SecondSubconstituent G x) := by
  classical
  exact Finset.univ.filter fun D => localGramMatrix G x B D = k

/--
@isnad1 id=iff.0h6v.s6.98eefcadfacb from=translated src=- shape=d9295ce6 vocab=5a202288
-/
@[simp]
theorem mem_gramEntryIndices (x : V)
    (B D : SecondSubconstituent G x) (k : ℤ) :
    D ∈ gramEntryIndices G x B k ↔
      localGramMatrix G x B D = k := by
  classical
  simp [gramEntryIndices]

/--
@isnad1 id=eq.0h4v.s5.a976b28f8552 from=translated src=- shape=fc3767a7 vocab=86800143
-/
theorem gramEntryIndices_zero
    (x : V) (B : SecondSubconstituent G x) :
    gramEntryIndices G x B 0 = zeroGramIndices G x B := by
  classical
  ext D
  simp

/--
@isnad1 id=eq.1h4v.s5.f4ce18b28772 from=translated src=- shape=3bc9fb45 vocab=254b421b
-/
theorem gramEntryIndices_three
    (hG : IsHypothetical G) (x : V)
    (B : SecondSubconstituent G x) :
    gramEntryIndices G x B 3 = gramClass G x B := by
  classical
  ext D
  rw [mem_gramEntryIndices, mem_gramClass,
    gramEquivalent_iff_entry_eq_three G hG x B D]

/--
@isnad1 id=eq.1h4v.s6.fd3f6f8bb5dd from=translated src=- shape=f76fffc9 vocab=028b6f54
-/
theorem gramEntryTwo_card_add_three_mul_class_card
    (hG : IsHypothetical G) (x : V)
    (B : SecondSubconstituent G x) :
    (gramEntryIndices G x B 2).card +
        3 * (gramClass G x B).card = 30 := by
  classical
  let L : SecondSubconstituent G x → ℤ :=
    fun D => localGramMatrix G x B D
  have hpoint (D : SecondSubconstituent G x) :
      L D ^ 2 - L D =
        2 * (if L D = 2 then (1 : ℤ) else 0) +
          6 * (if L D = 3 then (1 : ℤ) else 0) := by
    rcases localGramMatrix_entry_cases G hG x B D with
      hzero | hone | htwo | hthree
    · simp [L, hzero]
    · simp [L, hone]
    · simp [L, htwo]
    · simp [L, hthree]
  have htwoCount :
      ∑ D, (if L D = 2 then (1 : ℤ) else 0) =
        ((gramEntryIndices G x B 2).card : ℤ) := by
    simp [L, gramEntryIndices]
  have hthreeCount :
      ∑ D, (if L D = 3 then (1 : ℤ) else 0) =
        ((gramClass G x B).card : ℤ) := by
    rw [← gramEntryIndices_three G hG x B]
    simp [L, gramEntryIndices]
  have hsum :
      60 =
        2 * ((gramEntryIndices G x B 2).card : ℤ) +
          6 * ((gramClass G x B).card : ℤ) := by
    calc
      60 = (∑ D, L D ^ 2) - ∑ D, L D := by
        change 60 =
          (∑ D, localGramMatrix G x B D ^ 2) -
            ∑ D, localGramMatrix G x B D
        rw [sum_localGramMatrix_row_sq G hG x B,
          localGramMatrix_row_sum G hG x B]
        norm_num
      _ = ∑ D, (L D ^ 2 - L D) := by
        rw [Finset.sum_sub_distrib]
      _ = ∑ D, (2 * (if L D = 2 then (1 : ℤ) else 0) +
          6 * (if L D = 3 then (1 : ℤ) else 0)) := by
        apply Finset.sum_congr rfl
        intro D _
        exact hpoint D
      _ = 2 * ((gramEntryIndices G x B 2).card : ℤ) +
          6 * ((gramClass G x B).card : ℤ) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum,
          ← Finset.mul_sum, htwoCount, hthreeCount]
  exact_mod_cast (show
    ((gramEntryIndices G x B 2).card : ℤ) +
        3 * (gramClass G x B).card = 30 by omega)

/--
@isnad1 id=eq.1h4v.s6.8faf45179b72 from=translated src=- shape=814f70b5 vocab=028b6f54
-/
theorem gramEntryOne_card
    (hG : IsHypothetical G) (x : V)
    (B : SecondSubconstituent G x) :
    (gramEntryIndices G x B 1).card =
      105 + 3 * (gramClass G x B).card := by
  classical
  let L : SecondSubconstituent G x → ℤ :=
    fun D => localGramMatrix G x B D
  have hpoint (D : SecondSubconstituent G x) :
      L D =
        (if L D = 1 then (1 : ℤ) else 0) +
          2 * (if L D = 2 then (1 : ℤ) else 0) +
          3 * (if L D = 3 then (1 : ℤ) else 0) := by
    rcases localGramMatrix_entry_cases G hG x B D with
      hzero | hone | htwo | hthree
    · simp [L, hzero]
    · simp [L, hone]
    · simp [L, htwo]
    · simp [L, hthree]
  have honeCount :
      ∑ D, (if L D = 1 then (1 : ℤ) else 0) =
        ((gramEntryIndices G x B 1).card : ℤ) := by
    simp [L, gramEntryIndices]
  have htwoCount :
      ∑ D, (if L D = 2 then (1 : ℤ) else 0) =
        ((gramEntryIndices G x B 2).card : ℤ) := by
    simp [L, gramEntryIndices]
  have hthreeCount :
      ∑ D, (if L D = 3 then (1 : ℤ) else 0) =
        ((gramClass G x B).card : ℤ) := by
    rw [← gramEntryIndices_three G hG x B]
    simp [L, gramEntryIndices]
  have hrow :
      165 =
        ((gramEntryIndices G x B 1).card : ℤ) +
          2 * (gramEntryIndices G x B 2).card +
          3 * (gramClass G x B).card := by
    calc
      165 = ∑ D, L D := by
        exact (localGramMatrix_row_sum G hG x B).symm
      _ = ∑ D, ((if L D = 1 then (1 : ℤ) else 0) +
          2 * (if L D = 2 then (1 : ℤ) else 0) +
          3 * (if L D = 3 then (1 : ℤ) else 0)) := by
        apply Finset.sum_congr rfl
        intro D _
        exact hpoint D
      _ = ((gramEntryIndices G x B 1).card : ℤ) +
          2 * (gramEntryIndices G x B 2).card +
          3 * (gramClass G x B).card := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum,
          honeCount, htwoCount, hthreeCount]
  have htwo :=
    gramEntryTwo_card_add_three_mul_class_card G hG x B
  have htwoZ :
      ((gramEntryIndices G x B 2).card : ℤ) +
          3 * ((gramClass G x B).card : ℤ) = 30 := by
    exact_mod_cast htwo
  exact_mod_cast (show
    ((gramEntryIndices G x B 1).card : ℤ) =
        105 + 3 * (gramClass G x B).card by
      omega)

/--
@isnad1 id=and.1h4v.s7.7f0c0601bb71 from=translated src=- shape=b801b95d vocab=028b6f54
-/
theorem gramEntry_weighted_profile
    (hG : IsHypothetical G) (x : V)
    (B : SecondSubconstituent G x) :
    (gramEntryIndices G x B 0).card +
          (gramClass G x B).card = 85 ∧
      (gramEntryIndices G x B 1).card =
          105 + 3 * (gramClass G x B).card ∧
      (gramEntryIndices G x B 2).card +
          3 * (gramClass G x B).card = 30 ∧
      (gramEntryIndices G x B 3).card =
          (gramClass G x B).card := by
  constructor
  · rw [gramEntryIndices_zero]
    exact zeroGramIndices_card_add_gramClass_card G hG x B
  constructor
  · exact gramEntryOne_card G hG x B
  constructor
  · exact gramEntryTwo_card_add_three_mul_class_card G hG x B
  · rw [gramEntryIndices_three G hG x B]

end SRG266
