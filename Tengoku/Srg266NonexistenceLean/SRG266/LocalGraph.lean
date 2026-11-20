/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.IncidenceMatrix
import Tengoku.Seed.Combinatorics.SimpleGraph.Maps

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped Matrix

namespace SRG266

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

abbrev secondSubconstituentGraph (x : V) :
    SimpleGraph (SecondSubconstituent G x) :=
  G.induce (Gᶜ.neighborSet x)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/--
@isnad1 id=iff.0h5v.s6.4cfdc0af2a34 from=translated src=- shape=638c1b55 vocab=81e7a03e
-/
@[simp]
theorem secondSubconstituentGraph_adj
    (x : V) (B C : SecondSubconstituent G x) :
    (secondSubconstituentGraph G x).Adj B C ↔ G.Adj (B : V) (C : V) :=
  Iff.rfl

/--
@isnad1 id=eq.0h4v.s8.7bb38354fc09 from=translated src=- shape=199418f5 vocab=a2f0fb30
-/
theorem second_neighbor_inter_eq_sdiff_common
    (x : V) (B : SecondSubconstituent G x) :
    G.neighborFinset (B : V) ∩ (Gᶜ.neighborSet x).toFinset =
      G.neighborFinset (B : V) \ (G.commonNeighbors x (B : V)).toFinset := by
  ext z
  have hBx : ¬G.Adj (B : V) x :=
    (((G.compl_adj x B).mp B.property).2) ∘ G.adj_symm
  simp only [Finset.mem_inter, G.mem_neighborFinset, Set.mem_toFinset,
    Finset.mem_sdiff, G.mem_commonNeighbors]
  constructor
  · rintro ⟨hBz, hzSecond⟩
    have hz := (G.compl_adj x z).mp hzSecond
    exact ⟨hBz, fun h => hz.2 h.1⟩
  · rintro ⟨hBz, hnotCommon⟩
    have hnotxz : ¬G.Adj x z := fun hxz => hnotCommon ⟨hxz, hBz⟩
    have hxne : x ≠ z := by
      intro hxz
      subst z
      exact hBx hBz
    exact ⟨hBz, (G.compl_adj x z).mpr ⟨hxne, hnotxz⟩⟩

/--
@isnad1 id=eq.1h4v.s8.e3e3db553ca9 from=translated src=- shape=1132da66 vocab=6df286b1
-/
theorem secondSubconstituentGraph_degree
    (hG : IsHypothetical G) (x : V) (B : SecondSubconstituent G x) :
    (secondSubconstituentGraph G x).degree B = 36 := by
  have hmap := G.map_neighborFinset_induce B
  have hsubset :
      (G.commonNeighbors x (B : V)).toFinset ⊆ G.neighborFinset (B : V) := by
    intro z hz
    exact (G.mem_neighborFinset _ _).mpr ((G.mem_commonNeighbors).mp
      (Set.mem_toFinset.mp hz)).2
  have hB := (G.compl_adj x B).mp B.property
  calc
    (secondSubconstituentGraph G x).degree B =
        ((secondSubconstituentGraph G x).neighborFinset B).card :=
      ((secondSubconstituentGraph G x).card_neighborFinset_eq_degree B).symm
    _ = (((secondSubconstituentGraph G x).neighborFinset B).map
        (.subtype (· ∈ Gᶜ.neighborSet x))).card := (Finset.card_map _).symm
    _ = (G.neighborFinset (B : V) ∩ (Gᶜ.neighborSet x).toFinset).card :=
      congrArg Finset.card hmap
    _ = (G.neighborFinset (B : V) \
        (G.commonNeighbors x (B : V)).toFinset).card :=
      congrArg Finset.card (second_neighbor_inter_eq_sdiff_common G x B)
    _ = (G.neighborFinset (B : V)).card -
        (G.commonNeighbors x (B : V)).toFinset.card :=
      Finset.card_sdiff_of_subset hsubset
    _ = 36 := by
      rw [G.card_neighborFinset_eq_degree, Set.toFinset_card, hG.regular B,
        hG.of_not_adj hB.1 hB.2]

/--
@isnad1 id=isregula.1h3v.s8.593eb3c0b669 from=translated src=- shape=41009c34 vocab=682a740a
-/
theorem secondSubconstituentGraph_regular
    (hG : IsHypothetical G) (x : V) :
    (secondSubconstituentGraph G x).IsRegularOfDegree 36 :=
  secondSubconstituentGraph_degree G hG x

def commonNeighborsDecompositionTo
    (x : V) (B C : SecondSubconstituent G x) :
    G.commonNeighbors (B : V) (C : V) →
      Sum ↥(localBlock G x B ∩ localBlock G x C)
        ((secondSubconstituentGraph G x).commonNeighbors B C) := fun z => by
  by_cases hxz : G.Adj x (z : V)
  · exact Sum.inl
      ⟨⟨z, hxz⟩, Finset.mem_inter.mpr
        ⟨(mem_localBlock G x B ⟨z, hxz⟩).mpr z.property.1.symm,
          (mem_localBlock G x C ⟨z, hxz⟩).mpr z.property.2.symm⟩⟩
  · have hxne : x ≠ (z : V) := by
      intro hxzEq
      have hxB : ¬G.Adj x (B : V) := ((G.compl_adj x B).mp B.property).2
      apply hxB
      simpa [hxzEq] using z.property.1.symm
    let y : SecondSubconstituent G x :=
      ⟨z, (G.compl_adj x z).mpr ⟨hxne, hxz⟩⟩
    exact Sum.inr ⟨y, z.property⟩

def commonNeighborsDecompositionInv
    (x : V) (B C : SecondSubconstituent G x) :
    Sum ↥(localBlock G x B ∩ localBlock G x C)
        ((secondSubconstituentGraph G x).commonNeighbors B C) →
      G.commonNeighbors (B : V) (C : V)
  | Sum.inl p =>
      ⟨p.1, ⟨(mem_localBlock G x B p.1).mp
        (Finset.mem_inter.mp p.property).1 |>.symm,
        (mem_localBlock G x C p.1).mp
          (Finset.mem_inter.mp p.property).2 |>.symm⟩⟩
  | Sum.inr y => ⟨y.1, y.property⟩

def commonNeighborsDecomposition
    (x : V) (B C : SecondSubconstituent G x) :
    G.commonNeighbors (B : V) (C : V) ≃
      Sum ↥(localBlock G x B ∩ localBlock G x C)
        ((secondSubconstituentGraph G x).commonNeighbors B C) where
  toFun := commonNeighborsDecompositionTo G x B C
  invFun := commonNeighborsDecompositionInv G x B C
  left_inv z := by
    apply Subtype.ext
    by_cases hxz : G.Adj x (z : V)
    · simp [commonNeighborsDecompositionTo, commonNeighborsDecompositionInv, hxz]
    · simp [commonNeighborsDecompositionTo, commonNeighborsDecompositionInv, hxz]
  right_inv s := by
    cases s with
    | inl p =>
        have hp : G.Adj x (p.1 : V) := p.1.property
        simp [commonNeighborsDecompositionTo, commonNeighborsDecompositionInv, hp]
    | inr y =>
        have hxy : ¬G.Adj x (y : V) := ((G.compl_adj x y).mp y.1.property).2
        simp [commonNeighborsDecompositionTo, commonNeighborsDecompositionInv, hxy]

/--
@isnad1 id=eq.0h5v.s8.6bd8f4d1e77c from=translated src=- shape=64894112 vocab=2b9d7c2e
-/
theorem card_commonNeighbors_decomposition
    (x : V) (B C : SecondSubconstituent G x) :
    Fintype.card (G.commonNeighbors (B : V) (C : V)) =
      blockIntersection G x B C +
        Fintype.card ((secondSubconstituentGraph G x).commonNeighbors B C) := by
  calc
    Fintype.card (G.commonNeighbors (B : V) (C : V)) =
        Fintype.card
          (Sum ↥(localBlock G x B ∩ localBlock G x C)
            ((secondSubconstituentGraph G x).commonNeighbors B C)) :=
      Fintype.card_congr (commonNeighborsDecomposition G x B C)
    _ = Fintype.card ↥(localBlock G x B ∩ localBlock G x C) +
        Fintype.card ((secondSubconstituentGraph G x).commonNeighbors B C) := by
      rw [Fintype.card_sum]
    _ = blockIntersection G x B C +
        Fintype.card ((secondSubconstituentGraph G x).commonNeighbors B C) := by
      rw [Fintype.card_coe]
      rfl

/--
@isnad1 id=eq.3h5v.s8.2887a12514d0 from=translated src=- shape=06ed0c46 vocab=e10c9691
-/
theorem card_second_commonNeighbors_of_not_adj
    (hG : IsHypothetical G) (x : V)
    {B C : SecondSubconstituent G x} (hne : B ≠ C)
    (hBC : ¬(secondSubconstituentGraph G x).Adj B C) :
    Fintype.card ((secondSubconstituentGraph G x).commonNeighbors B C) =
      9 - blockIntersection G x B C := by
  have hval : (B : V) ≠ (C : V) := fun h => hne (Subtype.ext h)
  have hGBC : ¬G.Adj (B : V) (C : V) := hBC
  have htotal := hG.of_not_adj hval hGBC
  have hdecomp := card_commonNeighbors_decomposition G x B C
  omega

def localAdjacencyMatrix (x : V) :
    Matrix (SecondSubconstituent G x) (SecondSubconstituent G x) ℤ :=
  (secondSubconstituentGraph G x).adjMatrix ℤ

/--
@isnad1 id=eq.1h3v.s7.0b1d76896b21 from=translated src=- shape=cd9c03c9 vocab=1fb4496c
-/
@[simp]
theorem localAdjacencyMatrix_mulVec_one
    (hG : IsHypothetical G) (x : V) :
    localAdjacencyMatrix G x *ᵥ (1 : SecondSubconstituent G x → ℤ) = 36 := by
  funext B
  simpa [localAdjacencyMatrix] using
    (secondSubconstituentGraph G x).adjMatrix_mulVec_const_apply_of_regular
      (secondSubconstituentGraph_regular G hG x) (a := (1 : ℤ)) (v := B)

/--
@isnad1 id=eq.0h5v.s8.483388dcd19e from=translated src=- shape=2e795afb vocab=3198f5f1
-/
theorem localAdjacencyMatrix_sq_apply_card_commonNeighbors
    (x : V) (B C : SecondSubconstituent G x) :
    (localAdjacencyMatrix G x * localAdjacencyMatrix G x) B C =
      Fintype.card ((secondSubconstituentGraph G x).commonNeighbors B C) := by
  rw [Matrix.mul_apply]
  simp only [localAdjacencyMatrix, SimpleGraph.adjMatrix_apply, ite_zero_mul_ite_zero,
    one_mul, Finset.sum_boole]
  norm_cast
  rw [← Set.toFinset_card]
  apply congrArg Finset.card
  ext D
  simp [SimpleGraph.mem_commonNeighbors, SimpleGraph.adj_comm]

omit [DecidableEq V] in

/--
@isnad1 id=disjoint.2h5v.s6.64df623c2477 from=translated src=- shape=ba28cae4 vocab=1ca867e4
-/
theorem localBlock_disjoint_of_adj
    (hG : IsHypothetical G) (x : V)
    {B C : SecondSubconstituent G x}
    (hBC : (secondSubconstituentGraph G x).Adj B C) :
    Disjoint (localBlock G x B) (localBlock G x C) := by
  rw [Finset.disjoint_left]
  intro p hpB hpC
  have hcard : Fintype.card (G.commonNeighbors (B : V) (C : V)) = 0 :=
    hG.of_adj B C hBC
  let : IsEmpty (G.commonNeighbors (B : V) (C : V)) :=
    Fintype.card_eq_zero_iff.mp hcard
  exact isEmptyElim
    (⟨p, (mem_localBlock G x B p).mp hpB |>.symm,
      (mem_localBlock G x C p).mp hpC |>.symm⟩ :
        G.commonNeighbors (B : V) (C : V))

/--
@isnad1 id=eq.2h5v.s6.5bb3bf95121b from=translated src=- shape=d34ac22b vocab=a05691cc
-/
theorem blockIntersection_of_adj
    (hG : IsHypothetical G) (x : V)
    {B C : SecondSubconstituent G x}
    (hBC : (secondSubconstituentGraph G x).Adj B C) :
    blockIntersection G x B C = 0 := by
  rw [blockIntersection, Finset.card_eq_zero]
  exact Finset.disjoint_iff_inter_eq_empty.mp (localBlock_disjoint_of_adj G hG x hBC)

/--
@isnad1 id=eq.2h5v.s6.9f573f14812c from=translated src=- shape=d34ac22b vocab=5f5f53d1
-/
theorem localIntersectionMatrix_of_adj
    (hG : IsHypothetical G) (x : V)
    {B C : SecondSubconstituent G x}
    (hBC : (secondSubconstituentGraph G x).Adj B C) :
    localIntersectionMatrix G x B C = 0 := by
  rw [localIntersectionMatrix_apply, blockIntersection_of_adj G hG x hBC]
  norm_num

/--
@isnad1 id=le.1h5v.s5.7e0d8f2d2daf from=translated src=- shape=d12a242f vocab=58103005
-/
theorem blockIntersection_le_nine
    (hG : IsHypothetical G) (x : V) (B C : SecondSubconstituent G x) :
    blockIntersection G x B C ≤ 9 := by
  calc
    blockIntersection G x B C =
        (localBlock G x B ∩ localBlock G x C).card := rfl
    _ ≤ (localBlock G x B).card :=
      Finset.card_le_card Finset.inter_subset_left
    _ = 9 := localBlock_card G hG x B

/--
@isnad1 id=eq.1h5v.s8.aa39f1d5bf91 from=translated src=- shape=1fbba0ca vocab=173a895b
-/
theorem localAdjacencyMatrix_sq_apply
    (hG : IsHypothetical G) (x : V) (B C : SecondSubconstituent G x) :
    (localAdjacencyMatrix G x * localAdjacencyMatrix G x) B C =
      if B = C then 36
      else if (secondSubconstituentGraph G x).Adj B C then 0
      else 9 - (blockIntersection G x B C : ℤ) := by
  by_cases hEq : B = C
  · subst C
    rw [ite_eq_left rfl]
    calc
      (localAdjacencyMatrix G x * localAdjacencyMatrix G x) B B =
          (secondSubconstituentGraph G x).degree B := by
        simpa [localAdjacencyMatrix] using
          (secondSubconstituentGraph G x).adjMatrix_mul_self_apply_self (α := ℤ) B
      _ = 36 := by exact_mod_cast secondSubconstituentGraph_degree G hG x B
  · rw [ite_eq_right hEq]
    by_cases hBC : (secondSubconstituentGraph G x).Adj B C
    · rw [ite_eq_left hBC, localAdjacencyMatrix_sq_apply_card_commonNeighbors]
      have htotal :
          Fintype.card (G.commonNeighbors (B : V) (C : V)) = 0 :=
        hG.of_adj B C hBC
      have hdecomp := card_commonNeighbors_decomposition G x B C
      norm_cast
      omega
    · rw [ite_eq_right hBC, localAdjacencyMatrix_sq_apply_card_commonNeighbors,
        card_second_commonNeighbors_of_not_adj G hG x hEq hBC]
      rw [Nat.cast_sub (blockIntersection_le_nine G hG x B C)]
      norm_num

/--
@isnad1 id=eq.1h3v.s8.b3eb80354623 from=translated src=- shape=ba237b19 vocab=0e448d86
-/
theorem localAdjacencyMatrix_sq
    (hG : IsHypothetical G) (x : V) :
    localAdjacencyMatrix G x * localAdjacencyMatrix G x =
      fun B C =>
        (if B = C then (36 : ℤ) else 0) + 9 -
          localIntersectionMatrix G x B C -
          if (secondSubconstituentGraph G x).Adj B C then 9 else 0 := by
  ext B C
  rw [localAdjacencyMatrix_sq_apply G hG x B C]
  by_cases hEq : B = C
  · subst C
    simp [localIntersectionMatrix_diagonal G hG x B]
  · rw [ite_eq_right hEq]
    by_cases hBC : (secondSubconstituentGraph G x).Adj B C
    · rw [ite_eq_left hBC, localIntersectionMatrix_of_adj G hG x hBC]
      have hGBC : G.Adj (B : V) (C : V) := hBC
      simp [hEq, hGBC]
    · rw [ite_eq_right hBC, localIntersectionMatrix_apply]
      have hGBC : ¬G.Adj (B : V) (C : V) := hBC
      simp [hEq, hGBC]

end SRG266
