/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/
module

public import Tengoku.LeanPool.LeanPool.QuantumParallelRepetition.Part03
public import Tengoku

/-! # Quantum parallel repetition, part 04 -/

@[expose] public section

noncomputable section

namespace QuantumParallelRepetition

open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset

section

open scoped BigOperators

/-- The type used to represent source remaining coordinate in the exact sampling construction. -/
abbrev SourceRemainingCoordinate {n : ℕ} (D : Finset (Fin n)) :=
  ↥(Finset.univ \ D)

/-- A permutation of the coordinates outside the revealed set. -/
abbrev SourceRemainingPermutation {n : ℕ} (D : Finset (Fin n)) :=
  Equiv.Perm (SourceRemainingCoordinate D)

/-- Rank the remaining coordinates in the order determined by the permutation. -/
def sourceRemainingPermutationRank
    {n : ℕ} (D : Finset (Fin n))
    (π : SourceRemainingPermutation D) :
    SourceRemainingCoordinate D ≃ Fin (Finset.univ \ D).card :=
  π.symm.trans (Finset.equivFin (Finset.univ \ D))

/-- The remaining coordinate at a given permutation rank, with membership evidence. -/
def sourceRemainingPermutationCoordinateSubtype
    {n : ℕ} (D : Finset (Fin n))
    (π : SourceRemainingPermutation D)
    (k : Fin (Finset.univ \ D).card) :
    SourceRemainingCoordinate D :=
  (sourceRemainingPermutationRank D π).symm k

/-- The coordinate at a given rank in the permutation of unrevealed coordinates. -/
def sourceRemainingPermutationCoordinate
    {n : ℕ} (D : Finset (Fin n))
    (π : SourceRemainingPermutation D)
    (k : Fin (Finset.univ \ D).card) : Fin n :=
  (sourceRemainingPermutationCoordinateSubtype D π k).val

@[simp] private theorem sourceRemainingPermutationRank_coordinate
    {n : ℕ} (D : Finset (Fin n))
    (π : SourceRemainingPermutation D)
    (k : Fin (Finset.univ \ D).card) :
    sourceRemainingPermutationRank D π
      (sourceRemainingPermutationCoordinateSubtype D π k) = k := by
  simp only [sourceRemainingPermutationCoordinateSubtype, Equiv.apply_symm_apply]

/-- The remaining coordinates whose permutation ranks precede the cutoff. -/
def sourceRemainingPermutationPrefixSubtype
    {n : ℕ} (D : Finset (Fin n))
    (π : SourceRemainingPermutation D)
    (k : Fin ((Finset.univ \ D).card + 1)) :
    Finset (SourceRemainingCoordinate D) := by
  classical
  exact Finset.univ.filter fun i =>
    (sourceRemainingPermutationRank D π i).val < k.val

/-- The coordinates preceding the cutoff in the remaining permutation. -/
def sourceRemainingPermutationPrefix
    {n : ℕ} (D : Finset (Fin n))
    (π : SourceRemainingPermutation D)
    (k : Fin ((Finset.univ \ D).card + 1)) : Finset (Fin n) := by
  classical
  exact (sourceRemainingPermutationPrefixSubtype D π k).image
    (fun i : SourceRemainingCoordinate D => i.val)

private theorem sourceRemainingPermutationPrefix_subset
    {n : ℕ} (D : Finset (Fin n))
    (π : SourceRemainingPermutation D)
    (k : Fin ((Finset.univ \ D).card + 1)) :
    sourceRemainingPermutationPrefix D π k ⊆ Finset.univ \ D := by
  classical
  intro i hi
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hi
  simpa only [mem_sdiff, mem_univ, true_and, hj] using j.property

@[simp] private theorem sourceRemainingPermutationPrefix_zero
    {n : ℕ} (D : Finset (Fin n))
    (π : SourceRemainingPermutation D) :
    sourceRemainingPermutationPrefix D π 0 = ∅ := by
  classical
  simp only [sourceRemainingPermutationPrefix, sourceRemainingPermutationPrefixSubtype,
    Fin.coe_ofNat_eq_mod, Nat.zero_mod, not_lt_zero, filter_false, image_empty]

@[simp] private theorem sourceRemainingPermutationPrefix_last
    {n : ℕ} (D : Finset (Fin n))
    (π : SourceRemainingPermutation D) :
    sourceRemainingPermutationPrefix D π
        (Fin.last (Finset.univ \ D).card) =
      Finset.univ \ D := by
  classical
  ext i
  constructor
  · intro hi
    exact sourceRemainingPermutationPrefix_subset D π _ hi
  · intro hi
    apply Finset.mem_image.mpr
    refine ⟨(⟨i, hi⟩ : SourceRemainingCoordinate D), ?_, rfl⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,
      (sourceRemainingPermutationRank D π
        (⟨i, hi⟩ : SourceRemainingCoordinate D)).isLt⟩

section ActualEntropyBudgets

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

private def sourcePermutationAliceEntropyIncrement
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (π : SourceRemainingPermutation D)
    (k : Fin (Finset.univ \ D).card) : ℝ :=
  fullCoordinateAliceTotalEntropyIncrement G n S D
    (sourceRemainingPermutationPrefix D π k.castSucc)
    (sourceRemainingPermutationCoordinate D π k)

private def sourceUniformPermutationAverage
    {n : ℕ} (D : Finset (Fin n))
    (f : SourceRemainingPermutation D →
      Fin (Finset.univ \ D).card → ℝ) : ℝ :=
  (∑ π : SourceRemainingPermutation D,
    ∑ k : Fin (Finset.univ \ D).card, f π k) /
    ((Fintype.card (SourceRemainingPermutation D) : ℝ) *
      ((Finset.univ \ D).card : ℝ))

end ActualEntropyBudgets

end

section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- The exact left construction used in the quantum parallel-repetition argument. -/
def exactLeft
    {M : Type*} [Fintype M] [DecidableEq M]
    (coordinate : M) (partition : M → Bool) : Finset M :=
  Finset.univ.filter fun j => j ≠ coordinate ∧ partition j = false

/-- The exact right construction used in the quantum parallel-repetition argument. -/
def exactRight
    {M : Type*} [Fintype M] [DecidableEq M]
    (coordinate : M) (partition : M → Bool) : Finset M :=
  Finset.univ.filter fun j => j ≠ coordinate ∧ partition j = true

/--
@isnad1 id=not.0h3v.s5.5cde3f68a08c from=translated src=- shape=7fbd8864 vocab=7887a7c7
-/
theorem exactLeft_coordinate_not_mem
    {M : Type*} [Fintype M] [DecidableEq M]
    (coordinate : M) (partition : M → Bool) :
    coordinate ∉ exactLeft coordinate partition := by
  simp only [exactLeft, ne_eq, mem_filter, mem_univ, not_true_eq_false, false_and, and_false,
    not_false_eq_true]

/--
@isnad1 id=not.0h3v.s5.21160c6f304f from=translated src=- shape=7fbd8864 vocab=35204227
-/
theorem exactRight_coordinate_not_mem
    {M : Type*} [Fintype M] [DecidableEq M]
    (coordinate : M) (partition : M → Bool) :
    coordinate ∉ exactRight coordinate partition := by
  simp only [exactRight, ne_eq, mem_filter, mem_univ, not_true_eq_false, false_and, and_false,
    not_false_eq_true]

/-- The coordinate, partition, orders, and cuts sampled by the exact forward process. -/
structure ExactForwardSeed
    (M : Type*) [Fintype M] [DecidableEq M] where
  /-- The marked coordinate of the seed. -/
  coordinate : M
  /-- The binary partition of coordinates carried by the seed. -/
  partition : M → Bool
  /-- The ordering of coordinates on the left side of the partition. -/
  leftOrder : Equiv.Perm
    {j : M // j ∈ exactLeft coordinate partition}
  /-- The ordering of coordinates on the right side of the partition. -/
  rightOrder : Equiv.Perm
    {j : M // j ∈ exactRight coordinate partition}
  /-- The reveal cut in the left-side ordering. -/
  leftCut : Fin ((exactLeft coordinate partition).card + 1)
  /-- The reveal cut in the right-side ordering. -/
  rightCut : Fin ((exactRight coordinate partition).card + 1)
  deriving Fintype

/-- The type used to represent exact remaining seed in the exact sampling construction. -/
abbrev ExactRemainingSeed
    {n : ℕ} (D : Finset (Fin n)) :=
  ExactForwardSeed (SourceRemainingCoordinate D)

/-- The rank map for exact left. -/
def exactLeftRank
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    {j : M // j ∈ exactLeft seed.coordinate seed.partition} ≃
      Fin (exactLeft seed.coordinate seed.partition).card :=
  seed.leftOrder.symm.trans
    (Finset.equivFin (exactLeft seed.coordinate seed.partition))

/-- The rank map for exact right. -/
def exactRightRank
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    {j : M // j ∈ exactRight seed.coordinate seed.partition} ≃
      Fin (exactRight seed.coordinate seed.partition).card :=
  seed.rightOrder.symm.trans
    (Finset.equivFin (exactRight seed.coordinate seed.partition))

/-- The exact left prefix construction used in the quantum parallel-repetition argument. -/
def exactLeftPrefix
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) : Finset M :=
  (Finset.univ.filter
    (fun j : {j : M //
      j ∈ exactLeft seed.coordinate seed.partition} =>
      (exactLeftRank seed j).val < seed.leftCut.val)).image
        Subtype.val

/-- The exact right prefix construction used in the quantum parallel-repetition argument. -/
def exactRightPrefix
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) : Finset M :=
  (Finset.univ.filter
    (fun j : {j : M //
      j ∈ exactRight seed.coordinate seed.partition} =>
      (exactRightRank seed j).val < seed.rightCut.val)).image
        Subtype.val

/-- The probability weight for exact seed. -/
def exactSeedWeight
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) : ℝ :=
  (1 / (Fintype.card M : ℝ)) *
    (1 / (Fintype.card (M → Bool) : ℝ)) *
    (1 / (Fintype.card
      (Equiv.Perm
        {j : M // j ∈
          exactLeft seed.coordinate seed.partition}) : ℝ)) *
    (1 / (Fintype.card
      (Equiv.Perm
        {j : M // j ∈
          exactRight seed.coordinate seed.partition}) : ℝ)) *
    (1 / ((exactLeft
      seed.coordinate seed.partition).card + 1 : ℝ)) *
    (1 / ((exactRight
      seed.coordinate seed.partition).card + 1 : ℝ))

/--
@isnad1 id=le.0h2v.s4.be466fafb768 from=translated src=- shape=abec20dc vocab=65a0584a
-/
theorem exactSeedWeight_nonneg
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    0 ≤ exactSeedWeight seed := by
  unfold exactSeedWeight
  positivity

private abbrev ExactSeedTuple
    (M : Type*) [Fintype M] [DecidableEq M] :=
  Σ i : M, Σ partition : M → Bool,
    (Equiv.Perm {j : M // j ∈ exactLeft i partition}) ×
    (Equiv.Perm {j : M // j ∈ exactRight i partition}) ×
    Fin ((exactLeft i partition).card + 1) ×
    Fin ((exactRight i partition).card + 1)

private def exactSeedEquiv
    (M : Type*) [Fintype M] [DecidableEq M] :
    ExactForwardSeed M ≃ ExactSeedTuple M where
  toFun seed := ⟨seed.coordinate, seed.partition,
    seed.leftOrder, seed.rightOrder, seed.leftCut, seed.rightCut⟩
  invFun t :=
    ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1,
      t.2.2.2.2.1, t.2.2.2.2.2⟩
  left_inv seed := by
    cases seed
    rfl
  right_inv t := by
    rcases t with ⟨i, partition, leftOrder, rightOrder,
      leftCut, rightCut⟩
    rfl

@[simp] private theorem exactSeedEquiv_symm_apply
    {M : Type*} [Fintype M] [DecidableEq M]
    (t : ExactSeedTuple M) :
    (exactSeedEquiv M).symm t =
      ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1,
        t.2.2.2.2.1, t.2.2.2.2.2⟩ := by
  rfl

/--
@isnad1 id=eq.0h2v.s9.caf498f9fa0e from=translated src=- shape=0e97b6bd vocab=fe9cfc6a
-/
theorem exactForwardSeed_sum
    {M : Type*} [Fintype M] [DecidableEq M]
    (f : ExactForwardSeed M → ℝ) :
    (∑ seed : ExactForwardSeed M, f seed) =
      ∑ i : M,
      ∑ partition : M → Bool,
      ∑ leftOrder : Equiv.Perm
        {j : M // j ∈ exactLeft i partition},
      ∑ rightOrder : Equiv.Perm
        {j : M // j ∈ exactRight i partition},
      ∑ leftCut : Fin ((exactLeft i partition).card + 1),
      ∑ rightCut : Fin ((exactRight i partition).card + 1),
        f ⟨i, partition, leftOrder, rightOrder, leftCut, rightCut⟩ := by
  classical
  calc
    (∑ seed : ExactForwardSeed M, f seed) =
        ∑ t : ExactSeedTuple M,
          f ((exactSeedEquiv M).symm t) :=
      ((exactSeedEquiv M).symm.sum_comp f).symm
    _ = _ := by
      simp only [exactSeedEquiv_symm_apply, Fintype.sum_sigma, Fintype.sum_prod_type]

/--
@isnad1 id=eq.1h1v.s5.9b0bd8adf3b7 from=translated src=- shape=3d809ce6 vocab=d7609d09
-/
theorem exactUniform_sum
    {T : Type*} [Fintype T]
    (positive : 0 < Fintype.card T) :
    (∑ _t : T, (1 / (Fintype.card T : ℝ))) = 1 := by
  have hcard : (Fintype.card T : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt positive)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp [hcard]

/--
@isnad1 id=eq.1h2v.s5.4a790ae05c55 from=translated src=- shape=8cf55550 vocab=75dbce51
-/
theorem exactUniform_sum_mul
    {T : Type*} [Fintype T]
    (positive : 0 < Fintype.card T) (value : ℝ) :
    (∑ _t : T,
      value * (1 / (Fintype.card T : ℝ))) = value := by
  rw [← Finset.mul_sum, exactUniform_sum positive]
  ring

/--
@isnad1 id=eq.0h2v.s6.d6c40462fd94 from=translated src=- shape=51ad221b vocab=430b9f8c
-/
theorem exactPrefixUniform_sum_mul
    (m : ℕ) (value : ℝ) :
    (∑ _k : Fin (m + 1),
      value * (1 / ((m : ℝ) + 1))) = value := by
  simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] using
    (exactUniform_sum_mul
      (T := Fin (m + 1)) (by simp only [Fintype.card_fin, lt_add_iff_pos_left,
                               Order.lt_add_one_iff, zero_le]) value)

/--
@isnad1 id=eq.0h2v.s6.a48392d56707 from=translated src=- shape=b130868c vocab=f54d5b49
-/
theorem exactPermutationUniform_sum_mul
    {T : Type*} [Fintype T] (value : ℝ) :
    (∑ _π : Equiv.Perm T,
      value * (1 / (Fintype.card (Equiv.Perm T) : ℝ))) = value := by
  exact exactUniform_sum_mul
    (Fintype.card_pos_iff.mpr ⟨Equiv.refl T⟩) value

end

section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

end

section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

end

section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The measurement effect for conditioned alice coordinate. -/
def conditionedAliceCoordinateEffect
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (α : {j : Fin n // j ∈ D} → A)
    (xs : Fin n → X) (i : Fin n) (a : A) :
    Matrix S.Alice S.Alice ℂ := by
  classical
  exact ∑ answers : Fin n → A,
    if (∀ (j : Fin n) (hj : j ∈ D), answers j = α ⟨j, hj⟩) ∧
      answers i = a
    then (S.aliceMeasurement xs).effect answers
    else 0

/-- The measurement effect for conditioned bob coordinate. -/
def conditionedBobCoordinateEffect
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (β : {j : Fin n // j ∈ D} → B)
    (ys : Fin n → Y) (i : Fin n) (b : B) :
    Matrix S.Bob S.Bob ℂ := by
  classical
  exact ∑ answers : Fin n → B,
    if (∀ (j : Fin n) (hj : j ∈ D), answers j = β ⟨j, hj⟩) ∧
      answers i = b
    then (S.bobMeasurement ys).effect answers
    else 0

/--
@isnad1 id=possemid.0h12v.s8.536b8201f292 from=translated src=- shape=863b4185 vocab=7c8ac64c
-/
theorem conditionedAliceCoordinateEffect_posSemidef
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (α : {j : Fin n // j ∈ D} → A)
    (xs : Fin n → X) (i : Fin n) (a : A) :
    (conditionedAliceCoordinateEffect G n S D α xs i a).PosSemidef := by
  classical
  unfold conditionedAliceCoordinateEffect
  apply Matrix.posSemidef_sum Finset.univ
  intro answers _
  split_ifs
  · exact (S.aliceMeasurement xs).positive answers
  · exact Matrix.PosSemidef.zero

/--
@isnad1 id=possemid.0h12v.s8.0f4588c5e966 from=translated src=- shape=68a24475 vocab=5f95bd74
-/
theorem conditionedBobCoordinateEffect_posSemidef
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (β : {j : Fin n // j ∈ D} → B)
    (ys : Fin n → Y) (i : Fin n) (b : B) :
    (conditionedBobCoordinateEffect G n S D β ys i b).PosSemidef := by
  classical
  unfold conditionedBobCoordinateEffect
  apply Matrix.posSemidef_sum Finset.univ
  intro answers _
  split_ifs
  · exact (S.bobMeasurement ys).positive answers
  · exact Matrix.PosSemidef.zero

/--
@isnad1 id=eq.0h11v.s9.6045c789a662 from=translated src=- shape=a2cbb5ea vocab=ee3c8e2c
-/
theorem conditionedAliceCoordinateEffect_sum
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (α : {j : Fin n // j ∈ D} → A)
    (xs : Fin n → X) (i : Fin n) :
    (∑ a : A, conditionedAliceCoordinateEffect G n S D α xs i a) =
      conditionedAliceEffect G n S D α xs := by
  classical
  unfold conditionedAliceCoordinateEffect conditionedAliceEffect
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro answers _
  calc
    (∑ a : A,
      if (∀ (j : Fin n) (hj : j ∈ D), answers j = α ⟨j, hj⟩) ∧
        answers i = a
      then (S.aliceMeasurement xs).effect answers
      else 0) =
      if (∀ (j : Fin n) (hj : j ∈ D), answers j = α ⟨j, hj⟩) ∧
        answers i = answers i
      then (S.aliceMeasurement xs).effect answers
      else 0 := by
        apply Fintype.sum_eq_single (answers i)
        intro a ha
        simp only [ha.symm, and_false, ↓reduceIte]
    _ = _ := by simp only [and_true]

/--
@isnad1 id=eq.0h11v.s9.aaa0cd620cdb from=translated src=- shape=2141061f vocab=43508cce
-/
theorem conditionedBobCoordinateEffect_sum
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (β : {j : Fin n // j ∈ D} → B)
    (ys : Fin n → Y) (i : Fin n) :
    (∑ b : B, conditionedBobCoordinateEffect G n S D β ys i b) =
      conditionedBobEffect G n S D β ys := by
  classical
  unfold conditionedBobCoordinateEffect conditionedBobEffect
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro answers _
  calc
    (∑ b : B,
      if (∀ (j : Fin n) (hj : j ∈ D), answers j = β ⟨j, hj⟩) ∧
        answers i = b
      then (S.bobMeasurement ys).effect answers
      else 0) =
      if (∀ (j : Fin n) (hj : j ∈ D), answers j = β ⟨j, hj⟩) ∧
        answers i = answers i
      then (S.bobMeasurement ys).effect answers
      else 0 := by
        apply Fintype.sum_eq_single (answers i)
        intro b hb
        simp only [hb.symm, and_false, ↓reduceIte]
    _ = _ := by simp only [and_true]

/-- Alice's coordinate effect averaged over the questions hidden by the history. -/
def fullHistoryAliceCoordinateEffect
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n))
    (h : FullSubsetHistory X Y n D L)
    (α : {j : Fin n // j ∈ D} → A)
    (i : Fin n) (a : A) :
    Matrix S.Alice S.Alice ℂ :=
  ∑ hidden : {j : Fin n // j ∈ fullHistoryRemaining n D L} → X,
    fullHistoryHiddenAliceWeight G h hidden •
      conditionedAliceCoordinateEffect G n S D α
        (fullHistoryAliceQuestion h hidden) i a

/-- Bob's coordinate effect averaged over the questions hidden by the history. -/
def fullHistoryBobCoordinateEffect
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n))
    (h : FullSubsetHistory X Y n D L)
    (β : {j : Fin n // j ∈ D} → B)
    (i : Fin n) (b : B) :
    Matrix S.Bob S.Bob ℂ :=
  ∑ hidden : {j : Fin n // j ∈ L} → Y,
    fullHistoryHiddenBobWeight G h hidden •
      conditionedBobCoordinateEffect G n S D β
        (fullHistoryBobQuestion h hidden) i b

/-- Alice's coordinate effect after extending the history with the new question. -/
def fullCoordinateAliceRefinementEffect
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n)) (i : Fin n)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (α : {j : Fin n // j ∈ D} → A)
    (x : X) (a : A) : Matrix S.Alice S.Alice ℂ :=
  fullHistoryAliceCoordinateEffect G n S D (insert i L)
    (fullCoordinateNewHistory D L i r x) α i a

/-- Bob's coordinate effect for the selected question and previous history. -/
def fullCoordinateBobRefinementEffect
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n)) (i : Fin n)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (β : {j : Fin n // j ∈ D} → B)
    (y : Y) (b : B) : Matrix S.Bob S.Bob ℂ :=
  fullHistoryBobCoordinateEffect G n S D L
    (fullCoordinateOldHistory D L i r y) β i b

end

section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The exact conditioned transcript associated with a forward seed. -/
structure ExactRevealHistory
    (X Y : Type*) [Fintype X] [Fintype Y]
    {n : ℕ} (D : Finset (Fin n))
    (seed : ExactRemainingSeed D) where
  /-- Alice's questions on conditioned coordinates. -/
  aliceConditioned : {j : Fin n // j ∈ D} → X
  /-- Bob's questions on conditioned coordinates. -/
  bobConditioned : {j : Fin n // j ∈ D} → Y
  /-- Alice's questions revealed on the left side. -/
  aliceLeft :
    {j : SourceRemainingCoordinate D //
      j ∈ exactLeft seed.coordinate seed.partition} → X
  /-- Bob's questions revealed on the right side. -/
  bobRight :
    {j : SourceRemainingCoordinate D //
      j ∈ exactRight seed.coordinate seed.partition} → Y
  /-- Bob's revealed prefix on the left side. -/
  bobLeftPrefix :
    {j : SourceRemainingCoordinate D //
      j ∈ exactLeftPrefix seed} → Y
  /-- Alice's revealed prefix on the right side. -/
  aliceRightPrefix :
    {j : SourceRemainingCoordinate D //
      j ∈ exactRightPrefix seed} → X

/-- The type used to represent exact reveal history tuple in the exact sampling construction. -/
abbrev ExactRevealHistoryTuple
    (X Y : Type*)
    {n : ℕ} (D : Finset (Fin n))
    (seed : ExactRemainingSeed D) :=
  ({j : Fin n // j ∈ D} → X) ×
  ({j : Fin n // j ∈ D} → Y) ×
  ({j : SourceRemainingCoordinate D //
      j ∈ exactLeft seed.coordinate seed.partition} → X) ×
  ({j : SourceRemainingCoordinate D //
      j ∈ exactRight seed.coordinate seed.partition} → Y) ×
  ({j : SourceRemainingCoordinate D //
      j ∈ exactLeftPrefix seed} → Y) ×
  ({j : SourceRemainingCoordinate D //
      j ∈ exactRightPrefix seed} → X)

/-- The finite equivalence encoding exact reveal history. -/
def exactRevealHistoryEquiv
    {n : ℕ} (D : Finset (Fin n))
    (seed : ExactRemainingSeed D) :
    ExactRevealHistory X Y D seed ≃
      ExactRevealHistoryTuple X Y D seed where
  toFun h := ⟨h.aliceConditioned, h.bobConditioned,
    h.aliceLeft, h.bobRight, h.bobLeftPrefix, h.aliceRightPrefix⟩
  invFun t := ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1,
    t.2.2.2.2.1, t.2.2.2.2.2⟩
  left_inv h := by cases h; rfl
  right_inv t := by
    rcases t with ⟨ac, bc, al, br, bl, ar⟩
    rfl

noncomputable instance exactRevealHistoryFintype
    {n : ℕ} (D : Finset (Fin n))
    (seed : ExactRemainingSeed D) :
    Fintype (ExactRevealHistory X Y D seed) := by
  classical
  exact Fintype.ofEquiv (ExactRevealHistoryTuple X Y D seed)
    (exactRevealHistoryEquiv
      (X := X) (Y := Y) D seed).symm

/-- The type used to represent exact full question in the exact sampling construction. -/
abbrev ExactFullQuestion
    (X Y : Type*) (n : ℕ) :=
  (Fin n → X) × (Fin n → Y)

/-- The finite encoding of exact reveal. -/
def exactRevealCode
    {n : ℕ} (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (q : ExactFullQuestion X Y n) :
    ExactRevealHistory X Y D seed where
  aliceConditioned j := q.1 j.val
  bobConditioned j := q.2 j.val
  aliceLeft j := q.1 j.val.val
  bobRight j := q.2 j.val.val
  bobLeftPrefix j := q.2 j.val.val
  aliceRightPrefix j := q.1 j.val.val

/-- The probability weight for exact prior question. -/
def exactPriorQuestionWeight
    (G : Game X Y A B) (n : ℕ)
    (q : ExactFullQuestion X Y n) : ℝ :=
  (G.repeat n).questionWeight q.1 q.2

/--
@isnad1 id=le.0h7v.s5.4a34e2a019bf from=translated src=- shape=7518765b vocab=14771889
-/
theorem exactPriorQuestionWeight_nonneg
    (G : Game X Y A B) (n : ℕ)
    (q : ExactFullQuestion X Y n) :
    0 ≤ exactPriorQuestionWeight G n q :=
  (G.repeat n).weight_nonneg q.1 q.2

/-- The total probability mass of exact reveal. -/
def exactRevealMass
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed) : ℝ :=
  ∑ q : ExactFullQuestion X Y n,
    if exactRevealCode D seed q = history
    then exactPriorQuestionWeight G n q
    else 0

/-- The total probability mass of exact alice question. -/
def exactAliceQuestionMass
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) : ℝ :=
  ∑ q : ExactFullQuestion X Y n,
    if exactRevealCode D seed q = history ∧
      q.1 seed.coordinate.val = x
    then exactPriorQuestionWeight G n q
    else 0

/-- The total probability mass of exact bob question. -/
def exactBobQuestionMass
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (y : Y) : ℝ :=
  ∑ q : ExactFullQuestion X Y n,
    if exactRevealCode D seed q = history ∧
      q.2 seed.coordinate.val = y
    then exactPriorQuestionWeight G n q
    else 0

/-- The total probability mass of exact joint question. -/
def exactJointQuestionMass
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) (y : Y) : ℝ :=
  ∑ q : ExactFullQuestion X Y n,
    if exactRevealCode D seed q = history ∧
      q.1 seed.coordinate.val = x ∧
      q.2 seed.coordinate.val = y
    then exactPriorQuestionWeight G n q
    else 0

/--
@isnad1 id=le.0h10v.s6.e5635c2d1191 from=translated src=- shape=b4e67307 vocab=dc1cf13b
-/
theorem exactAliceQuestionMass_nonneg
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) :
    0 ≤ exactAliceQuestionMass G n D seed history x := by
  unfold exactAliceQuestionMass
  apply Finset.sum_nonneg
  intro q _
  split
  · exact exactPriorQuestionWeight_nonneg G n q
  · exact le_rfl

/--
@isnad1 id=le.0h10v.s6.f6701d9ad0a7 from=translated src=- shape=52bf1fde vocab=5f7ef980
-/
theorem exactBobQuestionMass_nonneg
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (y : Y) :
    0 ≤ exactBobQuestionMass G n D seed history y := by
  unfold exactBobQuestionMass
  apply Finset.sum_nonneg
  intro q _
  split
  · exact exactPriorQuestionWeight_nonneg G n q
  · exact le_rfl

/-- The spectral filter for exact alice question. -/
def exactAliceQuestionFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → A)
    (x : X) : Matrix S.Alice S.Alice ℂ :=
  ∑ q : ExactFullQuestion X Y n,
    if exactRevealCode D seed q = history ∧
      q.1 seed.coordinate.val = x
    then
      (exactPriorQuestionWeight G n q /
        exactAliceQuestionMass G n D seed history x) •
        conditionedAliceEffect G n S D answer q.1
    else 0

/-- The spectral filter for exact bob question. -/
def exactBobQuestionFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → B)
    (y : Y) : Matrix S.Bob S.Bob ℂ :=
  ∑ q : ExactFullQuestion X Y n,
    if exactRevealCode D seed q = history ∧
      q.2 seed.coordinate.val = y
    then
      (exactPriorQuestionWeight G n q /
        exactBobQuestionMass G n D seed history y) •
        conditionedBobEffect G n S D answer q.2
    else 0

/--
@isnad1 id=possemid.0h12v.s8.8a3b170f5a8a from=translated src=- shape=5fe9d83f vocab=aac1e012
-/
theorem exactAliceQuestionFilter_posSemidef
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → A)
    (x : X) :
    (exactAliceQuestionFilter
      G n S D seed history answer x).PosSemidef := by
  unfold exactAliceQuestionFilter
  apply Matrix.posSemidef_sum Finset.univ
  intro q _
  split
  · exact (conditionedAliceEffect_positive G n S D answer q.1).smul
      (div_nonneg
        (exactPriorQuestionWeight_nonneg G n q)
        (exactAliceQuestionMass_nonneg
          G n D seed history x))
  · exact Matrix.PosSemidef.zero

/--
@isnad1 id=possemid.0h12v.s8.8c5072c85a0d from=translated src=- shape=59a8e3e9 vocab=bf88dc80
-/
theorem exactBobQuestionFilter_posSemidef
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → B)
    (y : Y) :
    (exactBobQuestionFilter
      G n S D seed history answer y).PosSemidef := by
  unfold exactBobQuestionFilter
  apply Matrix.posSemidef_sum Finset.univ
  intro q _
  split
  · exact (conditionedBobEffect_positive G n S D answer q.2).smul
      (div_nonneg
        (exactPriorQuestionWeight_nonneg G n q)
        (exactBobQuestionMass_nonneg
          G n D seed history y))
  · exact Matrix.PosSemidef.zero

/-- The spectral filter for exact alice mean. -/
def exactAliceMeanFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → A)
    (y : Y) : Matrix S.Alice S.Alice ℂ :=
  ∑ x : X, G.conditionalXGivenY y x •
    exactAliceQuestionFilter G n S D seed history answer x

/-- The spectral filter for exact bob mean. -/
def exactBobMeanFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → B)
    (x : X) : Matrix S.Bob S.Bob ℂ :=
  ∑ y : Y, G.conditionalYGivenX x y •
    exactBobQuestionFilter G n S D seed history answer y

/--
@isnad1 id=possemid.0h12v.s8.79a7f3018bcd from=translated src=- shape=5bb585e2 vocab=87077dcb
-/
theorem exactAliceMeanFilter_posSemidef
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → A)
    (y : Y) :
    (exactAliceMeanFilter
      G n S D seed history answer y).PosSemidef := by
  unfold exactAliceMeanFilter
  apply Matrix.posSemidef_sum Finset.univ
  intro x _
  exact (exactAliceQuestionFilter_posSemidef
    G n S D seed history answer x).smul
    (G.conditionalXGivenY_nonneg y x)

/--
@isnad1 id=possemid.0h12v.s8.4ed9b66b9947 from=translated src=- shape=578801f0 vocab=882665db
-/
theorem exactBobMeanFilter_posSemidef
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → B)
    (x : X) :
    (exactBobMeanFilter
      G n S D seed history answer x).PosSemidef := by
  unfold exactBobMeanFilter
  apply Matrix.posSemidef_sum Finset.univ
  intro y _
  exact (exactBobQuestionFilter_posSemidef
    G n S D seed history answer y).smul
    (G.conditionalYGivenX_nonneg x y)

/-- The spectral filter for exact alice coordinate. -/
def exactAliceCoordinateFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → A)
    (x : X) (a : A) : Matrix S.Alice S.Alice ℂ :=
  ∑ q : ExactFullQuestion X Y n,
    if exactRevealCode D seed q = history ∧
      q.1 seed.coordinate.val = x
    then
      (exactPriorQuestionWeight G n q /
        exactAliceQuestionMass G n D seed history x) •
        conditionedAliceCoordinateEffect G n S D answer q.1
          seed.coordinate.val a
    else 0

/-- The spectral filter for exact bob coordinate. -/
def exactBobCoordinateFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → B)
    (y : Y) (b : B) : Matrix S.Bob S.Bob ℂ :=
  ∑ q : ExactFullQuestion X Y n,
    if exactRevealCode D seed q = history ∧
      q.2 seed.coordinate.val = y
    then
      (exactPriorQuestionWeight G n q /
        exactBobQuestionMass G n D seed history y) •
        conditionedBobCoordinateEffect G n S D answer q.2
          seed.coordinate.val b
    else 0

/--
@isnad1 id=possemid.0h13v.s8.e2d080474995 from=translated src=- shape=cd843239 vocab=e6a79798
-/
theorem exactAliceCoordinateFilter_posSemidef
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → A)
    (x : X) (a : A) :
    (exactAliceCoordinateFilter
      G n S D seed history answer x a).PosSemidef := by
  unfold exactAliceCoordinateFilter
  apply Matrix.posSemidef_sum Finset.univ
  intro q _
  split
  · exact (conditionedAliceCoordinateEffect_posSemidef
      G n S D answer q.1 seed.coordinate.val a).smul
      (div_nonneg
        (exactPriorQuestionWeight_nonneg G n q)
        (exactAliceQuestionMass_nonneg
          G n D seed history x))
  · exact Matrix.PosSemidef.zero

/--
@isnad1 id=possemid.0h13v.s8.0c2a1dbdd53f from=translated src=- shape=c15d6b5e vocab=b440cf2c
-/
theorem exactBobCoordinateFilter_posSemidef
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → B)
    (y : Y) (b : B) :
    (exactBobCoordinateFilter
      G n S D seed history answer y b).PosSemidef := by
  unfold exactBobCoordinateFilter
  apply Matrix.posSemidef_sum Finset.univ
  intro q _
  split
  · exact (conditionedBobCoordinateEffect_posSemidef
      G n S D answer q.2 seed.coordinate.val b).smul
      (div_nonneg
        (exactPriorQuestionWeight_nonneg G n q)
        (exactBobQuestionMass_nonneg
          G n D seed history y))
  · exact Matrix.PosSemidef.zero

/--
@isnad1 id=eq.0h12v.s9.04db1495b9ac from=translated src=- shape=f7fe95d5 vocab=05745a90
-/
theorem exactAliceCoordinateFilter_sum
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → A)
    (x : X) :
    (∑ a : A,
      exactAliceCoordinateFilter
        G n S D seed history answer x a) =
      exactAliceQuestionFilter
        G n S D seed history answer x := by
  classical
  unfold exactAliceCoordinateFilter
    exactAliceQuestionFilter
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : exactRevealCode D seed q = history ∧
      q.1 seed.coordinate.val = x
  · simp only [hq, and_self, ↓reduceIte, ← smul_sum, conditionedAliceCoordinateEffect_sum]
  · simp only [hq, ↓reduceIte, sum_const_zero]

/--
@isnad1 id=eq.0h12v.s9.3243d4015a0f from=translated src=- shape=c9a3c252 vocab=72c5e9cd
-/
theorem exactBobCoordinateFilter_sum
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → B)
    (y : Y) :
    (∑ b : B,
      exactBobCoordinateFilter
        G n S D seed history answer y b) =
      exactBobQuestionFilter
        G n S D seed history answer y := by
  classical
  unfold exactBobCoordinateFilter
    exactBobQuestionFilter
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : exactRevealCode D seed q = history ∧
      q.2 seed.coordinate.val = y
  · simp only [hq, and_self, ↓reduceIte, ← smul_sum, conditionedBobCoordinateEffect_sum]
  · simp only [hq, ↓reduceIte, sum_const_zero]

/--
The exact alice purification family construction used in the quantum parallel-repetition
argument.
-/
def exactAlicePurificationFamily
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → A) :
    Sum X Y → Matrix S.Alice S.Alice ℂ :=
  Sum.elim
    (exactAliceQuestionFilter G n S D seed history answer)
    (exactAliceMeanFilter G n S D seed history answer)

/--
The exact bob purification family construction used in the quantum parallel-repetition argument.
-/
def exactBobPurificationFamily
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → B) :
    Sum Y X → Matrix S.Bob S.Bob ℂ :=
  Sum.elim
    (exactBobQuestionFilter G n S D seed history answer)
    (exactBobMeanFilter G n S D seed history answer)

/--
@isnad1 id=possemid.0h12v.s8.2fae97656926 from=translated src=- shape=ff5fa001 vocab=83b626d3
-/
theorem exactAlicePurificationFamily_posSemidef
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → A)
    (q : Sum X Y) :
    (exactAlicePurificationFamily
      G n S D seed history answer q).PosSemidef := by
  cases q with
  | inl x =>
      exact exactAliceQuestionFilter_posSemidef
        G n S D seed history answer x
  | inr y =>
      exact exactAliceMeanFilter_posSemidef
        G n S D seed history answer y

/--
@isnad1 id=possemid.0h12v.s8.df8a561865d3 from=translated src=- shape=6f0c2640 vocab=07cc27a6
-/
theorem exactBobPurificationFamily_posSemidef
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → B)
    (q : Sum Y X) :
    (exactBobPurificationFamily
      G n S D seed history answer q).PosSemidef := by
  cases q with
  | inl y =>
      exact exactBobQuestionFilter_posSemidef
        G n S D seed history answer y
  | inr x =>
      exact exactBobMeanFilter_posSemidef
        G n S D seed history answer x

/-- The type used to represent exact alice lift index in the exact sampling construction. -/
abbrev ExactAliceLiftIndex
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → A) :=
  S.Alice × Fin (Module.finrank ℂ
    (commonPurificationSubspace
      (exactAlicePurificationFamily
        G n S D seed history answer)
      (0 : Matrix S.Alice S.Alice ℂ)
      (exactAlicePurificationFamily_posSemidef
        G n S D seed history answer)
      Matrix.PosSemidef.zero))

/-- The type used to represent exact bob lift index in the exact sampling construction. -/
abbrev ExactBobLiftIndex
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → B) :=
  S.Bob × Fin (Module.finrank ℂ
    (commonPurificationSubspace
      (exactBobPurificationFamily
        G n S D seed history answer)
      (0 : Matrix S.Bob S.Bob ℂ)
      (exactBobPurificationFamily_posSemidef
        G n S D seed history answer)
      Matrix.PosSemidef.zero))

/-- The matrix representation of exact alice purification. -/
def exactAlicePurificationMatrix
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → A)
    (q : Sum X Y) :
    Matrix (ExactAliceLiftIndex
      G n S D seed history answer) S.Alice ℂ :=
  finitePurificationMatrix
    (exactAlicePurificationFamily
      G n S D seed history answer)
    0
    (exactAlicePurificationFamily_posSemidef
      G n S D seed history answer)
    Matrix.PosSemidef.zero q

/-- The matrix representation of exact bob purification. -/
def exactBobPurificationMatrix
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → B)
    (q : Sum Y X) :
    Matrix (ExactBobLiftIndex
      G n S D seed history answer) S.Bob ℂ :=
  finitePurificationMatrix
    (exactBobPurificationFamily
      G n S D seed history answer)
    0
    (exactBobPurificationFamily_posSemidef
      G n S D seed history answer)
    Matrix.PosSemidef.zero q

/--
@isnad1 id=eq.0h12v.s14.d7c2ba9427da from=translated src=- shape=407e499c vocab=f257945e
-/
theorem exactAlicePurificationMatrix_gram
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → A)
    (q : Sum X Y) :
    (exactAlicePurificationMatrix
      G n S D seed history answer q).conjTranspose *
      exactAlicePurificationMatrix
        G n S D seed history answer q =
      exactAlicePurificationFamily
        G n S D seed history answer q :=
  finitePurificationMatrix_gram
    (exactAlicePurificationFamily
      G n S D seed history answer)
    0
    (exactAlicePurificationFamily_posSemidef
      G n S D seed history answer)
    Matrix.PosSemidef.zero q

/--
@isnad1 id=eq.0h12v.s14.85428105ef1a from=translated src=- shape=bd0cae5e vocab=45b5b78f
-/
theorem exactBobPurificationMatrix_gram
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → B)
    (q : Sum Y X) :
    (exactBobPurificationMatrix
      G n S D seed history answer q).conjTranspose *
      exactBobPurificationMatrix
        G n S D seed history answer q =
      exactBobPurificationFamily
        G n S D seed history answer q :=
  finitePurificationMatrix_gram
    (exactBobPurificationFamily
      G n S D seed history answer)
    0
    (exactBobPurificationFamily_posSemidef
      G n S D seed history answer)
    Matrix.PosSemidef.zero q

/-- A seed and transcript together with the answers at its marked coordinate. -/
@[ext (iff := false)] structure ExactHistoryFlag
    (X Y A B : Type*)
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {n : ℕ} (D : Finset (Fin n)) where
  /-- The forward seed carried by the flag. -/
  seed : ExactRemainingSeed D
  /-- The exact reveal history carried by the flag. -/
  history : ExactRevealHistory X Y D seed
  /-- Alice's answer at the marked coordinate. -/
  aliceAnswer : {j : Fin n // j ∈ D} → A
  /-- Bob's answer at the marked coordinate. -/
  bobAnswer : {j : Fin n // j ∈ D} → B

/-- The type used to represent exact history flag tuple in the exact sampling construction. -/
abbrev ExactHistoryFlagTuple
    (X Y A B : Type*)
    [Fintype X] [Fintype Y]
    {n : ℕ} (D : Finset (Fin n)) :=
  Σ seed : ExactRemainingSeed D,
    ExactRevealHistory X Y D seed ×
      ({j : Fin n // j ∈ D} → A) ×
      ({j : Fin n // j ∈ D} → B)

/-- The finite equivalence encoding exact history flag. -/
def exactHistoryFlagEquiv
    {n : ℕ} (D : Finset (Fin n)) :
    ExactHistoryFlag X Y A B D ≃
      ExactHistoryFlagTuple X Y A B D where
  toFun r := ⟨r.seed, r.history, r.aliceAnswer, r.bobAnswer⟩
  invFun t := ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩
  left_inv r := by cases r; rfl
  right_inv t := by
    rcases t with ⟨seed, history, aliceAnswer, bobAnswer⟩
    rfl

noncomputable instance exactHistoryFlagFintype
    {n : ℕ} (D : Finset (Fin n)) :
    Fintype (ExactHistoryFlag X Y A B D) := by
  classical
  exact Fintype.ofEquiv (ExactHistoryFlagTuple X Y A B D)
    (exactHistoryFlagEquiv
      (X := X) (Y := Y) (A := A) (B := B) D).symm

/-- The type used to represent exact alice local index in the exact sampling construction. -/
abbrev ExactAliceLocalIndex
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) :=
  ExactAliceLiftIndex
    G n S D r.seed r.history r.aliceAnswer × (S.Alice × S.Bob)

/-- The type used to represent exact bob local index in the exact sampling construction. -/
abbrev ExactBobLocalIndex
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) :=
  ExactBobLiftIndex
    G n S D r.seed r.history r.bobAnswer

/-- The exact unnormalized psi construction used in the quantum parallel-repetition argument. -/
def exactUnnormalizedPsi
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (x : X) (y : Y) :
    EuclideanSpace ℂ
      (ExactAliceLocalIndex G n S D r ×
        ExactBobLocalIndex G n S D r) :=
  finiteLocalPurificationVector S
    (exactAlicePurificationMatrix
      G n S D r.seed r.history r.aliceAnswer (.inl x))
    (exactBobPurificationMatrix
      G n S D r.seed r.history r.bobAnswer (.inl y))

/-- The exact unnormalized phi construction used in the quantum parallel-repetition argument. -/
def exactUnnormalizedPhi
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (y : Y) :
    EuclideanSpace ℂ
      (ExactAliceLocalIndex G n S D r ×
        ExactBobLocalIndex G n S D r) :=
  finiteLocalPurificationVector S
    (exactAlicePurificationMatrix
      G n S D r.seed r.history r.aliceAnswer (.inr y))
    (exactBobPurificationMatrix
      G n S D r.seed r.history r.bobAnswer (.inl y))

/-- The exact unnormalized gamma construction used in the quantum parallel-repetition argument. -/
def exactUnnormalizedGamma
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (x : X) :
    EuclideanSpace ℂ
      (ExactAliceLocalIndex G n S D r ×
        ExactBobLocalIndex G n S D r) :=
  finiteLocalPurificationVector S
    (exactAlicePurificationMatrix
      G n S D r.seed r.history r.aliceAnswer (.inl x))
    (exactBobPurificationMatrix
      G n S D r.seed r.history r.bobAnswer (.inr x))

/--
@isnad1 id=eq.0h10v.s14.628ea762707d from=translated src=- shape=0e10368d vocab=5e0227cd
-/
theorem exactAliceQuestionPurificationMatrix_gram
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (x : X) :
    (exactAlicePurificationMatrix
      G n S D r.seed r.history r.aliceAnswer (.inl x)).conjTranspose *
      exactAlicePurificationMatrix
        G n S D r.seed r.history r.aliceAnswer (.inl x) =
      exactAliceQuestionFilter
        G n S D r.seed r.history r.aliceAnswer x :=
  exactAlicePurificationMatrix_gram
    G n S D r.seed r.history r.aliceAnswer (.inl x)

/--
@isnad1 id=eq.0h10v.s14.f03be92d5dcf from=translated src=- shape=5b138cc1 vocab=3f6e0604
-/
theorem exactBobQuestionPurificationMatrix_gram
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (y : Y) :
    (exactBobPurificationMatrix
      G n S D r.seed r.history r.bobAnswer (.inl y)).conjTranspose *
      exactBobPurificationMatrix
        G n S D r.seed r.history r.bobAnswer (.inl y) =
      exactBobQuestionFilter
        G n S D r.seed r.history r.bobAnswer y :=
  exactBobPurificationMatrix_gram
    G n S D r.seed r.history r.bobAnswer (.inl y)

/-- The positive operator-valued measurement implementing exact alice refined. -/
def exactAliceRefinedPOVM
    [DecidableEq A]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (a₀ : A) (x : X) :
    POVM A (ExactAliceLiftIndex
      G n S D r.seed r.history r.aliceAnswer) :=
  purifiedRefinedPOVM
    (exactAliceQuestionFilter
      G n S D r.seed r.history r.aliceAnswer x)
    (exactAliceQuestionFilter_posSemidef
      G n S D r.seed r.history r.aliceAnswer x)
    (exactAlicePurificationMatrix
      G n S D r.seed r.history r.aliceAnswer (.inl x))
    (exactAliceQuestionPurificationMatrix_gram G n S D r x)
    (exactAliceCoordinateFilter
      G n S D r.seed r.history r.aliceAnswer x)
    (exactAliceCoordinateFilter_posSemidef
      G n S D r.seed r.history r.aliceAnswer x)
    (exactAliceCoordinateFilter_sum
      G n S D r.seed r.history r.aliceAnswer x)
    a₀

/-- The positive operator-valued measurement implementing exact bob refined. -/
def exactBobRefinedPOVM
    [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (b₀ : B) (y : Y) :
    POVM B (ExactBobLiftIndex
      G n S D r.seed r.history r.bobAnswer) :=
  purifiedRefinedPOVM
    (exactBobQuestionFilter
      G n S D r.seed r.history r.bobAnswer y)
    (exactBobQuestionFilter_posSemidef
      G n S D r.seed r.history r.bobAnswer y)
    (exactBobPurificationMatrix
      G n S D r.seed r.history r.bobAnswer (.inl y))
    (exactBobQuestionPurificationMatrix_gram G n S D r y)
    (exactBobCoordinateFilter
      G n S D r.seed r.history r.bobAnswer y)
    (exactBobCoordinateFilter_posSemidef
      G n S D r.seed r.history r.bobAnswer y)
    (exactBobCoordinateFilter_sum
      G n S D r.seed r.history r.bobAnswer y)
    b₀

/-- The type used to represent exact padded local index in the exact sampling construction. -/
abbrev ExactPaddedLocalIndex
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) :=
  PUnit.{1} ⊕
    (ExactAliceLocalIndex G n S D r ⊕
      ExactBobLocalIndex G n S D r)

/-- The state vector representing exact padded. -/
def exactPaddedVector
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (z : EuclideanSpace ℂ
      (ExactAliceLocalIndex G n S D r ×
        ExactBobLocalIndex G n S D r)) :
    EuclideanSpace ℂ
      (ExactPaddedLocalIndex G n S D r ×
        ExactPaddedLocalIndex G n S D r) :=
  toLp 2 fun q =>
    match q.1, q.2 with
    | .inr (.inl a), .inr (.inr b) => z (a, b)
    | _, _ => 0

/-- The exact padded default construction used in the quantum parallel-repetition argument. -/
def exactPaddedDefault
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) :
    EuclideanSpace ℂ
      (ExactPaddedLocalIndex G n S D r ×
        ExactPaddedLocalIndex G n S D r) := by
  classical
  exact PiLp.single 2 (.inl PUnit.unit, .inl PUnit.unit) (1 : ℂ)

/--
@isnad1 id=eq.0h9v.s16.82b2d4fd9bb7 from=translated src=- shape=11ce7f33 vocab=5f2f9c39
-/
theorem exactPaddedDefault_norm
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) :
    ‖exactPaddedDefault G n S D r‖ = 1 := by
  classical
  simp only [exactPaddedDefault, PiLp.norm_single, norm_one]

/-- The exact psi construction used in the quantum parallel-repetition argument. -/
def exactPsi
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (x : X) (y : Y) :
    EuclideanSpace ℂ
      (ExactPaddedLocalIndex G n S D r ×
        ExactPaddedLocalIndex G n S D r) :=
  normalizeOrDefault (exactPaddedDefault G n S D r)
    (exactPaddedVector G n S D r
      (exactUnnormalizedPsi G n S D r x y))

/-- The exact phi construction used in the quantum parallel-repetition argument. -/
def exactPhi
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (y : Y) :
    EuclideanSpace ℂ
      (ExactPaddedLocalIndex G n S D r ×
        ExactPaddedLocalIndex G n S D r) :=
  normalizeOrDefault (exactPaddedDefault G n S D r)
    (exactPaddedVector G n S D r
      (exactUnnormalizedPhi G n S D r y))

/-- The exact gamma construction used in the quantum parallel-repetition argument. -/
def exactGamma
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (x : X) :
    EuclideanSpace ℂ
      (ExactPaddedLocalIndex G n S D r ×
        ExactPaddedLocalIndex G n S D r) :=
  normalizeOrDefault (exactPaddedDefault G n S D r)
    (exactPaddedVector G n S D r
      (exactUnnormalizedGamma G n S D r x))

end

section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/--
The exact alice question compatible construction used in the quantum parallel-repetition
argument.
-/
def exactAliceQuestionCompatible
    {n : ℕ} (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) (xs : Fin n → X) : Prop :=
  (∀ j : {j : Fin n // j ∈ D},
      xs j.val = history.aliceConditioned j) ∧
  (∀ j : {j : SourceRemainingCoordinate D //
      j ∈ exactLeft seed.coordinate seed.partition},
      xs j.val.val = history.aliceLeft j) ∧
  (∀ j : {j : SourceRemainingCoordinate D //
      j ∈ exactRightPrefix seed},
      xs j.val.val = history.aliceRightPrefix j) ∧
  xs seed.coordinate.val = x

/--
The exact bob question compatible construction used in the quantum parallel-repetition argument.
-/
def exactBobQuestionCompatible
    {n : ℕ} (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (y : Y) (ys : Fin n → Y) : Prop :=
  (∀ j : {j : Fin n // j ∈ D},
      ys j.val = history.bobConditioned j) ∧
  (∀ j : {j : SourceRemainingCoordinate D //
      j ∈ exactRight seed.coordinate seed.partition},
      ys j.val.val = history.bobRight j) ∧
  (∀ j : {j : SourceRemainingCoordinate D //
      j ∈ exactLeftPrefix seed},
      ys j.val.val = history.bobLeftPrefix j) ∧
  ys seed.coordinate.val = y

/-- The probability weight for exact fiber question. -/
def exactFiberQuestionWeight
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) (y : Y)
    (xs : Fin n → X) (ys : Fin n → Y) : ℝ :=
  if exactAliceQuestionCompatible
      D seed history x xs ∧
      exactBobQuestionCompatible
        D seed history y ys
  then (G.repeat n).questionWeight xs ys
  else 0

/-- The question-fiber weight summed over Bob's full question vector. -/
def exactFiberAliceMarginal
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) (y : Y) (xs : Fin n → X) : ℝ :=
  ∑ ys : Fin n → Y,
    exactFiberQuestionWeight G n D seed history x y xs ys

/-- The question-fiber weight summed over Alice's full question vector. -/
def exactFiberBobMarginal
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) (y : Y) (ys : Fin n → Y) : ℝ :=
  ∑ xs : Fin n → X,
    exactFiberQuestionWeight G n D seed history x y xs ys

/-- The total probability mass of exact fiber question. -/
def exactFiberQuestionMass
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) (y : Y) : ℝ :=
  ∑ xs : Fin n → X, ∑ ys : Fin n → Y,
    exactFiberQuestionWeight G n D seed history x y xs ys

end

section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/--
@isnad1 id=eq.0h3v.s4.18e345864b79 from=translated src=- shape=3e810e78 vocab=5790e008
-/
theorem exactFintypeCard_eq
    {T : Type*} (first second : Fintype T) :
    @Fintype.card T first = @Fintype.card T second :=
  @Fintype.card_congr T T first second (Equiv.refl T)

/--
@isnad1 id=eq.1h1v.s5.7f3f96d40c6b from=translated src=- shape=d9c45cdd vocab=abafccc4
-/
theorem exactSeedWeight_sum
    {M : Type*} [Fintype M] [DecidableEq M]
    (nonempty : 0 < Fintype.card M) :
    (∑ seed : ExactForwardSeed M,
      exactSeedWeight seed) = 1 := by
  classical
  have hbits : 0 < Fintype.card (M → Bool) :=
    Fintype.card_pos_iff.mpr ⟨fun _ => false⟩
  rw [exactForwardSeed_sum]
  conv_rhs => rw [← exactUniform_sum nonempty]
  apply Finset.sum_congr (by ext; simp only [mem_univ])
  intro coordinate _
  conv_rhs =>
    rw [← exactUniform_sum_mul hbits
      (1 / (Fintype.card M : ℝ))]
  apply Finset.sum_congr (by ext; simp only [mem_univ])
  intro partition _
  let : DecidableEq
      {j : M // j ∈ exactLeft coordinate partition} :=
    fun a b => Classical.propDecidable (a = b)
  let : DecidableEq
      {j : M // j ∈ exactRight coordinate partition} :=
    fun a b => Classical.propDecidable (a = b)
  conv_rhs =>
    rw [← exactPermutationUniform_sum_mul
      (T := {j : M // j ∈ exactLeft coordinate partition})
      ((1 / (Fintype.card M : ℝ)) *
        (1 / (Fintype.card (M → Bool) : ℝ)))]
  apply Finset.sum_congr (by ext; simp only [mem_univ])
  intro leftOrder _
  conv_rhs =>
    rw [← exactPermutationUniform_sum_mul
      (T := {j : M // j ∈ exactRight coordinate partition})
      ((1 / (Fintype.card M : ℝ)) *
        (1 / (Fintype.card (M → Bool) : ℝ)) *
        (1 / (Fintype.card
          (Equiv.Perm
            {j : M // j ∈ exactLeft coordinate partition}) : ℝ)))]
  apply Finset.sum_congr (by ext; simp only [mem_univ])
  intro rightOrder _
  conv_rhs =>
    rw [← exactPrefixUniform_sum_mul
      (exactLeft coordinate partition).card
      ((1 / (Fintype.card M : ℝ)) *
        (1 / (Fintype.card (M → Bool) : ℝ)) *
        (1 / (Fintype.card
          (Equiv.Perm
            {j : M // j ∈ exactLeft coordinate partition}) : ℝ)) *
        (1 / (Fintype.card
          (Equiv.Perm
            {j : M // j ∈ exactRight coordinate partition}) : ℝ)))]
  apply Finset.sum_congr (by ext; simp only [mem_univ])
  intro leftCut _
  conv_rhs =>
    rw [← exactPrefixUniform_sum_mul
      (exactRight coordinate partition).card
      ((1 / (Fintype.card M : ℝ)) *
        (1 / (Fintype.card (M → Bool) : ℝ)) *
        (1 / (Fintype.card
          (Equiv.Perm
            {j : M // j ∈ exactLeft coordinate partition}) : ℝ)) *
        (1 / (Fintype.card
          (Equiv.Perm
            {j : M // j ∈ exactRight coordinate partition}) : ℝ)) *
        (1 / ((exactLeft coordinate partition).card + 1 : ℝ)))]
  apply Finset.sum_congr (by ext; simp only [mem_univ])
  intro rightCut _
  simp only [exactSeedWeight]
  refine congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·)
    (congrArg₂ (· * ·) rfl ?_) ?_) rfl) rfl
  · exact congrArg (fun k : ℕ => 1 / (k : ℝ)) (exactFintypeCard_eq _ _)
  · exact congrArg (fun k : ℕ => 1 / (k : ℝ)) (exactFintypeCard_eq _ _)

end

section

open scoped BigOperators

/-- The numerical bound for has exponential. -/
def HasExponentialBound (v : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, v n ≤ C * Real.exp (-c * (n : ℝ))

/-- The has subexponential witness construction used in the quantum parallel-repetition argument. -/
def HasSubexponentialWitness (v : ℕ → ℝ) : Prop :=
  ∀ c : ℝ, 0 < c → ∀ C : ℝ, 0 < C →
    ∃ n : ℕ, C * Real.exp (-c * (n : ℝ)) < v n

end

section

open scoped BigOperators

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The standard exponential-decay statement for quantum parallel repetition. -/
def StandardQuantumParallelRepetition (G : Game X Y A B) : Prop :=
  entangledValue G < 1 →
    HasExponentialBound (repeatedEntangledValue G)

end

section

open scoped BigOperators

open QuantumParallelRepetition.Pinsker

end

section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

section ActualSharedFlag

variable {X Y A B dA dB J : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [Fintype dA] [Fintype dB] [DecidableEq dA] [DecidableEq dB]
variable [Fintype J] [DecidableEq J]

/-- The measurement effect for pure verifier. -/
def pureVerifierEffect
    (G : Game X Y A B)
    (z : EuclideanSpace ℂ (dA × dB)) (hz : ‖z‖ = 1)
    (PA : X → POVM A dA) (PB : Y → POVM B dB)
    (x : X) (y : Y) : Matrix (dA × dB) (dA × dB) ℂ :=
  (pureVectorStrategy G z hz PA PB).winningEffect x y

/-- The probability weight for flagged question. -/
def flaggedQuestionWeight
    (G : Game X Y A B) (flagWeight : J → ℝ)
    (ω : J × (X × Y)) : ℝ :=
  flagWeight ω.1 * G.questionWeight ω.2.1 ω.2.2

end ActualSharedFlag

end

section

open Filter
open scoped Topology

/-- A universal upper bound for the accumulated rounding error. -/
def universalErrorCeiling (K₀ : ℝ) : ℝ :=
  K₀ * (1 + (2 : ℝ) ^ (1 / 6 : ℝ)) + 2

/-- The combined information-theoretic loss from the sampling steps. -/
def totalSamplingLoss (K₀ α η lam : ℝ) : ℝ :=
  5 * lam +
    2 * (K₀ * (α ^ (1 / 12 : ℝ) +
        (32 * η) ^ (1 / 12 : ℝ)) +
      Real.sqrt (8 * η) + universalErrorCeiling K₀ * lam)

/-- The numerical bound for rounded winning lower. -/
def roundedWinningLowerBound (ε K₀ α η lam : ℝ) : ℝ :=
  1 - ε / 2 - totalSamplingLoss K₀ α η lam

end

section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

end

section

open scoped BigOperators

end

section

open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

/--
@isnad1 id=eq.0h4v.s5.176d543b817d from=translated src=- shape=73148b7e vocab=6aa65041
-/
theorem fullHistoryRemaining_insert_conditioned
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n) :
    fullHistoryRemaining n (insert i D) L =
      fullHistoryRemaining n D (insert i L) := by
  ext j
  simp only [fullHistoryRemaining, Finset.mem_sdiff,
    Finset.mem_univ, true_and, Finset.mem_insert]
  tauto

private def fullHistoryRemainingInsertedEquiv
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n) :
    {j : Fin n // j ∈ fullHistoryRemaining n (insert i D) L} ≃
      {j : Fin n // j ∈ fullHistoryRemaining n D (insert i L)} :=
  Equiv.subtypeEquivRight fun j => by
    rw [fullHistoryRemaining_insert_conditioned D L i]

private def fullCoordinateAnswerExtension
    {T : Type*} {n : ℕ}
    (D : Finset (Fin n)) (i : Fin n)
    (α : {j : Fin n // j ∈ D} → T) (a : T) :
    {j : Fin n // j ∈ insert i D} → T := by
  classical
  intro j
  by_cases hj : (j : Fin n) = i
  · exact a
  · exact α ⟨j, (Finset.mem_insert.mp j.property).resolve_left hj⟩

private def fullCoordinateAnswerExtensionEquiv
    {T : Type*} {n : ℕ}
    (D : Finset (Fin n)) (i : Fin n) (hiD : i ∉ D) :
    (({j : Fin n // j ∈ D} → T) × T) ≃
      ({j : Fin n // j ∈ insert i D} → T) where
  toFun t := fullCoordinateAnswerExtension D i t.1 t.2
  invFun α :=
    (fun j => α ⟨j, Finset.mem_insert_of_mem j.property⟩,
      α ⟨i, Finset.mem_insert_self i D⟩)
  left_inv t := by
    rcases t with ⟨α, a⟩
    apply Prod.ext
    · funext j
      have hj : (j : Fin n) ≠ i := by
        intro he
        exact hiD (he ▸ j.property)
      simp only [fullCoordinateAnswerExtension, hj, ↓reduceDIte, Subtype.coe_eta]
    · simp only [fullCoordinateAnswerExtension, ↓reduceDIte]
  right_inv α := by
    funext j
    by_cases hj : (j : Fin n) = i
    · have hjsub :
          j = (⟨i, Finset.mem_insert_self i D⟩ :
            {j : Fin n // j ∈ insert i D}) := Subtype.ext hj
      subst j
      simp only [fullCoordinateAnswerExtension, ↓reduceDIte]
    · simp only [fullCoordinateAnswerExtension, hj, ↓reduceDIte, Subtype.coe_eta]

private def fullCoordinateInsertedHistory
    {X Y : Type*}
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (x : X) (y : Y) :
    FullSubsetHistory X Y n (insert i D) L := by
  classical
  refine ⟨
    fullCoordinateAnswerExtension D i r.aliceConditioned x,
    fullCoordinateAnswerExtension D i r.bobConditioned y,
    r.aliceRevealed,
    fun j => r.bobRemaining ⟨j, ?_⟩⟩
  rw [← fullHistoryRemaining_insert_conditioned D L i]
  exact j.property

private def fullCoordinateBaseOfInsertedHistory
    {X Y : Type*}
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n)
    (h : FullSubsetHistory X Y n (insert i D) L) :
    FullCoordinateRevealHistory X Y n D L i := by
  refine ⟨
    fun j => h.aliceConditioned
      ⟨j, Finset.mem_insert_of_mem j.property⟩,
    fun j => h.bobConditioned
      ⟨j, Finset.mem_insert_of_mem j.property⟩,
    h.aliceRevealed,
    fun j => h.bobRemaining ⟨j, ?_⟩⟩
  rw [fullHistoryRemaining_insert_conditioned D L i]
  exact j.property

private def fullCoordinateInsertedHistoryEquiv
    {X Y : Type*}
    {n : ℕ} (D L : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D) :
    (FullCoordinateRevealHistory X Y n D L i × X × Y) ≃
      FullSubsetHistory X Y n (insert i D) L where
  toFun t := fullCoordinateInsertedHistory D L i t.1 t.2.1 t.2.2
  invFun h :=
    (fullCoordinateBaseOfInsertedHistory D L i h,
      h.aliceConditioned ⟨i, Finset.mem_insert_self i D⟩,
      h.bobConditioned ⟨i, Finset.mem_insert_self i D⟩)
  left_inv t := by
    rcases t with ⟨r, x, y⟩
    apply Prod.ext
    · apply FullCoordinateRevealHistory.ext
      · funext j
        have hj : (j : Fin n) ≠ i := by
          intro he
          exact hiD (he ▸ j.property)
        simp only [fullCoordinateBaseOfInsertedHistory, fullCoordinateInsertedHistory,
          fullCoordinateAnswerExtension, Subtype.coe_eta, dite_eq_ite, hj, ↓reduceIte]
      · funext j
        have hj : (j : Fin n) ≠ i := by
          intro he
          exact hiD (he ▸ j.property)
        simp only [fullCoordinateBaseOfInsertedHistory, fullCoordinateInsertedHistory,
          fullCoordinateAnswerExtension, Subtype.coe_eta, dite_eq_ite, hj, ↓reduceIte]
      · rfl
      · rfl
    · apply Prod.ext <;>
        simp only [fullCoordinateInsertedHistory, fullCoordinateAnswerExtension, ↓reduceDIte]
  right_inv h := by
    apply FullSubsetHistory.ext
    · funext j
      by_cases hj : (j : Fin n) = i
      · have hjsub :
            j = (⟨i, Finset.mem_insert_self i D⟩ :
              {j : Fin n // j ∈ insert i D}) := Subtype.ext hj
        subst j
        simp only [fullCoordinateInsertedHistory, fullCoordinateBaseOfInsertedHistory,
          Subtype.coe_eta, fullCoordinateAnswerExtension, ↓reduceDIte]
      · simp only [fullCoordinateInsertedHistory, fullCoordinateBaseOfInsertedHistory,
          Subtype.coe_eta, fullCoordinateAnswerExtension, hj, ↓reduceDIte]
    · funext j
      by_cases hj : (j : Fin n) = i
      · have hjsub :
            j = (⟨i, Finset.mem_insert_self i D⟩ :
              {j : Fin n // j ∈ insert i D}) := Subtype.ext hj
        subst j
        simp only [fullCoordinateInsertedHistory, fullCoordinateBaseOfInsertedHistory,
          Subtype.coe_eta, fullCoordinateAnswerExtension, ↓reduceDIte]
      · simp only [fullCoordinateInsertedHistory, fullCoordinateBaseOfInsertedHistory,
          Subtype.coe_eta, fullCoordinateAnswerExtension, hj, ↓reduceDIte]
    · rfl
    · rfl

section InsertedWeights

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

end InsertedWeights

end

section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

end

section

open scoped BigOperators ComplexConjugate ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

/-- The state vector representing normalized pure. -/
def normalizedPureVector
    {d : Type*} [Fintype d]
    (z : EuclideanSpace ℂ d) : EuclideanSpace ℂ d :=
  ((‖z‖⁻¹ : ℝ) : ℂ) • z

end

section

open scoped BigOperators

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

end

section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- A remaining permutation, its reveal position and history, and the selected answers. -/
structure SourceHistoryFlag
    (X Y A B : Type*)
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {n : ℕ} (D : Finset (Fin n)) where
  /-- The order in which the remaining coordinates are revealed. -/
  permutation : SourceRemainingPermutation D
  /-- The rank of the coordinate currently being revealed. -/
  position : Fin (Finset.univ \ D).card
  /-- The revealed history for the chosen permutation prefix and coordinate. -/
  history : FullCoordinateRevealHistory X Y n D
    (sourceRemainingPermutationPrefix D permutation position.castSucc)
    (sourceRemainingPermutationCoordinate D permutation position)
  /-- Alice's answers on the already selected coordinates. -/
  aliceAnswer : {i : Fin n // i ∈ D} → A
  /-- Bob's answers on the already selected coordinates. -/
  bobAnswer : {i : Fin n // i ∈ D} → B

/-- A nested tuple representation of a source history flag. -/
abbrev SourceHistoryFlagTuple
    (X Y A B : Type*)
    {n : ℕ} (D : Finset (Fin n)) :=
  Σ π : SourceRemainingPermutation D,
    Σ k : Fin (Finset.univ \ D).card,
      FullCoordinateRevealHistory X Y n D
        (sourceRemainingPermutationPrefix D π k.castSucc)
        (sourceRemainingPermutationCoordinate D π k) ×
      ({i : Fin n // i ∈ D} → A) ×
      ({i : Fin n // i ∈ D} → B)

/-- Convert between a bundled source history flag and its nested tuple representation. -/
def sourceHistoryFlagEquiv
    {n : ℕ} (D : Finset (Fin n)) :
    SourceHistoryFlag X Y A B D ≃ SourceHistoryFlagTuple X Y A B D where
  toFun r := ⟨r.permutation, r.position,
    r.history, r.aliceAnswer, r.bobAnswer⟩
  invFun t := ⟨t.1, t.2.1,
    t.2.2.1, t.2.2.2.1, t.2.2.2.2⟩
  left_inv r := by cases r; rfl
  right_inv t := by
    rcases t with ⟨π, k, r, α, β⟩
    rfl

noncomputable instance sourceHistoryFlagFintype
    {n : ℕ} (D : Finset (Fin n)) :
    Fintype (SourceHistoryFlag X Y A B D) := by
  classical
  exact Fintype.ofEquiv (SourceHistoryFlagTuple X Y A B D)
    (sourceHistoryFlagEquiv (X := X) (Y := Y)
      (A := A) (B := B) D).symm

/-- The uniform weight of a remaining permutation and position pair. -/
def sourceHistoryPermutationPositionWeight
    {n : ℕ} (D : Finset (Fin n)) : ℝ :=
  1 / ((Fintype.card (SourceRemainingPermutation D) : ℝ) *
    ((Finset.univ \ D).card : ℝ))

/-- The unnormalized weight of a source history flag, including the selected wins. -/
def sourceHistoryRaw
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (r : SourceHistoryFlag X Y A B D) : ℝ :=
  sourceHistoryPermutationPositionWeight D *
    fullCoordinateBaseWeight G D
      (sourceRemainingPermutationPrefix D
        r.permutation r.position.castSucc)
      (sourceRemainingPermutationCoordinate D
        r.permutation r.position)
      r.history *
    fullCoordinateBaseWinIndicator G D
      (sourceRemainingPermutationPrefix D
        r.permutation r.position.castSucc)
      (sourceRemainingPermutationCoordinate D
        r.permutation r.position)
      r.history r.aliceAnswer r.bobAnswer

end

section

open scoped BigOperators

section FiniteSamples

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]

/-- The total probability mass of postselection. -/
def postselectionMass
    (law : FiniteEventLaw Ω) (wins : ι → Ω → Bool)
    (C : Finset ι) : ℝ :=
  law.eventMass (FiniteEventLaw.winEvent wins C)

/--
The conditional coordinate failure construction used in the quantum parallel-repetition
argument.
-/
def conditionalCoordinateFailure
    (law : FiniteEventLaw Ω) (wins : ι → Ω → Bool)
    (C : Finset ι) (i : ι) : ℝ :=
  FiniteEventLaw.failureMass law wins C i /
    postselectionMass law wins C

/-- The uniform remaining failure construction used in the quantum parallel-repetition argument. -/
def uniformRemainingFailure
    (law : FiniteEventLaw Ω) (wins : ι → Ω → Bool)
    (C : Finset ι) : ℝ :=
  (∑ i ∈ Finset.univ \ C,
    conditionalCoordinateFailure law wins C i) /
    ((Finset.univ \ C).card : ℝ)

end FiniteSamples

section ActualRepeatedStrategy

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The total probability mass of repeated postselection. -/
def repeatedPostselectionMass
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n)) (C : Finset (Fin n)) : ℝ :=
  postselectionMass (strategyEventLaw (G.repeat n) S)
    (repeatedCoordinateWin G n) C

end ActualRepeatedStrategy

end

section

open scoped BigOperators ComplexOrder MatrixOrder

end

section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

section ActualFilters

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The postselection log cost construction used in the quantum parallel-repetition argument. -/
def postselectionLogCost
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) : ℝ :=
  Real.log (1 / repeatedPostselectionMass G n S D)

/-- The answer log cost construction used in the quantum parallel-repetition argument. -/
def answerLogCost
    {A B : Type*} [Fintype A] [Fintype B]
    {n : ℕ} (D : Finset (Fin n)) : ℝ :=
  (D.card : ℝ) *
    Real.log ((Fintype.card A : ℝ) * (Fintype.card B : ℝ))

/-- The error rate associated with martingale. -/
def martingaleRate
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) : ℝ :=
  (postselectionLogCost G n S D +
      answerLogCost (A := A) (B := B) D) /
    ((Finset.univ \ D).card : ℝ)

end ActualFilters

section ActualPurificationHistories

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

end ActualPurificationHistories

end

section

open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

private def fullCoordinateInsertedHiddenAliceEquiv
    {X : Type*} {n : ℕ}
    (D L : Finset (Fin n)) (i : Fin n) :
    ({j : Fin n // j ∈ fullHistoryRemaining n (insert i D) L} → X) ≃
      ({j : Fin n // j ∈ fullHistoryRemaining n D (insert i L)} → X) where
  toFun hidden j :=
    hidden ((fullHistoryRemainingInsertedEquiv D L i).symm j)
  invFun hidden j := hidden (fullHistoryRemainingInsertedEquiv D L i j)
  left_inv hidden := by
    funext j
    simp only [Equiv.symm_apply_apply]
  right_inv hidden := by
    funext j
    simp only [Equiv.apply_symm_apply]

private def fullCoordinateAcceptedPostselectedMass
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D L : Finset (Fin n)) (i : Fin n) : ℝ :=
  ∑ r : FullCoordinateRevealHistory X Y n D L i,
  ∑ α : {j : Fin n // j ∈ D} → A,
  ∑ β : {j : Fin n // j ∈ D} → B,
    fullCoordinateBaseWeight G D L i r *
      fullCoordinateBaseWinIndicator G D L i r α β *
      (∑ x : X, ∑ y : Y, G.questionWeight x y *
        (∑ a : A, ∑ b : B,
          (if G.predicate x y a b = true then 1 else 0) *
            bornTracePairing S.state.matrix
              (fullCoordinateAliceRefinementEffect
                G n S D L i r α x a)
              (fullCoordinateBobRefinementEffect
                G n S D L i r β y b)))

end

section

open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The Born mass of winning answers for the flag's selected question pair. -/
def sourceHistoryAcceptedQuestionMass
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n)) (D : Finset (Fin n))
    (r : SourceHistoryFlag X Y A B D)
    (x : X) (y : Y) : ℝ :=
  ∑ a : A, ∑ b : B,
    (if G.predicate x y a b = true then 1 else 0) *
      bornTracePairing S.state.matrix
        (fullCoordinateAliceRefinementEffect G n S D
          (sourceRemainingPermutationPrefix D
            r.permutation r.position.castSucc)
          (sourceRemainingPermutationCoordinate D
            r.permutation r.position)
          r.history r.aliceAnswer x a)
        (fullCoordinateBobRefinementEffect G n S D
          (sourceRemainingPermutationPrefix D
            r.permutation r.position.castSucc)
          (sourceRemainingPermutationCoordinate D
            r.permutation r.position)
          r.history r.bobAnswer y b)

/-- The total probability mass of source history accepted. -/
def sourceHistoryAcceptedMass
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n)) (D : Finset (Fin n)) : ℝ :=
  ∑ r : SourceHistoryFlag X Y A B D,
    sourceHistoryRaw G n D r *
      (∑ x : X, ∑ y : Y, G.questionWeight x y *
        sourceHistoryAcceptedQuestionMass G n S D r x y)

end

section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

end

section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

section TaggedTensorBlocks

variable {R : Type*} [Fintype R]
variable {ι : R → Type*} [∀ r, Fintype (ι r)]

/-- The state vector representing tagged tensor. -/
def taggedTensorVector
    (r : R) (z : EuclideanSpace ℂ (ι r × ι r)) :
    EuclideanSpace ℂ
      ((PUnit.{1} ⊕ (Σ r : R, ι r)) ×
        (PUnit.{1} ⊕ (Σ r : R, ι r))) := by
  classical
  exact toLp 2 fun q =>
    match q.1, q.2 with
    | .inr ⟨rA, a⟩, .inr ⟨rB, b⟩ =>
        if hA : rA = r then
          if hB : rB = r then
            z (hA ▸ a, hB ▸ b)
          else 0
        else 0
    | _, _ => 0

/--
@isnad1 id=eq.0h4v.s7.11b751c020fd from=translated src=- shape=ed7788b0 vocab=c6dad396
-/
theorem taggedTensorVector_norm
    (r : R) (z : EuclideanSpace ℂ (ι r × ι r)) :
    ‖taggedTensorVector r z‖ = ‖z‖ := by
  classical
  have hsquare :
      ‖taggedTensorVector r z‖ ^ 2 = ‖z‖ ^ 2 := by
    simp only [taggedTensorVector, EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type,
      Fintype.sum_sum_type, univ_unique, PUnit.default_eq_unit, norm_zero, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sum_const_zero, Fintype.sum_sigma,
      zero_add]
    calc
      _ = ∑ a : ι r, ∑ rB : R, ∑ b : ι rB,
          ‖if hA : (r : R) = r then
              if hB : rB = r then z (hA ▸ a, hB ▸ b) else 0
            else 0‖ ^ 2 := by
        apply Fintype.sum_eq_single r
        intro rA hA
        simp only [hA, ↓reduceDIte, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          zero_pow, sum_const_zero]
      _ = ∑ a : ι r, ∑ rB : R, ∑ b : ι rB,
          ‖if hB : rB = r then z (a, hB ▸ b) else 0‖ ^ 2 := by
        simp only [↓reduceDIte]
      _ = ∑ a : ι r, ∑ b : ι r,
          ‖if hB : (r : R) = r then z (a, hB ▸ b) else 0‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro a _
        apply Fintype.sum_eq_single r
        intro rB hB
        simp only [hB, ↓reduceDIte, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          zero_pow, sum_const_zero]
      _ = _ := by simp only [↓reduceDIte]
  nlinarith [norm_nonneg (taggedTensorVector r z),
    norm_nonneg z]

end TaggedTensorBlocks

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

end

section

open scoped BigOperators

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
open QuantumParallelRepetition.ClassicalSampling

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/--
@isnad1 id=lt.1h2v.s5.3d3295b9d8ea from=translated src=- shape=1d955806 vocab=b469cfe1
-/
theorem remainingCoordinate_card_pos
    {n : ℕ} (D : Finset (Fin n))
    (hm : 0 < (Finset.univ \ D).card) :
    0 < Fintype.card (SourceRemainingCoordinate D) := by
  simpa only [Fintype.card_coe, card_pos] using hm

/-- The weighted conditional joint construction used in the quantum parallel-repetition argument. -/
def weightedConditionalJoint
    {κ ι : Type*}
    (weight : κ → ℝ) (conditional : κ → ι → ℝ) :
    κ × ι → ℝ :=
  fun t => weight t.1 * conditional t.1 t.2

/-- The type used to represent local question context in the exact sampling construction. -/
abbrev LocalQuestionContext
    (X Y : Type*)
    {n : ℕ} (D : Finset (Fin n)) :=
  SourceRemainingCoordinate D × (X × Y)

/-- The probability weight for local question. -/
def localQuestionWeight
    (G : Game X Y A B) (n : ℕ) (D : Finset (Fin n))
    (c : LocalQuestionContext X Y D) : ℝ :=
  G.questionWeight c.2.1 c.2.2 /
    (Fintype.card (SourceRemainingCoordinate D) : ℝ)

/-- The probability distribution for conditioned event. -/
def conditionedEventDistribution
    {Ω : Type*} [Fintype Ω]
    (law : FiniteEventLaw Ω) (event : Finset Ω) : Ω → ℝ :=
  fun ω => if ω ∈ event then law.weight ω / law.eventMass event else 0

/-- The finite probability law for repeated conditioned outcome. -/
def repeatedConditionedOutcomeLaw
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) :
    StrategyOutcome
      (Fin n → X) (Fin n → Y)
      (Fin n → A) (Fin n → B) → ℝ :=
  conditionedEventDistribution
    (strategyEventLaw (G.repeat n) S)
    (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D)

end

section

open scoped BigOperators

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

/-- The probability weight for finite uniform. -/
def finiteUniformWeight (Z : Type*) [Fintype Z] : ℝ :=
  1 / (Fintype.card Z : ℝ)

/-- The uniform flag reference construction used in the quantum parallel-repetition argument. -/
def uniformFlagReference
    {Ω Z : Type*} [Fintype Z]
    (prior : Ω → ℝ) : Ω × Z → ℝ :=
  fun t => prior t.1 * finiteUniformWeight Z

/-- The finite prefix mask construction used in the quantum parallel-repetition argument. -/
def finitePrefixMask
    {Ω Y : Type*} {h : ℕ} (base : Y)
    (k : Fin (h + 1)) :
    (Ω × (Fin h → Y)) → (Ω × (Fin h → Y)) :=
  fun t => (t.1, fun j => if j.val < k.val then t.2 j else base)

/-- The entropy quantity for finite prefix relative. -/
def finitePrefixRelativeEntropy
    {Ω Y : Type*} [Fintype Ω] [Fintype Y] {h : ℕ}
    (joint prior : Ω × (Fin h → Y) → ℝ)
    (base : Y) (k : Fin (h + 1)) : ℝ :=
  finiteRelativeEntropy
    (groupedMass (finitePrefixMask base k) joint)
    (groupedMass (finitePrefixMask base k) prior)

end

section

open scoped BigOperators

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The type used to represent conditioned answer flag in the exact sampling construction. -/
abbrev ConditionedAnswerFlag
    (A B : Type*)
    {n : ℕ} (D : Finset (Fin n)) :=
  ({i : Fin n // i ∈ D} → A) ×
    ({i : Fin n // i ∈ D} → B)

/--
The repeated conditioned answer flag construction used in the quantum parallel-repetition
argument.
-/
def repeatedConditionedAnswerFlag
    (G : Game X Y A B) (n : ℕ) (_S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (ω : StrategyOutcome
      (Fin n → X) (Fin n → Y)
      (Fin n → A) (Fin n → B)) :
    ConditionedAnswerFlag A B D :=
  (fun i => ω.2.2.1 i, fun i => ω.2.2.2 i)

end

section

open scoped BigOperators

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The type used to represent exact outcome in the exact sampling construction. -/
abbrev ExactOutcome (X Y A B : Type*) (n : ℕ) :=
  StrategyOutcome (Fin n → X) (Fin n → Y)
    (Fin n → A) (Fin n → B)

/-- The type used to represent exact joint outcome in the exact sampling construction. -/
abbrev ExactJointOutcome
    (X Y A B : Type*) {n : ℕ} (D : Finset (Fin n)) :=
  ExactRemainingSeed D × ExactOutcome X Y A B n

/-- The finite probability law for exact postselected joint. -/
def exactPostselectedJointLaw
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (q : ExactJointOutcome X Y A B D) : ℝ :=
  exactSeedWeight q.1 *
    repeatedConditionedOutcomeLaw G n S D q.2

/-- The exact source pushforward construction used in the quantum parallel-repetition argument. -/
def exactSourcePushforward
    {K : Type*}
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (projection : ExactJointOutcome X Y A B D → K) :
    K → ℝ :=
  groupedMass projection (exactPostselectedJointLaw G n S D)

end

section

open scoped BigOperators

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
open QuantumParallelRepetition.ClassicalSampling

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The type used to represent exact locally sampleable tuple in the exact sampling construction. -/
abbrev ExactLocallySampleableTuple
    (X Y A B : Type*)
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {n : ℕ} (D : Finset (Fin n)) :=
  SourceRemainingCoordinate D ×
    (X × (Y × ExactHistoryFlag X Y A B D))

/-- The finite encoding of exact history. -/
def exactHistoryCode
    {n : ℕ} (D : Finset (Fin n))
    (q : ExactJointOutcome X Y A B D) :
    ExactHistoryFlag X Y A B D where
  seed := q.1
  history := exactRevealCode D q.1 (q.2.1, q.2.2.1)
  aliceAnswer := fun j => q.2.2.2.1 j.val
  bobAnswer := fun j => q.2.2.2.2 j.val

/-- The finite encoding of exact locally sampleable. -/
def exactLocallySampleableCode
    {n : ℕ} (D : Finset (Fin n))
    (q : ExactJointOutcome X Y A B D) :
    ExactLocallySampleableTuple X Y A B D :=
  (q.1.coordinate,
    q.2.1 q.1.coordinate.val,
    q.2.2.1 q.1.coordinate.val,
    exactHistoryCode D q)

/-- The finite probability law for exact locally sampleable. -/
def exactLocallySampleableLaw
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) :
    ExactLocallySampleableTuple X Y A B D → ℝ :=
  exactSourcePushforward G n S D
    (exactLocallySampleableCode D)

/-- The total probability mass of exact alice local. -/
def exactAliceLocalMass
    {n : ℕ} (D : Finset (Fin n))
    (Q : ExactLocallySampleableTuple X Y A B D → ℝ)
    (i : SourceRemainingCoordinate D) (x : X) : ℝ :=
  ∑ r : ExactHistoryFlag X Y A B D,
    ∑ y : Y, Q (i, x, y, r)

/-- The total probability mass of exact bob local. -/
def exactBobLocalMass
    {n : ℕ} (D : Finset (Fin n))
    (Q : ExactLocallySampleableTuple X Y A B D → ℝ)
    (i : SourceRemainingCoordinate D) (y : Y) : ℝ :=
  ∑ r : ExactHistoryFlag X Y A B D,
    ∑ x : X, Q (i, x, y, r)

/--
The exact alice local conditional construction used in the quantum parallel-repetition argument.
-/
def exactAliceLocalConditional
    {n : ℕ} (D : Finset (Fin n))
    (base : ExactHistoryFlag X Y A B D)
    (Q : ExactLocallySampleableTuple X Y A B D → ℝ)
    (i : SourceRemainingCoordinate D) (x : X)
    (r : ExactHistoryFlag X Y A B D) : ℝ :=
  if exactAliceLocalMass D Q i x = 0 then
    if r = base then 1 else 0
  else
    (∑ y : Y, Q (i, x, y, r)) /
      exactAliceLocalMass D Q i x

/--
The exact bob local conditional construction used in the quantum parallel-repetition argument.
-/
def exactBobLocalConditional
    {n : ℕ} (D : Finset (Fin n))
    (base : ExactHistoryFlag X Y A B D)
    (Q : ExactLocallySampleableTuple X Y A B D → ℝ)
    (i : SourceRemainingCoordinate D) (y : Y)
    (r : ExactHistoryFlag X Y A B D) : ℝ :=
  if exactBobLocalMass D Q i y = 0 then
    if r = base then 1 else 0
  else
    (∑ x : X, Q (i, x, y, r)) /
      exactBobLocalMass D Q i y

/--
The exact locally sampleable ja construction used in the quantum parallel-repetition argument.
-/
def exactLocallySampleableJA
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (base : ExactHistoryFlag X Y A B D)
    (t : ExactLocallySampleableTuple X Y A B D) : ℝ :=
  G.questionWeight t.2.1 t.2.2.1 *
    exactAliceLocalConditional D base
      (exactLocallySampleableLaw G n S D)
      t.1 t.2.1 t.2.2.2 /
    (Fintype.card (SourceRemainingCoordinate D) : ℝ)

/--
The exact locally sampleable jb construction used in the quantum parallel-repetition argument.
-/
def exactLocallySampleableJB
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (base : ExactHistoryFlag X Y A B D)
    (t : ExactLocallySampleableTuple X Y A B D) : ℝ :=
  G.questionWeight t.2.1 t.2.2.1 *
    exactBobLocalConditional D base
      (exactLocallySampleableLaw G n S D)
      t.1 t.2.2.1 t.2.2.2 /
    (Fintype.card (SourceRemainingCoordinate D) : ℝ)

/-- The type used to represent exact local sampler index in the exact sampling construction. -/
abbrev ExactLocalSamplerIndex
    (X Y : Type*)
    {n : ℕ} (D : Finset (Fin n)) :=
  (SourceRemainingCoordinate D × X) ⊕
    (SourceRemainingCoordinate D × Y)

/--
The exact local conditional family construction used in the quantum parallel-repetition
argument.
-/
def exactLocalConditionalFamily
    {n : ℕ} (D : Finset (Fin n))
    (base : ExactHistoryFlag X Y A B D)
    (Q : ExactLocallySampleableTuple X Y A B D → ℝ)
    (k : ExactLocalSamplerIndex X Y D)
    (r : ExactHistoryFlag X Y A B D) : ℝ :=
  match k with
  | .inl (i, x) => exactAliceLocalConditional D base Q i x r
  | .inr (i, y) => exactBobLocalConditional D base Q i y r

end

section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The probability weight for exact conditional question. -/
def exactConditionalQuestionWeight
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) (y : Y)
    (xs : Fin n → X) (ys : Fin n → Y) : ℝ :=
  exactFiberQuestionWeight
      G n D seed history x y xs ys /
    exactFiberQuestionMass G n D seed history x y

private def exactJointAliceQuestionFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → A)
    (x : X) (y : Y) : Matrix S.Alice S.Alice ℂ :=
  ∑ xs : Fin n → X,
    (exactFiberAliceMarginal
      G n D seed history x y xs /
      exactFiberQuestionMass G n D seed history x y) •
    conditionedAliceEffect G n S D answer xs

private def exactJointBobQuestionFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → B)
    (x : X) (y : Y) : Matrix S.Bob S.Bob ℂ :=
  ∑ ys : Fin n → Y,
    (exactFiberBobMarginal
      G n D seed history x y ys /
      exactFiberQuestionMass G n D seed history x y) •
    conditionedBobEffect G n S D answer ys

/-- The spectral filter for exact joint alice coordinate. -/
def exactJointAliceCoordinateFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → A)
    (x : X) (y : Y) (a : A) : Matrix S.Alice S.Alice ℂ :=
  ∑ xs : Fin n → X,
    (exactFiberAliceMarginal
      G n D seed history x y xs /
      exactFiberQuestionMass G n D seed history x y) •
    conditionedAliceCoordinateEffect
      G n S D answer xs seed.coordinate.val a

/-- The spectral filter for exact joint bob coordinate. -/
def exactJointBobCoordinateFilter
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (answer : {j : Fin n // j ∈ D} → B)
    (x : X) (y : Y) (b : B) : Matrix S.Bob S.Bob ℂ :=
  ∑ ys : Fin n → Y,
    (exactFiberBobMarginal
      G n D seed history x y ys /
      exactFiberQuestionMass G n D seed history x y) •
    conditionedBobCoordinateEffect
      G n S D answer ys seed.coordinate.val b

/-- The total probability mass of exact joint conditional winning. -/
def exactJointConditionalWinningMass
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (aliceAnswer : {j : Fin n // j ∈ D} → A)
    (bobAnswer : {j : Fin n // j ∈ D} → B)
    (x : X) (y : Y) : ℝ :=
  ∑ a : A, ∑ b : B,
    if G.predicate x y a b = true then
      bornTracePairing S.state.matrix
        (exactJointAliceCoordinateFilter
          G n S D seed history aliceAnswer x y a)
        (exactJointBobCoordinateFilter
          G n S D seed history bobAnswer x y b)
    else 0

end

section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

end

end QuantumParallelRepetition

end
