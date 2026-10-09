/-
Copyright (c) 2024 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.LinearAlgebra.Matrix.Stochastic

/-!
# Doubly stochastic matrices

## Main definitions

* `doublyStochastic`: a square matrix is doubly stochastic if all entries are nonnegative, and left
  or right multiplication by the vector of all 1s gives the vector of all 1s. Equivalently, all
  row and column sums are equal to 1.

## Main statements

* `convex_doublyStochastic`: The set of doubly stochastic matrices is convex.
* `permMatrix_mem_doublyStochastic`: Any permutation matrix is doubly stochastic.

## Tags

Doubly stochastic, Birkhoff's theorem, Birkhoff-von Neumann theorem
-/

@[expose] public section

open Finset Matrix

variable {R n : Type*} [Fintype n] [DecidableEq n]

section OrderedSemiring
variable [Semiring R] [PartialOrder R] [IsOrderedRing R] {M : Matrix n n R}

/--
A square matrix is doubly stochastic iff all entries are nonnegative, and left or right
multiplication by the vector of all 1s gives the vector of all 1s.
-/
def doublyStochastic (R n : Type*) [Fintype n] [DecidableEq n] [Semiring R] [PartialOrder R]
    [IsOrderedRing R] :
    Submonoid (Matrix n n R) where
  carrier := {M | (∀ i j, 0 ≤ M i j) ∧ M *ᵥ 1 = 1 ∧ 1 ᵥ* M = 1 }
  mul_mem' {M N} hM hN := by
    refine ⟨fun i j => sum_nonneg fun i _ => mul_nonneg (hM.1 _ _) (hN.1 _ _), ?_, ?_⟩
    next => rw [← mulVec_mulVec, hN.2.1, hM.2.1]
    next => rw [← vecMul_vecMul, hM.2.2, hN.2.2]
  one_mem' := by simp [zero_le_one_elem]

/--
@isnad1 id=iff.0h3v.s8.566547500785 from=seed src=0 shape=474eb952 vocab=3cd577e4
-/
lemma mem_doublyStochastic :
    M ∈ doublyStochastic R n ↔ (∀ i j, 0 ≤ M i j) ∧ M *ᵥ 1 = 1 ∧ 1 ᵥ* M = 1 :=
  Iff.rfl

/--
@isnad1 id=iff.0h3v.s7.71d856ff7542 from=seed src=0 shape=5b030e40 vocab=0bb40d92
-/
lemma mem_doublyStochastic_iff_sum :
    M ∈ doublyStochastic R n ↔
      (∀ i j, 0 ≤ M i j) ∧ (∀ i, ∑ j, M i j = 1) ∧ ∀ j, ∑ i, M i j = 1 := by
  simp [funext_iff, doublyStochastic, mulVec, vecMul, dotProduct]

/-- A matrix is doubly stochastic if and only if it is both row and
column stochastic.
@isnad1 id=eq.0h2v.s6.7b734465ec2f from=seed src=0 shape=c1c7037e vocab=27e7497e
-/
@[local grind =]
lemma doublyStochastic_eq_rowStochastic_inf_colStochastic :
    doublyStochastic R n = rowStochastic R n ⊓ colStochastic R n := by
  ext M
  simp only [rowStochastic, colStochastic, Submonoid.mem_inf, Submonoid.mem_mk, Subsemigroup.mem_mk,
    Set.mem_ofPred_eq, doublyStochastic]
  grind

/--
@isnad1 id=iff.0h3v.s8.ddf597bacb78 from=seed src=0 shape=c6e75a04 vocab=d39f9d85
-/
lemma mem_doublyStochastic_iff_mem_rowStochastic_and_mem_colStochastic {M : Matrix n n R} :
    M ∈ doublyStochastic R n ↔ M ∈ rowStochastic R n ∧ M ∈ colStochastic R n := by
  rw [doublyStochastic_eq_rowStochastic_inf_colStochastic, Submonoid.mem_inf]

/-- Every entry of a doubly stochastic matrix is nonnegative.
@isnad1 id=le.1h5v.s7.5618146871e3 from=seed src=0 shape=164be969 vocab=82afc201
-/
lemma nonneg_of_mem_doublyStochastic (hM : M ∈ doublyStochastic R n) {i j : n} : 0 ≤ M i j :=
  hM.1 _ _

/-- Each row sum of a doubly stochastic matrix is 1.
@isnad1 id=eq.1h4v.s7.8f1cfb63c67b from=seed src=0 shape=f3bc514f vocab=5860c3d5
-/
lemma sum_row_of_mem_doublyStochastic (hM : M ∈ doublyStochastic R n) (i : n) : ∑ j, M i j = 1 :=
  (mem_doublyStochastic_iff_sum.1 hM).2.1 _

/-- Each column sum of a doubly stochastic matrix is 1.
@isnad1 id=eq.1h4v.s7.e1ae444a436e from=seed src=0 shape=3b53d2af vocab=5860c3d5
-/
lemma sum_col_of_mem_doublyStochastic (hM : M ∈ doublyStochastic R n) (j : n) : ∑ i, M i j = 1 :=
  (mem_doublyStochastic_iff_sum.1 hM).2.2 _

/-- A doubly stochastic matrix multiplied with the all-ones column vector is 1.
@isnad1 id=eq.1h3v.s7.1d69aca7b470 from=seed src=0 shape=54a700a3 vocab=b7c3d09f
-/
lemma mulVec_one_of_mem_doublyStochastic (hM : M ∈ doublyStochastic R n) : M *ᵥ 1 = 1 :=
  (mem_doublyStochastic.1 hM).2.1

/-- The all-ones row vector multiplied with a doubly stochastic matrix is 1.
@isnad1 id=eq.1h3v.s7.31924bf8bd5a from=seed src=0 shape=3a85c2bf vocab=f9e9cc89
-/
lemma one_vecMul_of_mem_doublyStochastic (hM : M ∈ doublyStochastic R n) : 1 ᵥ* M = 1 :=
  (mem_doublyStochastic.1 hM).2.2

/-- Every entry of a doubly stochastic matrix is less than or equal to 1.
@isnad1 id=le.1h5v.s7.249073104b47 from=seed src=0 shape=596afd4d vocab=82afc201
-/
lemma le_one_of_mem_doublyStochastic (hM : M ∈ doublyStochastic R n) {i j : n} :
    M i j ≤ 1 := by
  rw [← sum_row_of_mem_doublyStochastic hM i]
  exact single_le_sum (fun k _ => hM.1 _ k) (mem_univ j)

/-- The set of doubly stochastic matrices is convex.
@isnad1 id=convex.0h2v.s6.aee763116967 from=seed src=0 shape=e136b217 vocab=d4ee0bbd
-/
lemma convex_doublyStochastic : Convex R (doublyStochastic R n : Set (Matrix n n R)) := by
  intro x hx y hy a b ha hb h
  simp only [SetLike.mem_coe, mem_doublyStochastic_iff_sum] at hx hy ⊢
  simp [add_nonneg, ha, hb, mul_nonneg, hx, hy, sum_add_distrib, ← mul_sum, h]

/-- Any permutation matrix is doubly stochastic.
@isnad1 id=mem.0h3v.s6.dee7f176fa85 from=seed src=0 shape=9910e4c0 vocab=27cb88b3
-/
@[simp, grind ←]
lemma permMatrix_mem_doublyStochastic {σ : Equiv.Perm n} :
    σ.permMatrix R ∈ doublyStochastic R n := by grind

/-- A matrix is doubly stochastic iff its transpose is doubly stochastic
@isnad1 id=iff.0h3v.s7.5b5e8df74d98 from=seed src=0 shape=31b1a2fe vocab=53c1b968
-/
@[grind =]
lemma transpose_mem_doublyStochastic_iff :
    Mᵀ ∈ doublyStochastic R n ↔ M ∈ doublyStochastic R n := by grind

/-- Reindexing a matrix preserves double stochasticity.
@isnad1 id=mem.1h6v.s8.f592a48d30ca from=seed src=0 shape=c2f1f13a vocab=c8ee5a3d
-/
@[aesop safe apply]
lemma reindex_mem_doublyStochastic {m : Type*} [Fintype m] [DecidableEq m] {M : Matrix n n R}
    {e₁ e₂ : n ≃ m} (hM : M ∈ doublyStochastic R n) : M.reindex e₁ e₂ ∈ doublyStochastic R m := by
  grind

/-- Reindexing a matrix preserves double stochasticity.
@isnad1 id=iff.0h6v.s8.b5cad798bf0b from=seed src=0 shape=13d34959 vocab=c8ee5a3d
-/
@[grind =]
lemma reindex_mem_doublyStochastic_iff {m : Type*} [Fintype m] [DecidableEq m] {M : Matrix n n R}
    {e₁ e₂ : n ≃ m} : M.reindex e₁ e₂ ∈ doublyStochastic R m ↔ M ∈ doublyStochastic R n := by
  grind

/-- Applying a doubly stochastic matrix to a vector preserves its sum.
@isnad1 id=eq.1h4v.s7.4028f0413745 from=seed src=0 shape=af0c44e1 vocab=fb9099e3
-/
lemma sum_mulVec_of_mem_doublyStochastic {M : Matrix n n R} {x : n → R}
    (hA : M ∈ doublyStochastic R n) : ∑ i, (M *ᵥ x) i = ∑ i, x i := by
  apply sum_mulVec_of_mem_colStochastic
  grind

end OrderedSemiring

section LinearOrderedSemifield

variable [Semifield R] [LinearOrder R] [IsStrictOrderedRing R]

/--
A matrix is `s` times a doubly stochastic matrix iff all entries are nonnegative, and all row and
column sums are equal to `s`.

This lemma is useful for the proof of Birkhoff's theorem - in particular because it allows scaling
by nonnegative factors rather than positive ones only.
@isnad1 id=iff.1h4v.s8.e97a7ce6d295 from=seed src=0 shape=59a4ef77 vocab=ddb3cd04
-/
lemma exists_mem_doublyStochastic_eq_smul_iff {M : Matrix n n R} {s : R} (hs : 0 ≤ s) :
    (∃ M' ∈ doublyStochastic R n, M = s • M') ↔
      (∀ i j, 0 ≤ M i j) ∧ (∀ i, ∑ j, M i j = s) ∧ (∀ j, ∑ i, M i j = s) := by
  constructor
  case mp =>
    rintro ⟨M', hM', rfl⟩
    rw [mem_doublyStochastic_iff_sum] at hM'
    simp only [Matrix.smul_apply, smul_eq_mul, ← mul_sum]
    exact ⟨fun i j => mul_nonneg hs (hM'.1 _ _), by simp [hM']⟩
  rcases eq_or_lt_of_le hs with rfl | hs
  case inl =>
    simp only [zero_smul, exists_and_right, and_imp]
    intro h₁ h₂ _
    refine ⟨⟨1, Submonoid.one_mem _⟩, ?_⟩
    ext i j
    specialize h₂ i
    rw [sum_eq_zero_iff_of_nonneg (by simp [h₁ i])] at h₂
    exact h₂ _ (by simp)
  rintro ⟨hM₁, hM₂, hM₃⟩
  exact ⟨s⁻¹ • M, by simp [mem_doublyStochastic_iff_sum, ← mul_sum, hs.ne', *]⟩

end LinearOrderedSemifield
