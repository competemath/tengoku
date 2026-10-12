/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pjotr Buys
-/

module

public import Tengoku

@[expose] public section

/-!
# International Mathematical Olympiad 1997, Problem 4

An $n \times n$ matrix whose entries come from the set
$S = \{1, 2, \ldots, 2n - 1\}$ is called a *silver matrix* if, for each
$i = 1, \ldots, n$, the $i$-th row and the $i$-th column together contain
all elements of $S$. Show that:

  (a) there is no silver matrix for $n = 1997$;

  (b) silver matrices exist for infinitely many values of $n$.
-/

namespace Imo1997P4

/-- An `n × n` matrix `M` is a *silver matrix* if its entries come from
`S = {1, …, 2n - 1}` and, for each `i`, the `i`-th row and the `i`-th column
together contain all of `S`. -/
def SilverMatrix (n : ℕ) (M : Fin n → Fin n → ℕ) : Prop :=
  (∀ i j, M i j ∈ Finset.Icc 1 (2 * n - 1)) ∧
  (∀ i, (Finset.univ.image (fun j ↦ M i j) ∪ Finset.univ.image (fun j ↦ M j i))
          = Finset.Icc 1 (2 * n - 1))

open Finset

/-! ### Rows, columns and crosses -/

def row {n : ℕ} (i : Fin n) : Finset (Fin n × Fin n) := {i} ×ˢ univ

def col {n : ℕ} (i : Fin n) : Finset (Fin n × Fin n) := univ ×ˢ {i}

def cross {n : ℕ} (i : Fin n) : Finset (Fin n × Fin n) := row i ∪ col i

/--
@isnad1 id=eq.0h2v.s4.c14285d90730 from=translated src=- shape=41262a2f vocab=be2d9fef
-/
lemma card_row {n : ℕ} (i : Fin n) : (row i).card = n := by simp [row]

/--
@isnad1 id=eq.0h2v.s4.c6d56ca09ac6 from=translated src=- shape=41262a2f vocab=f3415474
-/
lemma card_col {n : ℕ} (i : Fin n) : (col i).card = n := by simp [col]

/--
@isnad1 id=mem.0h3v.s5.4aaf6aceb417 from=translated src=- shape=1ba7514c vocab=b5377177
-/
lemma row_mem {n : ℕ} (i j : Fin n) : (i, j) ∈ row i :=
  mk_mem_product (mem_singleton_self i) (mem_univ j)

/--
@isnad1 id=mem.0h3v.s5.f1458b29b8e4 from=translated src=- shape=09d2198c vocab=b8cbbe7b
-/
lemma col_mem {n : ℕ} (i j : Fin n) : (i, j) ∈ col j :=
  mk_mem_product (mem_univ i) (mem_singleton_self j)

/--
@isnad1 id=mem.0h3v.s5.69168d2b46e0 from=translated src=- shape=1ba7514c vocab=669f9ae9
-/
lemma cross_mem_left {n : ℕ} (i j : Fin n) : (i, j) ∈ cross i :=
  mem_union_left _ (row_mem _ _)

/--
@isnad1 id=eq.0h1v.s5.5f0b03d02c9c from=translated src=- shape=07c606ff vocab=cf1c8f19
-/
lemma row_union (n : ℕ) : (univ : Finset (Fin n)).biUnion row = univ :=
  eq_univ_iff_forall.2
    (fun (i, _) ↦ mem_biUnion.mpr ⟨i, mem_univ _, row_mem _ _⟩)

/--
@isnad1 id=eq.0h1v.s5.cd5525a1e31d from=translated src=- shape=07c606ff vocab=2236dd1b
-/
lemma col_union (n : ℕ) : (univ : Finset (Fin n)).biUnion col = univ :=
  eq_univ_iff_forall.2
    (fun (_, j) ↦ mem_biUnion.mpr ⟨j, mem_univ _, col_mem _ _⟩)

/--
@isnad1 id=pairwise.0h1v.s4.ad6e6c0fbf1f from=translated src=- shape=acf24888 vocab=f7747bb5
-/
lemma row_disjoint (n : ℕ) : (Set.univ : Set (Fin n)).PairwiseDisjoint row :=
  fun _ _ _ _ h ↦ disjoint_product.2 (Or.inl (disjoint_singleton.2 h))

/--
@isnad1 id=pairwise.0h1v.s4.1fa6273dab4e from=translated src=- shape=acf24888 vocab=61f318a6
-/
lemma col_disjoint (n : ℕ) : (Set.univ : Set (Fin n)).PairwiseDisjoint col :=
  fun _ _ _ _ h ↦ disjoint_product.2 (Or.inr (disjoint_singleton.2 h))

/--
@isnad1 id=eq.0h2v.s6.6967ba9d25b6 from=translated src=- shape=766ca2cb vocab=329323b8
-/
lemma row_inter_col {n : ℕ} (i : Fin n) : row i ∩ col i = {(i, i)} := by
  rw [row, col, product_inter_product]; simp

/--
@isnad1 id=eq.0h2v.s5.a3e856af6540 from=translated src=- shape=0c9e6f7e vocab=bd36bc78
-/
lemma card_cross {n : ℕ} (i : Fin n) : (cross i).card = 2 * n - 1 := by
  rw [cross, card_union, card_row, card_col, row_inter_col, card_singleton,
    Nat.two_mul]

/--
@isnad1 id=eq.0h3v.s6.0ec46ee4718e from=translated src=- shape=abca8ab9 vocab=4ab301f1
-/
lemma image_row {n : ℕ} (M : Fin n → Fin n → ℕ) (i : Fin n) :
    univ.image (fun j ↦ M i j) = (row i).image ↿M := by
  ext x; simp [row, Function.HasUncurry.uncurry]

/--
@isnad1 id=eq.0h3v.s6.fe437e28a394 from=translated src=- shape=018b7d13 vocab=cc50f9cb
-/
lemma image_col {n : ℕ} (M : Fin n → Fin n → ℕ) (i : Fin n) :
    univ.image (fun j ↦ M j i) = (col i).image ↿M := by
  ext x; simp [col, Function.HasUncurry.uncurry]

/--
@isnad1 id=eq.1h3v.s6.19645f946d36 from=translated src=- shape=3ece482f vocab=26c77bfb
-/
lemma image_cross {n : ℕ} {M : Fin n → Fin n → ℕ} (h : SilverMatrix n M) (i : Fin n) :
    (cross i).image ↿M = Icc 1 (2 * n - 1) := by
  rw [cross, image_union, ← image_row, ← image_col]
  exact h.2 i

/--
@isnad1 id=iff.0h2v.s6.d0b9aca84abb from=translated src=- shape=8902ce73 vocab=26c77bfb
-/
lemma silver_iff_cross {n : ℕ} (M : Fin n → Fin n → ℕ) :
    SilverMatrix n M ↔ ∀ i, (cross i).image ↿M = Icc 1 (2 * n - 1) := by
  refine ⟨image_cross, fun h ↦ ⟨fun i j ↦ ?_, fun i ↦ ?_⟩⟩ <;> rw [← h i]
  · exact mem_image.2 ⟨_, cross_mem_left i j, rfl⟩
  · rw [image_row, image_col, ← image_union, cross]

/-! ### Part (a): no silver matrix of odd size `n > 1` -/

/--
@isnad1 id=eq.1h3v.s6.464dea86b55d from=translated src=- shape=65a0d5e8 vocab=6420bec7
-/
lemma val_map_cross {n : ℕ} {M : Fin n → Fin n → ℕ} (h : SilverMatrix n M) (i : Fin n) :
    (cross i).val.map ↿M = Multiset.Icc 1 (2 * n - 1) := by
  rw [← image_val_of_injOn (injOn_of_card_image_eq (by
    simp [card_cross, image_cross h, Nat.card_Icc])), image_cross h i]; rfl

/--
@isnad1 id=eq.1h3v.s7.6225fb9feba0 from=translated src=- shape=dc4d2fb4 vocab=af8a4858
-/
lemma multiset_row_col {n : ℕ} {M : Fin n → Fin n → ℕ} (h : SilverMatrix n M) (i : Fin n) :
    (row i).val.map ↿M + (col i).val.map ↿M
      = M i i ::ₘ Multiset.Icc 1 (2 * n - 1) := by
  rw [← val_map_cross h i, ← Multiset.map_add, ← Multiset.union_add_inter,
    ← union_val, ← inter_val, row_inter_col, singleton_val,
    Multiset.map_add, Multiset.map_singleton, ← Multiset.singleton_add, add_comm]; rfl

/--
@isnad1 id=eq.0h1v.s6.054f15e937f7 from=translated src=- shape=4ea01ca6 vocab=44a4caf3
-/
lemma sum_row_val {n : ℕ} : ∑ i : Fin n, (row i).val = univ.val := by
  rw [← row_union n, ← disjiUnion_eq_biUnion _ _ (by simpa using row_disjoint n)]; rfl

/--
@isnad1 id=eq.0h1v.s6.623a9567924e from=translated src=- shape=4ea01ca6 vocab=c2c722cc
-/
lemma sum_col_val {n : ℕ} : ∑ i : Fin n, (col i).val = univ.val := by
  rw [← col_union n, ← disjiUnion_eq_biUnion _ _ (by simpa using col_disjoint n)]; rfl

/--
@isnad1 id=eq.0h2v.s7.56afa86b9c54 from=translated src=- shape=6602b72a vocab=290c5eca
-/
lemma sum_row_col_val {n : ℕ} (M : Fin n → Fin n → ℕ) :
    ∑ i, ((row i).val.map ↿M + (col i).val.map ↿M)
      = 2 • univ.val.map ↿M := by
  simp only [sum_add_distrib, ← Multiset.coe_mapAddMonoidHom, ← map_sum,
    sum_row_val, sum_col_val, two_nsmul]

/--
@isnad1 id=eq.1h2v.s7.2c0234808a42 from=translated src=- shape=68a8f113 vocab=c3015e05
-/
lemma sum_row_col_val_silver {n : ℕ} {M : Fin n → Fin n → ℕ} (h : SilverMatrix n M) :
    ∑ i, ((row i).val.map ↿M + (col i).val.map ↿M)
      = univ.val.map (fun x ↦ M x x) + n • Multiset.Icc 1 (2 * n - 1) := by
  simp_rw [multiset_row_col h, ← Multiset.singleton_add, sum_add_distrib,
    sum_const, card_univ, Fintype.card_fin, ← Finset.sum_multiset_singleton,
    ← Multiset.coe_mapAddMonoidHom, map_sum]
  rfl

/--
@isnad1 id=ex.1h2v.s6.4feca333652b from=translated src=- shape=d407a485 vocab=15f274ed
-/
lemma exists_diag_count_zero {n : ℕ} (hn : 1 < n) (M : Fin n → Fin n → ℕ) :
    ∃ v ∈ Multiset.Icc 1 (2 * n - 1),
      (univ.val.map (fun x ↦ M x x)).count v = 0 := by
  set D := univ.val.map (fun x ↦ M x x) with hD
  have hcard : D.toFinset.card < (Icc 1 (2 * n - 1)).card := by
    have : D.toFinset.card ≤ n := by simpa [hD] using Multiset.toFinset_card_le D
    rw [Nat.card_Icc]
    lia
  obtain ⟨v, hv, hv'⟩ := exists_mem_notMem_of_card_lt_card hcard
  exact ⟨v, hv, by simpa using hv'⟩

/--
@isnad1 id=not.2h1v.s5.a4b15349a849 from=translated src=- shape=c2021f1f vocab=5167fcb0
-/
lemma no_odd_SilverMatrix {n : ℕ} (hn : 1 < n) (hnodd : Odd n) :
    ¬ ∃ M : Fin n → Fin n → ℕ, SilverMatrix n M := by
  intro ⟨M, h⟩
  obtain ⟨x, hx₁, hx₂⟩ := exists_diag_count_zero hn M
  have heven : Even ((∑ i, ((row i).val.map ↿M + (col i).val.map ↿M)).count x) := by
    rw [sum_row_col_val M, Multiset.count_nsmul]
    exact even_two_mul _
  apply Nat.not_odd_iff_even.mpr heven
  rw [sum_row_col_val_silver h, Multiset.count_add, hx₂, zero_add,
    Multiset.count_nsmul, Multiset.count_eq_one_of_mem Multiset.nodup_Icc hx₁,
    mul_one]
  assumption

/-! ### Part (b): doubling a silver matrix -/

def blockMatrix {n : ℕ} (A B C D : Fin n → Fin n → ℕ) : Fin (n + n) → Fin (n + n) → ℕ :=
  fun a b ↦ Matrix.fromBlocks A B C D (finSumFinEquiv.symm a) (finSumFinEquiv.symm b)

/--
@isnad1 id=eq.0h6v.s8.f72f5239b810 from=translated src=- shape=0112bb29 vocab=028f015c
-/
lemma blockMatrix_row_left {n : ℕ} (A B C D : Fin n → Fin n → ℕ) (i : Fin n) :
    (row (finSumFinEquiv (.inl i))).image ↿(blockMatrix A B C D)
      = (row i).image ↿A ∪ (row i).image ↿B := by
  ext
  simp [← image_row, finSumFinEquiv.symm.exists_congr_left, blockMatrix,
    Matrix.fromBlocks]

/--
@isnad1 id=eq.0h6v.s8.c77a8a68fdce from=translated src=- shape=b2d3db1b vocab=4ee6e499
-/
lemma blockMatrix_row_right {n : ℕ} (A B C D : Fin n → Fin n → ℕ) (i : Fin n) :
    (row (finSumFinEquiv (.inr i))).image ↿(blockMatrix A B C D)
      = (row i).image ↿C ∪ (row i).image ↿D := by
  ext
  simp [← image_row, finSumFinEquiv.symm.exists_congr_left, blockMatrix,
    Matrix.fromBlocks, -finSumFinEquiv_apply_right]

/--
@isnad1 id=eq.0h6v.s8.5b2311da1d3a from=translated src=- shape=4c83c425 vocab=edb35169
-/
lemma blockMatrix_col_left {n : ℕ} (A B C D : Fin n → Fin n → ℕ) (j : Fin n) :
    (col (finSumFinEquiv (.inl j))).image ↿(blockMatrix A B C D)
      = (col j).image ↿A ∪ (col j).image ↿C := by
  ext
  simp [← image_col, finSumFinEquiv.symm.exists_congr_left, blockMatrix,
    Matrix.fromBlocks]

/--
@isnad1 id=eq.0h6v.s8.a86999ec5dd7 from=translated src=- shape=c2eb03b2 vocab=1b6eb654
-/
lemma blockMatrix_col_right {n : ℕ} (A B C D : Fin n → Fin n → ℕ) (j : Fin n) :
    (col (finSumFinEquiv (.inr j))).image ↿(blockMatrix A B C D)
      = (col j).image ↿B ∪ (col j).image ↿D := by
  ext
  simp [← image_col, finSumFinEquiv.symm.exists_congr_left, blockMatrix,
    Matrix.fromBlocks, -finSumFinEquiv_apply_right]

/--
@isnad1 id=eq.0h6v.s8.53cb846f9abf from=translated src=- shape=6418fe66 vocab=e35d9f6a
-/
lemma blockMatrix_cross_left {n : ℕ} (A B C D : Fin n → Fin n → ℕ) (i : Fin n) :
    (cross (finSumFinEquiv (.inl i))).image ↿(blockMatrix A B C D) =
    (cross i).image ↿A ∪ (row i).image ↿B ∪ (col i).image ↿C := by
  rw [cross, image_union, blockMatrix_row_left, blockMatrix_col_left, cross,
    image_union]
  ac_rfl

/--
@isnad1 id=eq.0h6v.s8.7d5dc43c0589 from=translated src=- shape=d75c73cc vocab=e2d72078
-/
lemma blockMatrix_cross_right {n : ℕ} (A B C D : Fin n → Fin n → ℕ) (i : Fin n) :
    (cross (finSumFinEquiv (.inr i))).image ↿(blockMatrix A B C D) =
    (cross i).image ↿D ∪ (row i).image ↿C ∪ (col i).image ↿B := by
  rw [cross, image_union, blockMatrix_row_right, blockMatrix_col_right, cross,
    image_union]
  ac_rfl

def latinSquare {n : ℕ} (v : Fin n → ℕ) : Fin n → Fin n → ℕ := fun i j ↦ v (i - j)

/--
@isnad1 id=eq.0h3v.s6.8f14649c98b0 from=translated src=- shape=230af6a3 vocab=6ffca079
-/
lemma latinSquare_row {n : ℕ} (v : Fin n → ℕ) (i : Fin n) :
    (row i).image ↿(latinSquare v) = univ.image v := by
  have : NeZero n := ⟨i.pos.ne'⟩
  rw [← image_row, show (fun j ↦ latinSquare v i j) = v ∘ Equiv.subLeft i from rfl,
    ← Finset.image_image, Finset.image_univ_equiv]

/--
@isnad1 id=eq.0h3v.s6.97f6fea93052 from=translated src=- shape=230af6a3 vocab=47beab76
-/
lemma latinSquare_col {n : ℕ} (v : Fin n → ℕ) (j : Fin n) :
    (col j).image ↿(latinSquare v) = univ.image v := by
  have : NeZero n := ⟨j.pos.ne'⟩
  rw [← image_col, show (fun i ↦ latinSquare v i j) = v ∘ Equiv.subRight j from rfl,
    ← Finset.image_image, Finset.image_univ_equiv]

/--
@isnad1 id=eq.1h3v.s5.2b3ab40bb04f from=translated src=- shape=7fe48128 vocab=6bdb2861
-/
lemma Icc_union' {a b c : ℕ} (h : a ≤ b ∧ b ≤ c) : Icc a (b - 1) ∪ Icc b c = Icc a c := by
  ext _; simp only [mem_union, mem_Icc]; lia

/--
@isnad1 id=ex.2h1v.s6.9275551a5740 from=translated src=- shape=a769332c vocab=24fedd87
-/
lemma silver_double {n : ℕ} (hn : 1 ≤ n) (h : ∃ M, SilverMatrix n M) :
    ∃ M, SilverMatrix (n + n) M := by
  obtain ⟨M, hM⟩ := h
  refine ⟨blockMatrix M
    (latinSquare ((Icc (2 * n) (3 * n - 1)).orderEmbOfFin (by rw [Nat.card_Icc]; lia)))
    (latinSquare ((Icc (3 * n) (4 * n - 1)).orderEmbOfFin (by rw [Nat.card_Icc]; lia)))
    M, (silver_iff_cross _).2 fun a ↦ ?_⟩
  obtain ⟨_ | _, rfl⟩ := finSumFinEquiv.surjective a
  · rw [blockMatrix_cross_left, image_cross hM, latinSquare_row, latinSquare_col,
      image_orderEmbOfFin_univ, image_orderEmbOfFin_univ, Icc_union' (by lia),
      Icc_union' (by lia), (by ring : 2 * (n + n) = 4 * n)]
  · rw [blockMatrix_cross_right, image_cross hM, latinSquare_row, latinSquare_col,
      image_orderEmbOfFin_univ, image_orderEmbOfFin_univ, union_right_comm,
      Icc_union' (by lia), Icc_union' (by lia), (by ring : 2 * (n + n) = 4 * n)]

/--
@isnad1 id=ex.0h1v.s6.b7831956d2a6 from=translated src=- shape=84b65f14 vocab=6a1ceac7
-/
lemma silver_two_pow : ∀ k, ∃ M, SilverMatrix (2 ^ k) M
  | .zero   => ⟨1, by simp, by simp⟩
  | .succ _ => by
      rw [pow_succ, mul_two]
      exact silver_double Nat.one_le_two_pow (silver_two_pow _)

end Imo1997P4
