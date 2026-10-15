/-
Copyright (c) 2026 Dhyan Aranha and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhyan Aranha, contributors
-/
module

public import Tengoku

/-!
# LeanPool.Monsky.SimplexBasic

Imported Lean Pool material for `LeanPool.Monsky.SimplexBasic`.
-/

@[expose] public section

namespace LeanPool.Monsky

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

open Finset

-- Shorthand for defining an element of ℝ²
/-- The plane vector with the two given real coordinates. -/
def v (x y : ℝ) : ℝ² := !₂[x, y]

/--
@isnad1 id=eq.0h2v.s6.8b5affc9613e from=translated src=- shape=02f1c7bf vocab=65a0cfcd
-/
@[simp]
lemma v₀_val {x y : ℝ} : (v x y) 0 = x := by simp [v]
/--
@isnad1 id=eq.0h2v.s6.4435ac0486fc from=translated src=- shape=6e7fa9ed vocab=65a0cfcd
-/
@[simp]
lemma v₁_val {x y : ℝ} : (v x y) 1 = y := by simp [v]

-- Definition of an n-dimensional standard simplex.
/-- The closed standard `n`-simplex of nonnegative weights summing to one. -/
def closedSimplex (n : ℕ) : Set (Fin n → ℝ) := {α | (∀ i, 0 ≤ α i) ∧ ∑ i, α i = 1}
/-- The open standard `n`-simplex of positive weights summing to one. -/
def openSimplex (n : ℕ) : Set (Fin n → ℝ) := {α | (∀ i, 0 < α i) ∧ ∑ i, α i = 1}

/-
  The Fin n → ℝ² in the following definitions represents the vertices of a polygon.
  Beware: Whenever the n vertices do not define an n-gon, i.e. a vertex lies within the
  convex hull of the others, the openHull does not give the topological interior of the closed
  hull.

  Also when f i = P for all i, both the closedHull and openHull are {P i}.
-/
/-- The closed convex hull of a finite point family, via the closed simplex. -/
def closedHull {n : ℕ} (f : Fin n → ℝ²) : Set ℝ² := (fun α ↦ ∑ i, α i • f i) '' closedSimplex n
/-- The open convex hull of a finite point family, via the open simplex. -/
def openHull {n : ℕ} (f : Fin n → ℝ²) : Set ℝ² := (fun α ↦ ∑ i, α i • f i) '' openSimplex n

/- Corner of the standard simplex.-/
/-- The `i`-th vertex of the standard simplex, as a weight function. -/
def simplexVertex {n : ℕ} (i : Fin n) : Fin n → ℝ :=
    fun j ↦ if i = j then 1 else 0

/--
@isnad1 id=mem.0h2v.s4.cc21b6679b7b from=translated src=- shape=e565237d vocab=8a1d4ebf
-/
lemma simplexVertex_in_simplex {n : ℕ} {i : Fin n} : simplexVertex i ∈ closedSimplex n := by
  exact ⟨fun j ↦ by by_cases h : i = j <;> simp [simplexVertex, h], by simp [simplexVertex]⟩

/--
@isnad1 id=eq.0h0v.s5.3552c8dc2c61 from=translated src=- shape=844708c8 vocab=6f1976b1
-/
lemma closedSimplex_zero_empty : closedSimplex 0 = ∅ := by
  rw [←Set.not_nonempty_iff_eq_empty]
  exact fun ⟨_,⟨_,hx⟩⟩ ↦ by rw [@Fin.sum_univ_zero] at hx; exact zero_ne_one' _ hx

/--
@isnad1 id=eq.0h0v.s5.f6b75d0f738e from=translated src=- shape=844708c8 vocab=36e4e687
-/
lemma openSimplex_zero_empty : openSimplex 0 = ∅ := by
  rw [←Set.not_nonempty_iff_eq_empty]
  exact fun ⟨_,⟨_,hx⟩⟩ ↦ by rw [@Fin.sum_univ_zero] at hx; exact zero_ne_one' _ hx

/--
@isnad1 id=eq.0h3v.s7.39a465ab8d83 from=translated src=- shape=5abaeb22 vocab=172e4ba0
-/
@[simp]
lemma simplexVertex_image {n : ℕ} {i : Fin n} (f : Fin n → ℝ²) :
    ∑ k, (simplexVertex i k) • f k = f i := by simp [simplexVertex]

/--
@isnad1 id=mem.0h3v.s5.78d96977bc31 from=translated src=- shape=b9191cd4 vocab=f6b3de85
-/
@[simp]
lemma corner_in_closedHull {n : ℕ} {i : Fin n} {P : Fin n → ℝ²} : P i ∈ closedHull P := by
  exact ⟨simplexVertex i, simplexVertex_in_simplex, by simp⟩

/--
@isnad1 id=eq.1h2v.s6.b18374dbd888 from=translated src=- shape=e8cbc467 vocab=d4761bb5
-/
lemma closedHull_constant {n : ℕ} {P : ℝ²} (hn : n ≠ 0) :
    closedHull (fun (_ : Fin n) ↦ P) = {P} := by
  ext _
  constructor
  · intro ⟨_, hα, hαv⟩
    simp [←hαv, ←sum_smul, hα.2, one_smul, Set.mem_singleton_iff]
  · intro hv; rw [hv]
    exact corner_in_closedHull (i := ⟨0, Nat.zero_lt_of_ne_zero hn⟩)

/--
@isnad1 id=eq.1h4v.s6.ea0da3a0ea61 from=translated src=- shape=a7d7a3b4 vocab=d4761bb5
-/
lemma closedHull_constant_rev {n : ℕ} {P : ℝ²} {f : Fin n → ℝ²}
    (hc : closedHull f = {P}) : ∀ i, f i = P := by
  simp_rw [←Set.mem_singleton_iff, ←hc]
  exact fun _ ↦ corner_in_closedHull

/--
@isnad1 id=nonempty.1h2v.s5.521d9552e475 from=translated src=- shape=54e74b3a vocab=ecdf64a7
-/
lemma open_pol_nonempty {n : ℕ} (hn : 0 < n) (P : Fin n → ℝ²) : Set.Nonempty (openHull P) := by
  use ∑ i, (1/(n : ℝ)) • P i, fun _ ↦ (1/(n : ℝ))
  refine ⟨⟨fun _ ↦ by simp [hn], ?_⟩, by simp⟩
  simpa only [one_div, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    using mul_inv_cancel₀ (by simp; linarith)

/--
@isnad1 id=le.0h1v.s4.d9a279bfdedd from=translated src=- shape=e71db7ee vocab=e724d0a6
-/
lemma open_sub_closedSimplex {n : ℕ} : openSimplex n ⊆ closedSimplex n :=
  fun _ ⟨hαpos, hαsum⟩ ↦ ⟨fun i ↦ by linarith [hαpos i], hαsum⟩

/--
@isnad1 id=le.0h2v.s5.2f3724f6b841 from=translated src=- shape=9b9f3241 vocab=8ce55651
-/
lemma open_sub_closed {n : ℕ} (P : Fin n → ℝ²) : openHull P ⊆ closedHull P :=
  Set.image_mono open_sub_closedSimplex

/--
@isnad1 id=nonempty.1h2v.s5.e0b4989e209b from=translated src=- shape=54e74b3a vocab=86398d08
-/
lemma closed_pol_nonempty {n : ℕ} (hn : 0 < n) (P : Fin n → ℝ²) : Set.Nonempty (closedHull P) :=
  Set.Nonempty.mono (open_sub_closed P) (open_pol_nonempty hn P)

/--
@isnad1 id=eq.1h2v.s6.6ad79864f553 from=translated src=- shape=e8cbc467 vocab=3a79cb39
-/
lemma openHull_constant {n : ℕ} {P : ℝ²} (hn : n ≠ 0) :
    openHull (fun (_ : Fin n) ↦ P) = {P} :=
  (Set.Nonempty.subset_singleton_iff (open_pol_nonempty (Nat.zero_lt_of_ne_zero hn) _)).mp
      (subset_of_subset_of_eq (open_sub_closed _) (closedHull_constant hn))

/--
@isnad1 id=eq.0h1v.s5.bec732419e04 from=translated src=- shape=b5c83e50 vocab=3fd06e45
-/
lemma closedHull_zero_dim (f : Fin 0 → ℝ²) : closedHull f = ∅ := by
  rw [closedHull, closedSimplex_zero_empty, Set.image_empty]

/--
@isnad1 id=eq.0h1v.s5.83efc98c8736 from=translated src=- shape=b5c83e50 vocab=1214dc81
-/
lemma openHull_zero_dim (f : Fin 0 → ℝ²) : openHull f = ∅ := by
  rw [openHull, openSimplex_zero_empty, Set.image_empty]

/-- The point obtained as a weighted combination of a point family. -/
noncomputable def linearCombination {n : ℕ} (α : Fin n → ℝ) (f : Fin n → ℝ²)
    : ℝ² := ∑ i, α i • f i

/--
@isnad1 id=mem.1h3v.s6.1a00711dede2 from=translated src=- shape=d643dfba vocab=34094a60
-/
lemma linear_co_closed {n : ℕ} {α : Fin n → ℝ} (f : Fin n → ℝ²) (h : α ∈ closedSimplex n) :
    linearCombination α f ∈ closedHull f := ⟨α, h, by rfl⟩

/- Implications of the requirements that (∀ i, 0 ≤ α i),  ∑ i, α i = 1. -/

/--
@isnad1 id=eq.3h4v.s5.c45e39157740 from=translated src=- shape=d72389a8 vocab=5ccb2440
-/
lemma simplex_co_eq_1 {n : ℕ} {α : Fin n → ℝ} {i : Fin n}
    (h₁ : α ∈ closedSimplex n) (h₂ : α i = 1) : ∀ j, j ≠ i → α j = 0 := by
  by_contra hcontra; push Not at hcontra
  have ⟨j, hji, hj0⟩ := hcontra
  rw [←lt_self_iff_false (1 : ℝ)]
  calc
    1 = α i               := h₂.symm
    _ < α i + α j         := by rw [lt_add_iff_pos_right]; exact lt_of_le_of_ne (h₁.1 j) (hj0.symm)
    _ = ∑(k ∈ {i,j}), α k := (sum_pair hji.symm).symm
    _ ≤ ∑ k, α k          := sum_le_univ_sum_of_nonneg h₁.1
    _ = 1                 := h₁.2

/--
@isnad1 id=ex.1h2v.s5.bfd14f4cdb4e from=translated src=- shape=ee71b5f6 vocab=7ce2c050
-/
lemma simplex_exists_co_pos {n : ℕ} {α : Fin n → ℝ} (h : α ∈ closedSimplex n)
    : ∃ i, 0 < α i := by
  by_contra hcontra; push Not at hcontra
  have t : 1 ≤ (0: ℝ)  := by
    calc
      1 = ∑ i, α i        := h.2.symm
      _ ≤ ∑ (i: Fin n), 0 := sum_le_sum fun i _ ↦ hcontra i
      _ = 0               := Fintype.sum_eq_zero _ (fun _ ↦ rfl)
  linarith

/--
@isnad1 id=le.1h3v.s5.c6f0e7766852 from=translated src=- shape=f22ab521 vocab=80480007
-/
lemma simplex_co_leq_1 {n : ℕ} {α : Fin n → ℝ}
    (h₁ : α ∈ closedSimplex n) : ∀ i, α i ≤ 1 := by
  by_contra hcontra; push Not at hcontra
  have ⟨i,hi⟩ := hcontra
  rw [←lt_self_iff_false (1 : ℝ)]
  calc
    1   < α i             := hi
    _   = ∑ k ∈ {i}, α k  := (sum_singleton _ _).symm
    _   ≤ ∑ k, α k        := sum_le_univ_sum_of_nonneg h₁.1
    _   = 1               := h₁.2

/--
@isnad1 id=lt.2h3v.s5.0e1f7a958629 from=translated src=- shape=8329228a vocab=6f2b312b
-/
lemma simplex_co_leq_1_open {n : ℕ} {α : Fin n → ℝ} (hn : 1 < n)
    (h₁ : α ∈ openSimplex n) : ∀ i, α i < 1 := by
  intro i
  apply lt_of_le_of_ne (simplex_co_leq_1 (open_sub_closedSimplex h₁) i)
  intro hα
  have hj : ∃ j, i ≠ j := by
    by_cases hs : i = ⟨0, by linarith⟩
    · use ⟨1, by linarith⟩
      simp [hs]
    · use ⟨0, by linarith⟩
  have ⟨j, hj⟩ := hj
  linarith [h₁.1 j, simplex_co_eq_1 (open_sub_closedSimplex h₁) hα j hj.symm]

/- Some lemmas specifically about Fin 2 → ℝ. -/

/--
@isnad1 id=eq.1h2v.s7.f18863dfb291 from=translated src=- shape=ee03cdb8 vocab=7b61dff6
-/
lemma simplex_closed_sub_fin2 {α : Fin 2 → ℝ} (h : α ∈ closedSimplex 2) :
    ∀ i, α i = 1 - α ((fun | 0 => 1 | 1 => 0) i) := by
    intro i;
    rw [←h.2, Fin.sum_univ_two]
    fin_cases i <;> simp

/--
@isnad1 id=eq.1h2v.s7.fa9aaa63f09b from=translated src=- shape=ee03cdb8 vocab=c8c05d4c
-/
lemma simplex_open_sub_fin2 {α : Fin 2 → ℝ} (h : α ∈ openSimplex 2) :
    ∀ i, α i = 1 - α ((fun | 0 => 1 | 1 => 0) i) :=
  simplex_closed_sub_fin2 (open_sub_closedSimplex h)

/-- Encodes a real `x` as the pair of weights `(x, 1 - x)`. -/
def real_to_fin_2 (x : ℝ) : (Fin 2 → ℝ) := fun | 0 => x | 1 => 1 - x

/--
@isnad1 id=mem.2h1v.s5.8d0f05f2cb54 from=translated src=- shape=565774e1 vocab=6808f418
-/
lemma real_to_fin_2_closed {x : ℝ} (h₁ : 0 ≤ x) (h₂ : x ≤ 1)
    : real_to_fin_2 x ∈ closedSimplex 2 :=
  ⟨fun i ↦ by fin_cases i <;> (simp only [real_to_fin_2, sub_nonneg]; assumption),
    by simp only [real_to_fin_2, Fin.sum_univ_two, add_sub_cancel]⟩

/--
@isnad1 id=mem.2h1v.s5.7f7aba388d93 from=translated src=- shape=565774e1 vocab=0cb76e8e
-/
lemma real_to_fin_2_open {x : ℝ} (h₁ : 0 < x) (h₂ : x < 1)
    : real_to_fin_2 x ∈ openSimplex 2 :=
  ⟨fun i ↦ by fin_cases i <;> (simp only [real_to_fin_2, sub_pos]; assumption),
    by simp only [real_to_fin_2, Fin.sum_univ_two, add_sub_cancel]⟩

/- Vertex set of polygon P₁ lies inside the closed hull of polygon P₂ implies
    the closed hull of P₁ lies inside the closed hull of P₂. -/
/--
@isnad1 id=le.1h4v.s6.5991191818cc from=translated src=- shape=c19bfc14 vocab=53cc9301
-/
lemma closedHull_convex {n₁ n₂ : ℕ} {P₁ : Fin n₁ → ℝ²} {P₂ : Fin n₂ → ℝ²}
  (h : ∀ i, P₁ i ∈ closedHull P₂) :
  closedHull P₁ ⊆ closedHull P₂ := by
  intro p ⟨β, hβ, hβp⟩
  use fun i ↦ ∑ k, (β k) * (Classical.choose (h k) i)
  refine ⟨⟨?_,?_⟩,?_⟩
  · exact fun _ ↦ Fintype.sum_nonneg fun _ ↦
      mul_nonneg (hβ.1 _) ((Classical.choose_spec (h _)).1.1 _)
  · simp_rw [sum_comm (γ := Fin n₂), ←mul_sum, (Classical.choose_spec (h _)).1.2,
      mul_one]
    exact hβ.2
  · simp_rw [sum_smul, mul_smul, sum_comm (γ := Fin n₂), ←smul_sum,
      (Classical.choose_spec (h _)).2]
    exact hβp

/--
@isnad1 id=mem.2h4v.s8.323e61917f44 from=translated src=- shape=230c99c1 vocab=ab8a104b
-/
lemma closedHull_openHull_com {n : ℕ} {P : Fin n → ℝ²} {x y : ℝ²}
  (hx : x ∈ openHull P) (hy : y ∈ closedHull P) :
    (1/(2:ℝ)) • x + (1/(2:ℝ)) • y ∈ openHull P := by
  have ⟨α, hα, hαx⟩ := hx
  have ⟨β, hβ, hβy⟩ := hy
  use fun i ↦ (1/(2 : ℝ)) * α i + (1/(2:ℝ)) * β i
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro i
    linarith [hα.1 i, hβ.1 i]
  · rw [sum_add_distrib, ←mul_sum,  ←mul_sum, hα.2, hβ.2]
    ring
  · simp_rw [add_smul _, sum_add_distrib, mul_smul, ←smul_sum, hαx, hβy]

/-
  We define the boundary of a polygon as the elements in the closed hull but not
  in the open hull.
-/

/-- The boundary of the convex hull of a point family: closed hull minus open hull. -/
def boundary {n : ℕ} (P : Fin n → ℝ²) : Set ℝ² := (closedHull P) \ (openHull P)

/--
@isnad1 id=le.0h2v.s5.7bc86be35119 from=translated src=- shape=9b9f3241 vocab=09f434a1
-/
lemma boundary_sub_closed {n : ℕ} (P : Fin n → ℝ²) : boundary P ⊆ closedHull P :=
  Set.sdiff_subset

/--
@isnad1 id=not.1h3v.s6.752c766586ae from=translated src=- shape=5a15548a vocab=edae68f5
-/
lemma boundary_not_in_open {n : ℕ} {P : Fin n → ℝ²} {x : ℝ²} (hx : x ∈ boundary P) :
    x ∉ openHull P := hx.2

/--
@isnad1 id=mem.1h3v.s6.366b24b622aa from=translated src=- shape=101b0142 vocab=5ab86e86
-/
lemma boundary_in_closed {n : ℕ} {P : Fin n → ℝ²} {x : ℝ²} (hx : x ∈ boundary P) :
    x ∈ closedHull P := Set.mem_of_mem_sdiff hx

/--
@isnad1 id=eq.0h2v.s6.c5a77de2e3b4 from=translated src=- shape=0fad6a7f vocab=524013e3
-/
lemma boundary_int_open_empty {n : ℕ} {P : Fin n → ℝ²} : boundary P ∩ openHull P = ∅ :=
  Set.sdiff_inter_self

/--
@isnad1 id=disjoint.0h2v.s7.b334420fd1e5 from=translated src=- shape=9b9f3241 vocab=c6e5e070
-/
lemma boundary_open_disjoint {n : ℕ} {P : Fin n → ℝ²} : Disjoint (boundary P) (openHull P) :=
  Set.disjoint_iff_inter_eq_empty.mpr boundary_int_open_empty

/--
@isnad1 id=eq.0h2v.s5.62b23a5c16e2 from=translated src=- shape=5c642179 vocab=426e0df6
-/
lemma boundary_union_open_closed {n : ℕ} {P : Fin n → ℝ²} :
    boundary P ∪ openHull P = closedHull P := Set.sdiff_union_of_subset (open_sub_closed P)

/--
@isnad1 id=eq.0h2v.s5.bbcab86ab2c5 from=translated src=- shape=5c642179 vocab=38725a38
-/
lemma open_closedHull_minus_boundary {n : ℕ} {P : Fin n → ℝ²} :
    closedHull P \ boundary P = openHull P := by
  simp [boundary, open_sub_closed]

/--
@isnad1 id=eq.0h2v.s5.79b31b9ab955 from=translated src=- shape=c2577e77 vocab=a6c3a527
-/
lemma boundary_constant {n : ℕ} {P : ℝ²} :
    boundary (fun (_ : Fin n) ↦ P) = ∅ := by
  unfold boundary
  rcases (ne_or_eq n 0) with hn | hz
  · rw [openHull_constant hn, closedHull_constant hn]
    simp only [sdiff_self, Set.bot_eq_empty]
  · unfold closedHull
    rw [hz, closedSimplex_zero_empty]
    simp only [univ_eq_empty, sum_empty, Set.image_empty, Set.empty_sdiff]

/--
@isnad1 id=eq.1h4v.s6.178ea3d8261f from=translated src=- shape=a7d7a3b4 vocab=3a79cb39
-/
lemma openHull_constant_rev {n : ℕ} {P : ℝ²} {f : Fin n → ℝ²}
    (ho : openHull f = {P}) : ∀ i, f i = P :=  by
  rcases eq_or_ne 0 n with hz | hn
  · intro i
    subst hz
    by_contra h
    unfold openHull at ho
    rw [openSimplex_zero_empty] at ho
    simp_all
  · by_contra hc; push Not at hc
    have hP : P ∈ openHull f := by
      rw [ho, Set.mem_singleton_iff]
    have ⟨i, hi⟩ := hc
    have this := closedHull_openHull_com hP (corner_in_closedHull (i := i) (P := f))
    rw [ho, Set.mem_singleton_iff, add_comm, ←eq_sub_iff_add_eq] at this
    nth_rw 1 [←(one_smul (M := ℝ) P), ←sub_smul] at this
    ring_nf at this
    simp_all

end Monsky
end LeanPool
