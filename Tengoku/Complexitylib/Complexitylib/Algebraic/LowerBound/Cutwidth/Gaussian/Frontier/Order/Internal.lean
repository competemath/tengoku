/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Frontier.Order.Defs
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Gaussian.Edge.Defs
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition

/-!
# Path decompositions from edge scores: proofs

A cubic vertex has three incident edges. If a threshold has incident edges on both sides,
one side holds one edge and the other two, so four ordered pairs of distinct incident edges
are separated by the threshold.

For the decomposition, list the edges in nondecreasing score order and let bag `k` hold the
vertices with an incident edge at a position at most `k` and another at a position at least
`k`. With `t` the score of the `k`-th edge, every vertex of bag `k` has an edge scoring at
most `t` and an edge scoring at least `t`. If `t` lies below the grid or above it, the
vertex is an endpoint of a tail edge. Otherwise `a + i δ ≤ t < a + (i + 1) δ` for some
`i < M`, and the vertex straddles `a + i δ` or is an endpoint of an edge in the window
`[a + i δ, a + (i + 1) δ)`.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Gaussian.Internal

variable {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]

open scoped Classical in
/-- Three reals on both sides of a threshold give four ordered separated pairs. -/
theorem four_le_between_pairs {t p q r : ℝ} (hlt : p < t ∨ q < t ∨ r < t)
    (hge : t ≤ p ∨ t ≤ q ∨ t ≤ r) :
    (4 : ℝ) ≤ ((if Between t p q then 1 else 0) + (if Between t p r then 1 else 0)) +
      (((if Between t q p then 1 else 0) + (if Between t q r then 1 else 0)) +
        ((if Between t r p then 1 else 0) + (if Between t r q then 1 else 0))) := by
  rcases lt_or_ge p t with hp | hp <;> rcases lt_or_ge q t with hq | hq <;>
    rcases lt_or_ge r t with hr | hr <;>
    simp [Between, hp, hq, hr, not_le.mpr, not_lt.mpr] <;> norm_num <;>
    rcases hlt with h | h | h <;> rcases hge with h' | h' | h' <;> linarith

/-- The edges at `v` are the edges of the graph containing `v`. -/
theorem mem_incidenceFinset_iff {v : W} {e : Sym2 W} :
    e ∈ H.incidenceFinset v ↔ e ∈ H.edgeFinset ∧ v ∈ e := by
  rw [SimpleGraph.incidenceFinset_eq_filter, Finset.mem_filter]

/-- A set of edges has at most two endpoints per edge. -/
theorem card_filter_exists_mem_le (F : Finset (Sym2 W)) :
    (Finset.univ.filter fun v => ∃ e ∈ F, v ∈ e).card ≤ 2 * F.card := by
  have hsub : (Finset.univ.filter fun v => ∃ e ∈ F, v ∈ e) ⊆
      F.biUnion fun e => Finset.univ.filter fun v => v ∈ e := by
    intro v hv
    simpa using hv
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  calc ∑ e ∈ F, (Finset.univ.filter fun v => v ∈ e).card ≤ ∑ _e ∈ F, 2 :=
        Finset.sum_le_sum fun e _ => ?_
    _ = 2 * F.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  induction e using Sym2.ind with
  | h x y =>
    refine (Finset.card_le_card fun w hw => ?_).trans (Finset.card_le_two (a := x) (b := y))
    simpa using hw

open scoped Classical in
/-- Below `a`: a vertex with an edge scoring at most `t < a` is an endpoint of an edge scoring
below `a`. -/
theorem card_filter_edgeScore_le_of_lt (score : Sym2 W → ℝ) {a t : ℝ} (ht : t < a) :
    ((Finset.univ.filter fun v => (∃ e ∈ H.edgeFinset, v ∈ e ∧ score e ≤ t) ∧
      ∃ e ∈ H.edgeFinset, v ∈ e ∧ t ≤ score e).card : ℝ) ≤
      2 * ((H.edgeFinset.filter fun e => score e < a).card : ℝ) := by
  have hsub : (Finset.univ.filter fun v => (∃ e ∈ H.edgeFinset, v ∈ e ∧ score e ≤ t) ∧
      ∃ e ∈ H.edgeFinset, v ∈ e ∧ t ≤ score e) ⊆
      Finset.univ.filter fun v => ∃ e ∈ H.edgeFinset.filter fun e => score e < a, v ∈ e := by
    intro v hv
    obtain ⟨⟨e, he, hv, hle⟩, -⟩ := (Finset.mem_filter.mp hv).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, e,
      Finset.mem_filter.mpr ⟨he, hle.trans_lt ht⟩, hv⟩
  exact_mod_cast (Finset.card_le_card hsub).trans (card_filter_exists_mem_le _)

open scoped Classical in
/-- At or above `b`: a vertex with an edge scoring at least `t ≥ b` is an endpoint of an edge
scoring at least `b`. -/
theorem card_filter_edgeScore_le_of_ge (score : Sym2 W → ℝ) {b t : ℝ} (ht : b ≤ t) :
    ((Finset.univ.filter fun v => (∃ e ∈ H.edgeFinset, v ∈ e ∧ score e ≤ t) ∧
      ∃ e ∈ H.edgeFinset, v ∈ e ∧ t ≤ score e).card : ℝ) ≤
      2 * ((H.edgeFinset.filter fun e => b ≤ score e).card : ℝ) := by
  have hsub : (Finset.univ.filter fun v => (∃ e ∈ H.edgeFinset, v ∈ e ∧ score e ≤ t) ∧
      ∃ e ∈ H.edgeFinset, v ∈ e ∧ t ≤ score e) ⊆
      Finset.univ.filter fun v => ∃ e ∈ H.edgeFinset.filter fun e => b ≤ score e, v ∈ e := by
    intro v hv
    obtain ⟨-, e, he, hv, hle⟩ := (Finset.mem_filter.mp hv).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, e,
      Finset.mem_filter.mpr ⟨he, ht.trans hle⟩, hv⟩
  exact_mod_cast (Finset.card_le_card hsub).trans (card_filter_exists_mem_le _)

open scoped Classical in
/-- **Score-order path decomposition.** List the edges of a cubic graph in nondecreasing score
order and let bag `k` hold the vertices with an incident edge at a position at most `k` and
another at a position at least `k`. Each bag lies inside the vertices with an edge scoring at
most `t` and an edge scoring at least `t`, where `t` is the score of the `k`-th edge. -/
theorem exists_pathDecomposition_subset_edgeScore (regular : H.IsRegularOfDegree 3)
    (score : Sym2 W → ℝ) :
    ∃ D : PathDecomposition H, ∀ k, ∃ t : ℝ, D.bag k ⊆ Finset.univ.filter fun v =>
      (∃ e ∈ H.edgeFinset, v ∈ e ∧ score e ≤ t) ∧ ∃ e ∈ H.edgeFinset, v ∈ e ∧ t ≤ score e := by
  -- List the edges in nondecreasing score order.
  set l := H.edgeFinset.toList.mergeSort fun e e' => decide (score e ≤ score e') with hl
  have mem_l : ∀ e, e ∈ l ↔ e ∈ H.edgeFinset := fun e => by
    rw [hl, (List.mergeSort_perm _ _).mem_iff, Finset.mem_toList]
  have sorted : l.Pairwise fun e e' => decide (score e ≤ score e') :=
    List.pairwise_mergeSort (fun _ _ _ h₁ h₂ => by simp at h₁ h₂ ⊢; linarith)
      (fun e e' => by simpa using le_total _ _) _
  have mono : ∀ i j : Fin l.length, i ≤ j → score l[i] ≤ score l[j] := by
    intro i j hij
    rcases hij.lt_or_eq with hlt | rfl
    · simpa using List.pairwise_iff_getElem.mp sorted i j i.2 j.2 hlt
    · exact le_rfl
  have index : ∀ e ∈ H.edgeFinset, ∃ i : Fin l.length, l[i] = e := fun e he => by
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ((mem_l e).mpr he)
    exact ⟨⟨i, hi⟩, rfl⟩
  refine ⟨{ length := l.length
            bag := fun k => Finset.univ.filter fun v =>
              ∃ i j : Fin l.length, i ≤ k ∧ k ≤ j ∧ v ∈ l[i] ∧ v ∈ l[j]
            vertex_mem := ?_
            edge_mem := ?_
            consecutive := ?_ }, ?_⟩
  · intro v
    have hpos : 0 < (H.incidenceFinset v).card := by
      rw [H.card_incidenceFinset_eq_degree, regular v]; norm_num
    obtain ⟨e, he⟩ := Finset.card_pos.mp hpos
    obtain ⟨he, hv⟩ := (mem_incidenceFinset_iff H).mp he
    obtain ⟨i, rfl⟩ := index e he
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, i, i, le_rfl, le_rfl, hv, hv⟩⟩
  · intro u v huv
    obtain ⟨i, hi⟩ := index s(u, v) (SimpleGraph.mem_edgeFinset.mpr huv)
    refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, i, i, le_rfl, le_rfl, ?_, ?_⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, i, i, le_rfl, le_rfl, ?_, ?_⟩⟩ <;>
      simp [hi]
  · intro v i j k hij hjk hi hk
    obtain ⟨i₁, -, hi₁, -, hv₁, -⟩ := (Finset.mem_filter.mp hi).2
    obtain ⟨-, j₂, -, hj₂, -, hv₂⟩ := (Finset.mem_filter.mp hk).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, i₁, j₂, hi₁.trans hij, hjk.trans hj₂,
      hv₁, hv₂⟩
  · intro k
    refine ⟨score l[k], fun v hv => ?_⟩
    obtain ⟨i, j, hik, hkj, hvi, hvj⟩ := (Finset.mem_filter.mp hv).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨l[i], (mem_l _).mp (List.getElem_mem _), hvi, mono i k hik⟩,
      l[j], (mem_l _).mp (List.getElem_mem _), hvj, mono k j hkj⟩

end Algebraic.Cutwidth.Gaussian.Internal
