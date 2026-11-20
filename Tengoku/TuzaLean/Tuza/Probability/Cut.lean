import Tengoku.TuzaLean.Tuza.Basic.Graph
import Tengoku.TuzaLean.Tuza.Probability.Average

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
The random-cut cover selects W, noncrossing old edges, and each uncovered
triangle's new edges. When each triangle has at least two old edges, every
added edge is noncrossing.
-/

namespace Tuza

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An unoriented edge is noncrossing when its two colors agree.-/
def noncrossingEdge (χ : V → Bool) (e : Sym2 V) : Prop :=
  (Sym2.map χ e).IsDiag

instance (χ : V → Bool) : DecidablePred (noncrossingEdge χ) :=
  fun e => inferInstanceAs (Decidable (Sym2.map χ e).IsDiag)

omit [Fintype V] [DecidableEq V] in
/--
@isnad1 id=iff.0h4v.s4.7c748b6f18e2 from=translated src=- shape=ba6e02e7 vocab=0d84337b
-/
@[simp] theorem noncrossingEdge_pair (χ : V → Bool) (u v : V) :
    noncrossingEdge χ s(u, v) ↔ χ u = χ v := by
  simp [noncrossingEdge]

/-- The old edges selected before any uncovered triangles are considered.-/
def selectedOld (W O : Finset (Sym2 V)) (χ : V → Bool) : Finset (Sym2 V) :=
  W ∪ O.filter (noncrossingEdge χ)

/-- Add every non-old edge of every triangle that the selected old edges miss.
Using a union counts a repeated edge only once.-/
noncomputable def cutAddedEdges (A W O : Finset (Sym2 V)) (χ : V → Bool) :
    Finset (Sym2 V) :=
  (residual (trianglesOn A) (selectedOld W O χ)).biUnion (fun T => T \ O)

noncomputable def cutCover (A W O : Finset (Sym2 V)) (χ : V → Bool) :
    Finset (Sym2 V) := selectedOld W O χ ∪ cutAddedEdges A W O χ

/--
@isnad1 id=iff.0h6v.s7.7847118d315a from=translated src=- shape=e56d3668 vocab=374f0c33
-/
@[simp] theorem mem_cutAddedEdges {A W O : Finset (Sym2 V)} {χ : V → Bool}
    {e : Sym2 V} :
    e ∈ cutAddedEdges A W O χ ↔
      ∃ T ∈ residual (trianglesOn A) (selectedOld W O χ), e ∈ T \ O := by
  classical
  simp [cutAddedEdges]

omit [Fintype V] in
/-- Every triangle has a noncrossing edge under a Boolean vertex coloring.
@isnad1 id=ex.1h3v.s5.c0261275b50e from=translated src=- shape=ff143b75 vocab=14037358
-/
theorem IsTriangle.exists_noncrossing {T : Finset (Sym2 V)} (hT : IsTriangle T)
    (χ : V → Bool) : ∃ e ∈ T, noncrossingEdge χ e := by
  obtain ⟨u, v, w, huv, huw, hvw, rfl⟩ := hT
  have h : χ u = χ v ∨ χ u = χ w ∨ χ v = χ w := by
    cases χ u <;> cases χ v <;> cases χ w <;> decide
  rcases h with h | h | h
  · exact ⟨s(u, v), by simp, (noncrossingEdge_pair χ u v).mpr h⟩
  · exact ⟨s(u, w), by simp, (noncrossingEdge_pair χ u w).mpr h⟩
  · exact ⟨s(v, w), by simp, (noncrossingEdge_pair χ v w).mpr h⟩

omit [Fintype V] in
/--
@isnad1 id=le.1h4v.s5.c83ab4a77fb9 from=translated src=- shape=db861712 vocab=1914e9d5
-/
theorem selectedOld_subset_old {W O : Finset (Sym2 V)} (hW : W ⊆ O)
    (χ : V → Bool) : selectedOld W O χ ⊆ O := by
  exact union_subset hW (filter_subset _ _)

/-- A noncrossing edge of an uncovered triangle cannot be old.
@isnad1 id=not.3h7v.s6.dbccabddab0d from=translated src=- shape=8683de17 vocab=c198c30b
-/
theorem residual_noncrossing_not_old {A W O T : Finset (Sym2 V)} {χ : V → Bool}
    (hT : T ∈ residual (trianglesOn A) (selectedOld W O χ))
    {e : Sym2 V} (he : e ∈ T) (hNC : noncrossingEdge χ e) : e ∉ O := by
  intro heO
  exact disjoint_left.mp (mem_residual.mp hT).2 he
    (mem_union_right _ (mem_filter.mpr ⟨heO, hNC⟩))

/--
@isnad1 id=nonempty.1h6v.s6.948416df18f0 from=translated src=- shape=726bfb53 vocab=fed49d62
-/
theorem residual_new_edges_nonempty {A W O T : Finset (Sym2 V)} {χ : V → Bool}
    (hT : T ∈ residual (trianglesOn A) (selectedOld W O χ)) :
    (T \ O).Nonempty := by
  have htri := (mem_trianglesOn.mp (mem_residual.mp hT).1).1
  obtain ⟨e, he, hNC⟩ := htri.exists_noncrossing χ
  exact ⟨e, mem_sdiff.mpr ⟨he, residual_noncrossing_not_old hT he hNC⟩⟩

/-- The selected old edges and the uncovered triangles' new edges cover every triangle.
@isnad1 id=iscover.0h5v.s5.4db672b11fd5 from=translated src=- shape=1d023790 vocab=2a241038
-/
theorem cutCover_covers (A W O : Finset (Sym2 V)) (χ : V → Bool) :
    IsCover (trianglesOn A) (cutCover A W O χ) := by
  apply cover_union_residual
  intro T hT
  obtain ⟨e, he⟩ := residual_new_edges_nonempty hT
  exact ⟨e, mem_inter.mpr ⟨(mem_sdiff.mp he).1,
    mem_cutAddedEdges.mpr ⟨T, hT, he⟩⟩⟩

/--
@isnad1 id=le.0h5v.s6.58dc24ea1297 from=translated src=- shape=e1f0eb15 vocab=1c757c3e
-/
theorem cutAddedEdges_subset {A W O : Finset (Sym2 V)} (χ : V → Bool) :
    cutAddedEdges A W O χ ⊆ A \ O := by
  intro e he
  obtain ⟨T, hT, heT⟩ := mem_cutAddedEdges.mp he
  obtain ⟨heT, heO⟩ := mem_sdiff.mp heT
  exact mem_sdiff.mpr
    ⟨(mem_trianglesOn.mp (mem_residual.mp hT).1).2 heT, heO⟩

/--
@isnad1 id=le.2h5v.s6.38c01a7b7689 from=translated src=- shape=83619dbf vocab=2eea3ec8
-/
theorem cutCover_subset {A W O : Finset (Sym2 V)}
    (hW : W ⊆ O) (hO : O ⊆ A) (χ : V → Bool) :
    cutCover A W O χ ⊆ A := by
  exact union_subset ((selectedOld_subset_old hW χ).trans hO)
    ((cutAddedEdges_subset χ).trans sdiff_subset)

/-- There is only one possible new edge in a triangle with at least two old
edges, so every added edge equals its noncrossing edge.
@isnad1 id=noncross.2h6v.s6.5e3eef54e8c7 from=translated src=- shape=5c675e1b vocab=5ee5879f
-/
theorem cutAddedEdges_noncrossing {A W O : Finset (Sym2 V)}
    (hOld : ∀ T ∈ trianglesOn A, 2 ≤ (T ∩ O).card) (χ : V → Bool)
    {e : Sym2 V} (he : e ∈ cutAddedEdges A W O χ) : noncrossingEdge χ e := by
  obtain ⟨T, hT, heT⟩ := mem_cutAddedEdges.mp he
  have ht := (mem_residual.mp hT).1
  have htri := (mem_trianglesOn.mp ht).1
  obtain ⟨f, hf, hNC⟩ := htri.exists_noncrossing χ
  have hfnew : f ∈ T \ O :=
    mem_sdiff.mpr ⟨hf, residual_noncrossing_not_old hT hf hNC⟩
  have hcard : (T \ O).card ≤ 1 := by
    have hs := card_sdiff_add_card_inter T O
    have htcard := trianglesOn_card ht
    have ho := hOld T ht
    omega
  have hef : e = f := (card_le_one.mp hcard) e heT f hfnew
  exact hef ▸ hNC

/--
@isnad1 id=le.1h6v.s7.d7bbb1e56c09 from=translated src=- shape=1459f764 vocab=c3222060
-/
theorem cutAddedEdges_inter_subset_noncrossing {A W O : Finset (Sym2 V)}
    (hOld : ∀ T ∈ trianglesOn A, 2 ≤ (T ∩ O).card)
    (N : Finset (Sym2 V)) (χ : V → Bool) :
    cutAddedEdges A W O χ ∩ N ⊆ N.filter (noncrossingEdge χ) := by
  intro e he
  obtain ⟨heAdd, heN⟩ := mem_inter.mp he
  exact mem_filter.mpr ⟨heN, cutAddedEdges_noncrossing hOld χ heAdd⟩

omit [Fintype V] in
/--
@isnad1 id=eq.0h4v.s6.ed6de2ea7a6c from=translated src=- shape=e6880cfe vocab=5cf56978
-/
theorem selectedOld_eq_union_sdiff (W O : Finset (Sym2 V)) (χ : V → Bool) :
    selectedOld W O χ = W ∪ (O \ W).filter (noncrossingEdge χ) := by
  ext e
  simp only [selectedOld, mem_union, mem_filter, mem_sdiff]
  tauto

omit [Fintype V] in
/--
@isnad1 id=eq.0h4v.s6.118c64f1baee from=translated src=- shape=c3761614 vocab=70f10434
-/
theorem selectedOld_card (W O : Finset (Sym2 V)) (χ : V → Bool) :
    (selectedOld W O χ).card = W.card + ((O \ W).filter (noncrossingEdge χ)).card := by
  rw [selectedOld_eq_union_sdiff, card_union_of_disjoint]
  apply disjoint_left.mpr
  intro e heW heF
  exact (mem_sdiff.mp (mem_filter.mp heF).1).2 heW

/-- The pointwise cover cost, separating added edges inside and outside `N`.
@isnad1 id=le.1h6v.s7.e6ec70c7630b from=translated src=- shape=b430e054 vocab=6a2a6dd9
-/
theorem cutCover_card_le {A W O : Finset (Sym2 V)}
    (hOld : ∀ T ∈ trianglesOn A, 2 ≤ (T ∩ O).card)
    (N : Finset (Sym2 V)) (χ : V → Bool) :
    (cutCover A W O χ).card ≤ W.card +
      ((O \ W).filter (noncrossingEdge χ)).card +
      (N.filter (noncrossingEdge χ)).card + (cutAddedEdges A W O χ \ N).card := by
  have hi := card_le_card (cutAddedEdges_inter_subset_noncrossing (W := W) hOld N χ)
  have hs := card_inter_add_card_sdiff (cutAddedEdges A W O χ) N
  have hu := card_union_le (selectedOld W O χ) (cutAddedEdges A W O χ)
  rw [selectedOld_card] at hu
  change (selectedOld W O χ ∪ cutAddedEdges A W O χ).card ≤ _
  omega

/-- The same pointwise inequality in the indicator form consumed by finite
average linearity.
@isnad1 id=le.1h6v.s7.221fb5826aa3 from=translated src=- shape=65c1bf70 vocab=4a681cfb
-/
theorem cutCover_charge_le {A W O : Finset (Sym2 V)}
    (hOld : ∀ T ∈ trianglesOn A, 2 ≤ (T ∩ O).card)
    (N : Finset (Sym2 V)) (χ : V → Bool) :
    ((cutCover A W O χ).card : ℚ) ≤ (W.card : ℚ) +
      (∑ e ∈ O \ W, if noncrossingEdge χ e then (1 : ℚ) else 0) +
      (∑ e ∈ N, if noncrossingEdge χ e then (1 : ℚ) else 0) +
      ((cutAddedEdges A W O χ \ N).card : ℚ) := by
  simp only [sum_boole]
  exact_mod_cast cutCover_card_le hOld N χ

end Tuza
