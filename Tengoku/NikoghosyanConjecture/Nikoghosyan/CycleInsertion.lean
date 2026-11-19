/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Tengoku.NikoghosyanConjecture.Nikoghosyan.CycleAssembly

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/canghaimeng/Nikoghosyan-conjecture@ccc8514d6801, `Nikoghosyan/CycleInsertion.lean`: removed 2 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-!
Elementary original-edge one-vertex cycle insertion.

Given an actual original path whose two distinct endpoints are original
neighbours of an outside vertex `x`, concatenate `x` at the start and
close by the original edge from the finish back to `x`. The result is a
genuine simple cycle of order at least three whose support is
`insert x p.support`.

This construction takes the path as input. It does not prove that such a
path exists, and it is not the manuscript one-vertex insertion corollary.
-/


open Classical
open Finset SimpleGraph

namespace Nikoghosyan

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}

namespace GraphPath

/--
@isnad1 id=le.1h3v.s5.66ce8ba00792 from=translated src=- shape=dc859b4b vocab=b2b3fe1a
-/
lemma two_le_card_support_of_ne_ends {p : GraphPath G}
    (hne : p.start ≠ p.finish) : 2 ≤ p.support.card := by
  have hnil : ¬ p.walk.Nil := fun h => hne (p.isPath.nil_iff_eq.1 h)
  have hpos : 0 < p.walk.length := by
    rw [Nat.pos_iff_ne_zero]
    intro h0
    exact hnil (Walk.length_eq_zero_iff.1 h0)
  have hcard := p.card_support
  omega

/--
@isnad1 id=le.2h4v.s6.3ec3ececa283 from=translated src=- shape=c22be15c vocab=f3c2e40b
-/
lemma three_le_card_insert_of_ne_ends {p : GraphPath G} {x : V}
    (hx : x ∉ p.support) (hne : p.start ≠ p.finish) :
    3 ≤ (insert x p.support).card := by
  have h2 := two_le_card_support_of_ne_ends hne
  have hcard : (insert x p.support).card = p.support.card + 1 :=
    card_insert_of_notMem hx
  omega

/-- Concatenate an outside vertex at the start of an original path and
close by the original edge from the finish to that vertex.-/
noncomputable def insertVertexCycle (p : GraphPath G) {x : V}
    (hs : G.Adj x p.start) (hf : G.Adj p.finish x)
    (hx : x ∉ p.support) (hne : p.start ≠ p.finish) : GraphCycle G :=
  (p.consAdj hs hx).toCycle hf (by
    simpa [support_consAdj] using three_le_card_insert_of_ne_ends hx hne)

/--
@isnad1 id=eq.4h4v.s6.c216e9e11959 from=translated src=- shape=a465e765 vocab=271d1765
-/
lemma support_insertVertexCycle (p : GraphPath G) {x : V}
    (hs : G.Adj x p.start) (hf : G.Adj p.finish x)
    (hx : x ∉ p.support) (hne : p.start ≠ p.finish) :
    (p.insertVertexCycle hs hf hx hne).support = insert x p.support := by
  simpa [insertVertexCycle, support_consAdj] using
    support_toCycle (p.consAdj hs hx) hf
      (by simpa [support_consAdj] using three_le_card_insert_of_ne_ends hx hne)

/--
@isnad1 id=le.4h4v.s6.3e5148071bee from=translated src=- shape=0aacda42 vocab=b897d0e2
-/
lemma three_le_card_support_insertVertexCycle (p : GraphPath G) {x : V}
    (hs : G.Adj x p.start) (hf : G.Adj p.finish x)
    (hx : x ∉ p.support) (hne : p.start ≠ p.finish) :
    3 ≤ (p.insertVertexCycle hs hf hx hne).support.card := by
  rw [support_insertVertexCycle]
  exact three_le_card_insert_of_ne_ends hx hne

/--
@isnad1 id=eq.4h4v.s6.d6432e47cc56 from=translated src=- shape=194116c0 vocab=050def00
-/
lemma card_support_insertVertexCycle (p : GraphPath G) {x : V}
    (hs : G.Adj x p.start) (hf : G.Adj p.finish x)
    (hx : x ∉ p.support) (hne : p.start ≠ p.finish) :
    (p.insertVertexCycle hs hf hx hne).support.card = p.support.card + 1 := by
  rw [support_insertVertexCycle, card_insert_of_notMem hx]

end GraphPath

/-- Existence form of the elementary insertion: an original path with
distinct endpoints adjacent to an outside vertex yields a genuine original
cycle through that vertex.
@isnad1 id=ex.4h4v.s7.bc62b564e963 from=translated src=- shape=07d682a6 vocab=d2c398cd
-/
theorem exists_graphCycle_insert (p : GraphPath G) {x : V}
    (hs : G.Adj x p.start) (hf : G.Adj p.finish x)
    (hx : x ∉ p.support) (hne : p.start ≠ p.finish) :
    ∃ c : GraphCycle G,
      c.support = insert x p.support ∧
        3 ≤ c.support.card ∧
        c.support.card = p.support.card + 1 :=
  ⟨p.insertVertexCycle hs hf hx hne,
    p.support_insertVertexCycle hs hf hx hne,
    p.three_le_card_support_insertVertexCycle hs hf hx hne,
    p.card_support_insertVertexCycle hs hf hx hne⟩

/-- If the input path spans `univ.erase x`, the inserted cycle is spanning.
@isnad1 id=ex.4h4v.s6.0a6edac8118c from=translated src=- shape=207ec05a vocab=5490b5f7
-/
theorem exists_spanning_graphCycle_insert (p : GraphPath G) {x : V}
    (hp : p.support = univ.erase x)
    (hs : G.Adj x p.start) (hf : G.Adj p.finish x)
    (hne : p.start ≠ p.finish) :
    ∃ c : GraphCycle G, c.support = univ := by
  have hx : x ∉ p.support := by simp [hp]
  obtain ⟨c, hc, _h3, _hcard⟩ := exists_graphCycle_insert p hs hf hx hne
  refine ⟨c, ?_⟩
  simpa [hp, insert_erase (mem_univ x)] using hc

end Nikoghosyan
