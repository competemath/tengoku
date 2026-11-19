/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Tengoku.NikoghosyanConjecture.Nikoghosyan.PathRotation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/canghaimeng/Nikoghosyan-conjecture@ccc8514d6801, `Nikoghosyan/CycleSwitches.lean`: removed 2 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-!
Same-sign original-run switches.

`switchStarts` joins two vertex-disjoint original paths at their starts by
an original edge, producing one path from the first finish to the second
finish. `switchEnds` is the symmetric operation at finishes. Exact
undirected edge identities are recorded; no edge outside `G` is used.

Cycle helpers `rotateTo`, `succAt`, and `rotateTo_eq_cons` open a
prescribed original cycle at a vertex and expose its successor dart.
G2 applies `switchStarts` / `switchEnds` to actual leftover runs once
those runs and the adjacent-start (or adjacent-end) hypothesis are
constructed. The adjacent-start hypothesis is an input.

This module does not construct leftover runs of `C - A` from a profile,
does not prove protected-path existence, and does not close
`prof:thm:protected`.
-/


open Classical
open Finset Function SimpleGraph

namespace Nikoghosyan

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}

namespace GraphPath

/-- Join two vertex-disjoint original paths at their starts by an original
edge. The result runs from the first finish to the second finish.-/
def switchStarts (p q : GraphPath G) (h : G.Adj p.start q.start)
    (hd : Disjoint p.support q.support) : GraphPath G :=
  p.reverse.splice q h (by simpa [support_reverse] using hd)

/--
@isnad1 id=eq.2h4v.s6.beae21d18cc9 from=translated src=- shape=82847fc6 vocab=966cbfba
-/
lemma switchStarts_start (p q : GraphPath G) (h : G.Adj p.start q.start)
    (hd : Disjoint p.support q.support) :
    (switchStarts p q h hd).start = p.finish :=
  rfl

/--
@isnad1 id=eq.2h4v.s6.49a280e97a1e from=translated src=- shape=fbfa60cc vocab=966cbfba
-/
lemma switchStarts_finish (p q : GraphPath G) (h : G.Adj p.start q.start)
    (hd : Disjoint p.support q.support) :
    (switchStarts p q h hd).finish = q.finish :=
  rfl

/--
@isnad1 id=eq.2h4v.s6.f645b345be55 from=translated src=- shape=bce8f99b vocab=0594c4e1
-/
lemma switchStarts_support (p q : GraphPath G) (h : G.Adj p.start q.start)
    (hd : Disjoint p.support q.support) :
    (switchStarts p q h hd).support = p.support ∪ q.support := by
  simp [switchStarts, splice, reverse, GraphPath.support, Walk.support_append,
    Walk.support_cons, Walk.support_reverse, List.toFinset_reverse, union_comm]

/--
@isnad1 id=eq.2h4v.s7.b237b1f2592e from=translated src=- shape=26dab350 vocab=c29eaf28
-/
theorem switchStarts_edges (p q : GraphPath G) (h : G.Adj p.start q.start)
    (hd : Disjoint p.support q.support) :
    (switchStarts p q h hd).edges = p.edges ∪ q.edges ∪ {s(p.start, q.start)} := by
  have hrev : p.walk.reverse.edges.toFinset = p.edges := by
    simp [edges, Walk.edges_reverse, List.toFinset_reverse]
  simp [edges, switchStarts, splice, reverse, Walk.edges_append, Walk.edges_cons,
    List.toFinset_append, List.toFinset_cons, hrev, union_comm, union_left_comm,
    union_assoc]

/-- Join two vertex-disjoint original paths at their finishes by an original
edge. The result runs from the first start to the second start.-/
def switchEnds (p q : GraphPath G) (h : G.Adj p.finish q.finish)
    (hd : Disjoint p.support q.support) : GraphPath G :=
  switchStarts p.reverse q.reverse (by simpa [reverse] using h)
    (by simpa [support_reverse] using hd)

/--
@isnad1 id=eq.2h4v.s6.8dd3c9b56bb5 from=translated src=- shape=04318f9b vocab=8a9ff246
-/
lemma switchEnds_start (p q : GraphPath G) (h : G.Adj p.finish q.finish)
    (hd : Disjoint p.support q.support) :
    (switchEnds p q h hd).start = p.start := by
  simp [switchEnds, switchStarts_start, reverse]

/--
@isnad1 id=eq.2h4v.s6.ea39fa438d07 from=translated src=- shape=e599e152 vocab=8a9ff246
-/
lemma switchEnds_finish (p q : GraphPath G) (h : G.Adj p.finish q.finish)
    (hd : Disjoint p.support q.support) :
    (switchEnds p q h hd).finish = q.start := by
  simp [switchEnds, switchStarts_finish, reverse]

/--
@isnad1 id=eq.2h4v.s6.a4c959cdee98 from=translated src=- shape=bce8f99b vocab=b0fb350e
-/
lemma switchEnds_support (p q : GraphPath G) (h : G.Adj p.finish q.finish)
    (hd : Disjoint p.support q.support) :
    (switchEnds p q h hd).support = p.support ∪ q.support := by
  simpa [switchEnds, support_reverse] using
    switchStarts_support p.reverse q.reverse (by simpa [reverse] using h)
      (by simpa [support_reverse] using hd)

/--
@isnad1 id=eq.2h4v.s7.bf5fb83f7cd8 from=translated src=- shape=26dab350 vocab=a8fa10af
-/
theorem switchEnds_edges (p q : GraphPath G) (h : G.Adj p.finish q.finish)
    (hd : Disjoint p.support q.support) :
    (switchEnds p q h hd).edges = p.edges ∪ q.edges ∪ {s(p.finish, q.finish)} := by
  have hrevp : p.reverse.edges = p.edges := by
    simp [edges, reverse, Walk.edges_reverse, List.toFinset_reverse]
  have hrevq : q.reverse.edges = q.edges := by
    simp [edges, reverse, Walk.edges_reverse, List.toFinset_reverse]
  rw [switchEnds, switchStarts_edges, hrevp, hrevq]
  simp [reverse]

/-- The new joining edge of a start-switch meets no vertex of a designated
set `A` that contains neither start. The two run edge-sets do not include
the host-cycle seams that G2 deletes when assembling a spanning path.
@isnad1 id=eq.4h5v.s7.c1e22ce01a2d from=translated src=- shape=71237efd vocab=f525cf18
-/
theorem switchStarts_AIncident (p q : GraphPath G) (h : G.Adj p.start q.start)
    (hd : Disjoint p.support q.support) {A : Finset V}
    (hp : p.start ∉ A) (hq : q.start ∉ A) :
    (switchStarts p q h hd).AIncident A = p.AIncident A ∪ q.AIncident A := by
  ext e
  simp only [mem_AIncident_iff, switchStarts_edges, mem_union, mem_singleton]
  constructor
  · rintro ⟨hmem, ⟨b, hbA, hbe⟩⟩
    rcases hmem with (h | h) | rfl
    · exact Or.inl ⟨h, ⟨b, hbA, hbe⟩⟩
    · exact Or.inr ⟨h, ⟨b, hbA, hbe⟩⟩
    · rcases Sym2.mem_iff.mp hbe with hb | hb
      · exact (hp (hb ▸ hbA)).elim
      · exact (hq (hb ▸ hbA)).elim
  · rintro (⟨he, hA⟩ | ⟨he, hA⟩)
    · exact ⟨Or.inl (Or.inl he), hA⟩
    · exact ⟨Or.inl (Or.inr he), hA⟩

/--
@isnad1 id=eq.4h5v.s7.568a059b7ac8 from=translated src=- shape=71237efd vocab=ce96e984
-/
theorem switchEnds_AIncident (p q : GraphPath G) (h : G.Adj p.finish q.finish)
    (hd : Disjoint p.support q.support) {A : Finset V}
    (hp : p.finish ∉ A) (hq : q.finish ∉ A) :
    (switchEnds p q h hd).AIncident A = p.AIncident A ∪ q.AIncident A := by
  have hp' : p.reverse.start ∉ A := by simpa [reverse] using hp
  have hq' : q.reverse.start ∉ A := by simpa [reverse] using hq
  have hrevp : p.reverse.AIncident A = p.AIncident A := by
    simp [AIncident, edges, reverse, Walk.edges_reverse, List.toFinset_reverse]
  have hrevq : q.reverse.AIncident A = q.AIncident A := by
    simp [AIncident, edges, reverse, Walk.edges_reverse, List.toFinset_reverse]
  simpa [switchEnds, hrevp, hrevq] using
    switchStarts_AIncident p.reverse q.reverse (by simpa [reverse] using h)
      (by simpa [support_reverse] using hd) hp' hq'

end GraphPath

namespace GraphCycle

/--
@isnad1 id=mem.1h4v.s5.8a715609affa from=translated src=- shape=a1a3b8c7 vocab=ebad12df
-/
lemma mem_walk_support_of_mem {c : GraphCycle G} {u : V}
    (hu : u ∈ c.support) : u ∈ c.walk.support :=
  List.mem_toFinset.mp (by simpa [support] using hu)

/-- Rotate a cycle so that it starts at a prescribed original vertex.-/
def rotateTo (c : GraphCycle G) {u : V} (hu : u ∈ c.support) : GraphCycle G where
  start := u
  walk := c.walk.rotate u (mem_walk_support_of_mem hu)
  isCycle := (Walk.isCycle_rotate (mem_walk_support_of_mem hu)).mpr c.isCycle

/--
@isnad1 id=eq.1h4v.s5.513cb80f31fd from=translated src=- shape=941d0d9c vocab=72488a2b
-/
lemma support_rotateTo (c : GraphCycle G) {u : V} (hu : u ∈ c.support) :
    (c.rotateTo hu).support = c.support := by
  ext x
  simp only [rotateTo, support, List.mem_toFinset]
  exact Walk.mem_support_rotate_iff (w := x) c.walk u (mem_walk_support_of_mem hu)

/--
@isnad1 id=eq.1h4v.s5.d084e80f7e71 from=translated src=- shape=6616a1e9 vocab=c4c600be
-/
lemma start_rotateTo (c : GraphCycle G) {u : V} (hu : u ∈ c.support) :
    (c.rotateTo hu).start = u :=
  rfl

/--
@isnad1 id=eq.1h4v.s6.d5a9b55b551c from=translated src=- shape=6b60c330 vocab=ea48f083
-/
lemma edges_rotateTo (c : GraphCycle G) {u : V} (hu : u ∈ c.support) :
    (c.rotateTo hu).walk.edges.toFinset = c.walk.edges.toFinset := by
  ext e
  simp [rotateTo, List.mem_toFinset]
  exact (c.walk.rotate_edges u (mem_walk_support_of_mem hu)).perm.mem_iff

/-- The original cycle successor of `u` along the rotated walk.-/
def succAt (c : GraphCycle G) {u : V} (hu : u ∈ c.support) : V :=
  (c.rotateTo hu).walk.getVert 1

/--
@isnad1 id=adj.1h4v.s5.8ce2619b0578 from=translated src=- shape=e1beeda5 vocab=03fd11ca
-/
lemma adj_succAt (c : GraphCycle G) {u : V} (hu : u ∈ c.support) :
    G.Adj u (c.succAt hu) := by
  have hpos : 0 < (c.rotateTo hu).walk.length := by
    simpa [rotateTo, Walk.length_rotate] using
      (lt_of_lt_of_le (by decide : (0 : ℕ) < 3) c.three_le_length)
  simpa [succAt, rotateTo, Walk.getVert_zero] using
    (c.rotateTo hu).walk.adj_getVert_succ hpos

/--
@isnad1 id=mem.1h4v.s5.a7dbba601609 from=translated src=- shape=366a6fa9 vocab=a8391780
-/
lemma succAt_mem_support (c : GraphCycle G) {u : V} (hu : u ∈ c.support) :
    c.succAt hu ∈ c.support := by
  have : c.succAt hu ∈ (c.rotateTo hu).support := by
    simp [succAt, support, List.mem_toFinset, Walk.getVert_mem_support]
  simpa [support_rotateTo] using this

/--
@isnad1 id=ne.1h4v.s5.cd13d61b856a from=translated src=- shape=7570d83f vocab=a8391780
-/
lemma succAt_ne (c : GraphCycle G) {u : V} (hu : u ∈ c.support) :
    c.succAt hu ≠ u :=
  (c.adj_succAt hu).ne.symm

/--
@isnad1 id=ex.1h4v.s7.42e84a264eda from=translated src=- shape=f3663687 vocab=06f818cb
-/
lemma rotateTo_eq_cons (c : GraphCycle G) {u : V} (hu : u ∈ c.support) :
    ∃ (w : V) (rest : G.Walk w (c.rotateTo hu).start)
      (h : G.Adj (c.rotateTo hu).start w),
      w = c.succAt hu ∧ (c.rotateTo hu).walk = Walk.cons h rest ∧ rest.IsPath := by
  have hnil : ¬ (c.rotateTo hu).walk.Nil := (c.rotateTo hu).isCycle.not_nil
  obtain ⟨w, hadj, rest, hcons⟩ := (Walk.not_nil_iff).1 hnil
  refine ⟨w, rest, hadj, ?_, hcons, ?_⟩
  · change w = (c.rotateTo hu).walk.getVert 1
    rw [hcons]
    simp [Walk.getVert_cons_succ, Walk.getVert_zero]
  · exact ((Walk.cons_isCycle_iff rest hadj).1
      (by simpa [hcons] using (c.rotateTo hu).isCycle)).1

end GraphCycle
end Nikoghosyan
