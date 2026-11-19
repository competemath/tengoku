/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Tengoku.NikoghosyanConjecture.Nikoghosyan.PathIncidences
import Tengoku.NikoghosyanConjecture.Nikoghosyan.CycleSwitches

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/canghaimeng/Nikoghosyan-conjecture@ccc8514d6801, `Nikoghosyan/CycleIncidences.lean`: removed 2 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-!
Exact original walk-edge incidences of a genuine simple cycle, and the
2/1 protection bridge.

Rotate a cycle to a vertex `v`, drop the first original dart, and read
the remaining simple path: the dropped dart is the successor edge, the
last dart of the remainder is the predecessor. Every vertex of a genuine
cycle of order at least three is incident to exactly those two cycle
edges. Ambient `G.degree` is never used.

If a spanning original path of the same support is `ProtectedAt c A`,
each internal vertex of `A` has path-incident edges exactly equal to the
two cycle edges, and each endpoint of `A` has exactly one prescribed
cycle edge. Path support of size at least three is inherited from the
genuine cycle.

Composing prefix rotation with this bridge retains original-`A`
internal-2 / endpoint-1 counts. The new start `a` is an endpoint and
loses one old cycle edge; every other `A`-incidence is unchanged.
Protection is asserted only at the original set `A`.
-/


open Classical
open Finset Function SimpleGraph

namespace Nikoghosyan

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}

namespace GraphCycle

/-- Undirected original edges of a genuine simple cycle.-/
def edges (c : GraphCycle G) : Finset (Sym2 V) :=
  c.walk.edges.toFinset

/--
@isnad1 id=iff.0h4v.s6.c094e045d9ca from=translated src=- shape=235ddb0e vocab=29ec9c78
-/
lemma mem_edges_iff {c : GraphCycle G} {e : Sym2 V} :
    e ∈ c.edges ↔ e ∈ c.walk.edges := by
  simp [edges]

/--
@isnad1 id=eq.0h3v.s5.801160cf05fb from=translated src=- shape=882ea3f8 vocab=8348cf98
-/
lemma edges_reverse (c : GraphCycle G) : c.reverse.edges = c.edges := by
  simp [edges, reverse, Walk.edges_reverse, List.toFinset_reverse]

/--
@isnad1 id=eq.1h4v.s5.a2295ddd4eef from=translated src=- shape=30115ee0 vocab=e82d520b
-/
lemma edges_rotateTo_eq (c : GraphCycle G) {u : V} (hu : u ∈ c.support) :
    (c.rotateTo hu).edges = c.edges :=
  c.edges_rotateTo hu

/-- Cycle edges incident to a designated original vertex.-/
def incidentEdges (c : GraphCycle G) (v : V) : Finset (Sym2 V) :=
  c.edges.filter fun e => v ∈ e

/--
@isnad1 id=iff.0h5v.s6.ab39496fd312 from=translated src=- shape=03ff94c4 vocab=45c80057
-/
lemma mem_incidentEdges_iff {c : GraphCycle G} {v : V} {e : Sym2 V} :
    e ∈ c.incidentEdges v ↔ e ∈ c.edges ∧ v ∈ e := by
  simp [incidentEdges]

/--
@isnad1 id=eq.1h5v.s5.9da8e75b955c from=translated src=- shape=71151d36 vocab=819ecd5a
-/
lemma incidentEdges_rotateTo (c : GraphCycle G) {u : V} (hu : u ∈ c.support)
    (v : V) : (c.rotateTo hu).incidentEdges v = c.incidentEdges v := by
  simp [incidentEdges, c.edges_rotateTo_eq hu]

/--
@isnad1 id=eq.0h4v.s5.c0963d78fa8d from=translated src=- shape=b00cd2e7 vocab=869499b0
-/
lemma incidentEdges_reverse (c : GraphCycle G) (v : V) :
    c.reverse.incidentEdges v = c.incidentEdges v := by
  simp [incidentEdges, c.edges_reverse]

/--
@isnad1 id=not.1h4v.s6.d63604d5527e from=translated src=- shape=cd361067 vocab=a17d50ce
-/
lemma rotateTo_not_nil (c : GraphCycle G) {u : V} (hu : u ∈ c.support) :
    ¬ (c.rotateTo hu).walk.Nil :=
  (c.rotateTo hu).isCycle.not_nil

/--
@isnad1 id=eq.1h4v.s6.32cd7d471449 from=translated src=- shape=80796052 vocab=7a5f08c9
-/
lemma succAt_eq_snd (c : GraphCycle G) {u : V} (hu : u ∈ c.support) :
    c.succAt hu = (c.rotateTo hu).walk.snd :=
  rfl

/-- The simple original path obtained by rotating `c` to `u` and deleting
the first dart. Start is the successor of `u`; finish is `u`. Cyclic
indices `0` and `length` name the same vertex; the remainder uses the
strict tail.-/
def openAt (c : GraphCycle G) {u : V} (hu : u ∈ c.support) : GraphPath G where
  start := c.succAt hu
  finish := u
  walk := (c.rotateTo hu).walk.tail
  isPath := (c.rotateTo hu).isCycle.isPath_tail

/--
@isnad1 id=eq.1h4v.s5.701df55ed0f3 from=translated src=- shape=faf5d93b vocab=7238267f
-/
lemma openAt_start (c : GraphCycle G) {u : V} (hu : u ∈ c.support) :
    (c.openAt hu).start = c.succAt hu :=
  rfl

/--
@isnad1 id=eq.1h4v.s5.b7bad3920b3f from=translated src=- shape=6616a1e9 vocab=a8d99489
-/
lemma openAt_finish (c : GraphCycle G) {u : V} (hu : u ∈ c.support) :
    (c.openAt hu).finish = u :=
  rfl

/--
@isnad1 id=ne.1h4v.s5.96f0afea46ac from=translated src=- shape=5cde55e5 vocab=e23e32ca
-/
lemma openAt_start_ne_finish (c : GraphCycle G) {u : V} (hu : u ∈ c.support) :
    (c.openAt hu).start ≠ (c.openAt hu).finish :=
  c.succAt_ne hu

/--
@isnad1 id=eq.1h4v.s7.84de7c8c5f4c from=translated src=- shape=152c2084 vocab=013659eb
-/
lemma rotateTo_cons_eq (c : GraphCycle G) {u : V} (hu : u ∈ c.support) :
    (c.rotateTo hu).walk =
      Walk.cons ((c.rotateTo hu).walk.adj_snd (c.rotateTo_not_nil hu))
        (c.openAt hu).walk :=
  ((c.rotateTo hu).walk.cons_tail_eq (c.rotateTo_not_nil hu)).symm

/--
@isnad1 id=eq.1h4v.s6.dd9226621553 from=translated src=- shape=de24812e vocab=3fe94152
-/
lemma openAt_length (c : GraphCycle G) {u : V} (hu : u ∈ c.support) :
    (c.openAt hu).walk.length = (c.rotateTo hu).walk.length - 1 :=
  Walk.length_tail (c.rotateTo hu).walk

/--
@isnad1 id=le.1h4v.s6.1a9e9e2e1d93 from=translated src=- shape=207d24a4 vocab=3ccf6419
-/
lemma two_le_openAt_length (c : GraphCycle G) {u : V} (hu : u ∈ c.support) :
    2 ≤ (c.openAt hu).walk.length := by
  have hlen : 3 ≤ (c.rotateTo hu).walk.length := (c.rotateTo hu).three_le_length
  have := c.openAt_length hu
  omega

/--
@isnad1 id=not.1h4v.s6.2fc56a401607 from=translated src=- shape=6f3cb08f vocab=6b617941
-/
lemma openAt_not_nil (c : GraphCycle G) {u : V} (hu : u ∈ c.support) :
    ¬ (c.openAt hu).walk.Nil :=
  Walk.not_nil_iff_lt_length.2
    (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) (c.two_le_openAt_length hu))

/--
@isnad1 id=le.1h4v.s5.e2e57d311ecd from=translated src=- shape=379261a4 vocab=520a91d7
-/
lemma three_le_openAt_card (c : GraphCycle G) {u : V} (hu : u ∈ c.support) :
    3 ≤ (c.openAt hu).support.card := by
  have : 2 ≤ (c.openAt hu).walk.length := c.two_le_openAt_length hu
  simpa [GraphPath.card_support] using Nat.add_le_add_right this 1

/--
@isnad1 id=mem.1h4v.s6.cc4f6acaa0d3 from=translated src=- shape=bba6eb32 vocab=f7264662
-/
lemma first_cycle_edge_mem (c : GraphCycle G) {u : V} (hu : u ∈ c.support) :
    s(u, c.succAt hu) ∈ c.edges := by
  have hnil := c.rotateTo_not_nil hu
  have hrot : s(u, c.succAt hu) ∈ (c.rotateTo hu).edges := by
    simpa [edges, start_rotateTo, succAt_eq_snd] using
      List.mem_toFinset.2 ((c.rotateTo hu).walk.mk_start_snd_mem_edges hnil)
  simpa [c.edges_rotateTo_eq hu] using hrot

/--
@isnad1 id=not.1h4v.s6.47599cc57e4b from=translated src=- shape=eaa6998b vocab=41bcfa4d
-/
lemma first_not_mem_openAt (c : GraphCycle G) {u : V} (hu : u ∈ c.support) :
    s(u, c.succAt hu) ∉ (c.openAt hu).edges := by
  have hnil := c.rotateTo_not_nil hu
  have hcons := (c.rotateTo hu).walk.cons_tail_eq hnil
  have hcycle : (Walk.cons ((c.rotateTo hu).walk.adj_snd hnil)
      ((c.rotateTo hu).walk.tail)).IsCycle := by
    convert (c.rotateTo hu).isCycle
  have hnin := (Walk.cons_isCycle_iff ((c.rotateTo hu).walk.tail)
      ((c.rotateTo hu).walk.adj_snd hnil)).1 hcycle |>.2
  simp [GraphPath.edges, openAt, start_rotateTo, succAt_eq_snd, List.mem_toFinset]
  exact hnin

/--
@isnad1 id=eq.1h4v.s6.0a758dc8bb58 from=translated src=- shape=4f4935f7 vocab=fe63bde4
-/
lemma edges_eq_insert_openAt (c : GraphCycle G) {u : V} (hu : u ∈ c.support) :
    c.edges = insert s(u, c.succAt hu) (c.openAt hu).edges := by
  have hnil := c.rotateTo_not_nil hu
  have hcons := (c.rotateTo hu).walk.cons_tail_eq hnil
  have hedges : (c.rotateTo hu).walk.edges =
      s((c.rotateTo hu).start, (c.rotateTo hu).walk.snd) ::
        (c.rotateTo hu).walk.tail.edges :=
    (congrArg Walk.edges hcons.symm).trans
      (Walk.edges_cons ((c.rotateTo hu).walk.adj_snd hnil)
        ((c.rotateTo hu).walk.tail))
  have hrot : (c.rotateTo hu).edges =
      insert s((c.rotateTo hu).start, (c.rotateTo hu).walk.snd)
        (c.openAt hu).edges := by
    simp only [edges, GraphPath.edges, openAt]
    rw [hedges, List.toFinset_cons]
    rfl
  have heq : s((c.rotateTo hu).start, (c.rotateTo hu).walk.snd) =
      s(u, c.succAt hu) := by
    simp [start_rotateTo, succAt_eq_snd]
  rw [heq] at hrot
  simpa [c.edges_rotateTo_eq hu] using hrot

/--
@isnad1 id=eq.2h6v.s5.25fce9443b8c from=translated src=- shape=bafeedc0 vocab=3700c919
-/
lemma penultimate_cons_of_not_nil {u v w : V} (h : G.Adj u v) (q : G.Walk v w)
    (hq : ¬ q.Nil) : (Walk.cons h q).penultimate = q.penultimate := by
  have hpos : 0 < q.length := Walk.not_nil_iff_lt_length.1 hq
  simp only [Walk.penultimate, Walk.length_cons]
  have : q.length + 1 - 1 = q.length := by omega
  rw [this]
  have hsucc : q.length = q.length - 1 + 1 := by omega
  rw [hsucc, Walk.getVert_cons_succ]
  simp

/--
@isnad1 id=eq.1h4v.s6.05ecdf14a605 from=translated src=- shape=9a0b0f3b vocab=3385abd2
-/
lemma penultimate_rotateTo (c : GraphCycle G) {u : V} (hu : u ∈ c.support) :
    (c.rotateTo hu).walk.penultimate = (c.openAt hu).walk.penultimate := by
  have hnil := c.rotateTo_not_nil hu
  have h := penultimate_cons_of_not_nil
    ((c.rotateTo hu).walk.adj_snd hnil) (c.openAt hu).walk (c.openAt_not_nil hu)
  exact (congrArg Walk.penultimate (c.rotateTo_cons_eq hu)).trans h

/--
@isnad1 id=mem.1h4v.s6.ee6eabde9caf from=translated src=- shape=f939bc7b vocab=607a7f3d
-/
lemma pred_edge_mem (c : GraphCycle G) {u : V} (hu : u ∈ c.support) :
    s((c.openAt hu).walk.penultimate, u) ∈ c.edges := by
  have hlast := GraphPath.last_edge_mem (c.openAt hu) (c.openAt_not_nil hu)
  have : s((c.openAt hu).walk.penultimate, u) ∈ (c.openAt hu).edges := by
    simpa [openAt_finish] using hlast
  rw [c.edges_eq_insert_openAt hu]
  exact mem_insert_of_mem this

/--
@isnad1 id=ne.1h4v.s6.7150ab18a3f6 from=translated src=- shape=55cfb15c vocab=6cd061fe
-/
lemma succ_ne_pred (c : GraphCycle G) {u : V} (hu : u ∈ c.support) :
    c.succAt hu ≠ (c.openAt hu).walk.penultimate := by
  have h := (c.rotateTo hu).isCycle.snd_ne_penultimate
  simpa [succAt_eq_snd, c.penultimate_rotateTo hu] using h

/--
@isnad1 id=ne.1h4v.s6.fe345ff23b64 from=translated src=- shape=8e487959 vocab=c863d248
-/
lemma first_ne_pred_edge (c : GraphCycle G) {u : V} (hu : u ∈ c.support) :
    s(u, c.succAt hu) ≠ s((c.openAt hu).walk.penultimate, u) := by
  intro heq
  rcases (Sym2.eq_iff.mp heq) with ⟨_, h2⟩ | ⟨_, h2⟩
  · exact (c.succAt_ne hu) h2
  · exact (c.succ_ne_pred hu) h2

/-- Exact two incident original cycle-edges at any vertex of a genuine
simple cycle of order at least three.
@isnad1 id=eq.1h4v.s6.073fabc16626 from=translated src=- shape=39931db2 vocab=3c84cfdb
-/
theorem incidentEdges_eq (c : GraphCycle G) {v : V} (hv : v ∈ c.support) :
    c.incidentEdges v =
      {s(v, c.succAt hv), s((c.openAt hv).walk.penultimate, v)} := by
  have hopen :=
    GraphPath.incidentEdges_finish (c.openAt hv) (c.openAt_not_nil hv)
  have hfin : (c.openAt hv).finish = v := c.openAt_finish hv
  have hopen' : (c.openAt hv).incidentEdges v =
      {s((c.openAt hv).walk.penultimate, v)} := by
    simpa [hfin] using hopen
  ext e
  simp only [mem_incidentEdges_iff, c.edges_eq_insert_openAt hv, mem_insert,
    mem_singleton]
  constructor
  · rintro ⟨hmem, hve⟩
    rcases hmem with rfl | hrest
    · exact Or.inl rfl
    · have : e ∈ (c.openAt hv).incidentEdges v :=
        GraphPath.mem_incidentEdges_iff.2 ⟨hrest, hve⟩
      have : e = s((c.openAt hv).walk.penultimate, v) :=
        mem_singleton.1 (by simpa [hopen'] using this)
      exact Or.inr this
  · rintro (rfl | rfl)
    · exact ⟨Or.inl rfl, by simp⟩
    · refine ⟨Or.inr ?_, by simp⟩
      simpa [hfin] using GraphPath.last_edge_mem (c.openAt hv) (c.openAt_not_nil hv)

/--
@isnad1 id=eq.1h4v.s5.9569c2d0058b from=translated src=- shape=cf8bd61d vocab=a4c5a4f4
-/
theorem incidentEdges_card (c : GraphCycle G) {v : V} (hv : v ∈ c.support) :
    (c.incidentEdges v).card = 2 := by
  rw [c.incidentEdges_eq hv]
  exact card_pair (c.first_ne_pred_edge hv)

/--
@isnad1 id=le.0h4v.s5.26ba16c724b3 from=translated src=- shape=69af219d vocab=53855d41
-/
lemma incidentEdges_subset_edges (c : GraphCycle G) (v : V) :
    c.incidentEdges v ⊆ c.edges := by
  intro e he
  exact (c.mem_incidentEdges_iff.1 he).1

end GraphCycle

namespace GraphPath

/--
@isnad1 id=iff.0h5v.s5.003798961410 from=translated src=- shape=866e60a6 vocab=4f203b4d
-/
lemma ProtectedAt.reverse_cycle {p : GraphPath G} {c : GraphCycle G}
    {A : Finset V} : p.ProtectedAt c.reverse A ↔ p.ProtectedAt c A := by
  simp [ProtectedAt, GraphCycle.reverse, Walk.edges_reverse, List.toFinset_reverse]

/--
@isnad1 id=le.2h6v.s6.86d9928f2a0b from=translated src=- shape=ddb1a269 vocab=0459c865
-/
lemma ProtectedAt.incidentEdges_subset_cycle {p : GraphPath G}
    {c : GraphCycle G} {A : Finset V} (h : p.ProtectedAt c A) {v : V}
    (hv : v ∈ A) : p.incidentEdges v ⊆ c.incidentEdges v := by
  intro e he
  have heA : e ∈ p.AIncident A := p.incidentEdges_subset_AIncident hv he
  exact GraphCycle.mem_incidentEdges_iff.2 ⟨h heA, (mem_incidentEdges_iff.1 he).2⟩

/-- Internal `A`-vertices of a spanning protected path have incident
walk-edges exactly equal to the two incident edges of the prescribed
cycle. Path order at least three is inherited from the genuine cycle,
not from a stronger graph-degree hypothesis.
@isnad1 id=eq.6h6v.s6.3a3d7b65d4ec from=translated src=- shape=0139226c vocab=4d8233de
-/
theorem incidentEdges_eq_cycle_of_internal_protected
    (p : GraphPath G) (c : GraphCycle G) {A : Finset V}
    (hsup : p.support = c.support) (hA : A ⊆ p.support)
    (hP : p.ProtectedAt c A) {v : V}
    (hvA : v ∈ A) (hs : v ≠ p.start) (hf : v ≠ p.finish) :
    p.incidentEdges v = c.incidentEdges v := by
  have hvU : v ∈ p.support := hA hvA
  have hvC : v ∈ c.support := by simpa [hsup] using hvU
  have h2p : (p.incidentEdges v).card = 2 :=
    p.incidentEdges_card_internal hvU hs hf
  have h2c : (c.incidentEdges v).card = 2 := c.incidentEdges_card hvC
  have hsub : p.incidentEdges v ⊆ c.incidentEdges v :=
    hP.incidentEdges_subset_cycle hvA
  exact eq_of_subset_of_card_le hsub (by omega)

/-- An endpoint of a spanning protected path that lies in `A` is incident
to exactly one prescribed cycle edge. Completeness of `A` to all other
vertices is not assumed.
@isnad1 id=and.5h6v.s7.40ef313bcd52 from=translated src=- shape=ceaf28bf vocab=9d332e06
-/
theorem incidentEdges_card_endpoint_protected
    (p : GraphPath G) (c : GraphCycle G) {A : Finset V}
    (hsup : p.support = c.support) (_hA : A ⊆ p.support)
    (hP : p.ProtectedAt c A) {v : V}
    (hvA : v ∈ A) (hE : v = p.start ∨ v = p.finish) :
    (p.incidentEdges v).card = 1 ∧ p.incidentEdges v ⊆ c.edges := by
  have h3 : 3 ≤ p.support.card := by simpa [hsup] using c.three_le_card_support
  have h2 : 2 ≤ p.support.card := le_trans (by decide : (2 : ℕ) ≤ 3) h3
  have hcard : (p.incidentEdges v).card = 1 := by
    rcases hE with rfl | rfl
    · exact p.incidentEdges_card_start h2
    · exact p.incidentEdges_card_finish h2
  refine ⟨hcard, ?_⟩
  intro e he
  exact hP (mem_AIncident_iff.2 ⟨(mem_incidentEdges_iff.1 he).1,
    ⟨v, hvA, (mem_incidentEdges_iff.1 he).2⟩⟩)

/-- Prefix rotation retains the original-`A` internal-2 / endpoint-1
counts of a spanning protected path. The new start `a` is an endpoint
and loses exactly the old dart `a—x`. Every other vertex of `A` keeps
its incident walk-edge set. Protection is asserted only at the original
set `A`; it is not asserted at any enlarged set containing the old
`Y`-endpoint. The factorization already supplies `a ≠ finish`.
@isnad1 id=and.7h8v.s8.4adce084e243 from=translated src=- shape=ce62db0e vocab=cf79390a
-/
theorem protected_exact_of_rotate {p : GraphPath G} {a x : V}
    (F : PrefixEdgeFactor p a x) (hyx : G.Adj p.start x)
    (c : GraphCycle G) {A : Finset V}
    (hsup : p.support = c.support) (hA : A ⊆ p.support)
    (haA : a ∈ A) (hyA : p.start ∉ A) (hxA : x ∉ A)
    (hP : p.ProtectedAt c A) :
    (F.rotate hyx).ProtectedAt c A ∧
      (F.rotate hyx).start = a ∧
        (F.rotate hyx).start ≠ (F.rotate hyx).finish ∧
          (F.rotate hyx).incidentEdges a = p.incidentEdges a \ {s(a, x)} ∧
            (∀ b ∈ A, b ≠ a →
              (F.rotate hyx).incidentEdges b = p.incidentEdges b) ∧
              (∀ b ∈ A, b ≠ a → b ≠ (F.rotate hyx).finish →
                (F.rotate hyx).incidentEdges b = c.incidentEdges b) ∧
                ((F.rotate hyx).incidentEdges a).card = 1 ∧
                  (F.rotate hyx).incidentEdges a ⊆ c.edges := by
  set q := F.rotate hyx
  have hqProt : q.ProtectedAt c A :=
    F.protectedAt_rotate hyx haA hyA hxA hP
  have hqst : q.start = a := F.rotate_start hyx
  have hqfin : q.finish = p.finish := F.rotate_finish hyx
  have hne : q.start ≠ q.finish := F.rotate_start_ne_finish hyx
  have hat : q.incidentEdges a = p.incidentEdges a \ {s(a, x)} :=
    F.incidentEdges_rotate_at_a hyx haA hyA hxA
  have hother : ∀ b ∈ A, b ≠ a → q.incidentEdges b = p.incidentEdges b :=
    fun b hbA hba => F.incidentEdges_rotate_of_mem_A hyx hbA haA hyA hxA hba
  have hsupq : q.support = c.support :=
    (F.rotate_support hyx).trans hsup
  have hAq : A ⊆ q.support := by
    rw [show q.support = p.support from F.rotate_support hyx]
    exact hA
  have haEnd : (q.incidentEdges a).card = 1 ∧ q.incidentEdges a ⊆ c.edges :=
    incidentEdges_card_endpoint_protected q c hsupq hAq hqProt haA (Or.inl hqst)
  refine ⟨hqProt, hqst, hne, hat, hother, ?_, haEnd.1, haEnd.2⟩
  intro b hbA hba hbf
  have hbeq : q.incidentEdges b = p.incidentEdges b := hother b hbA hba
  have hs : b ≠ p.start := fun h => hyA (h ▸ hbA)
  have hf : b ≠ p.finish := by
    intro h
    apply hbf
    simpa [hqfin] using h
  have : p.incidentEdges b = c.incidentEdges b :=
    incidentEdges_eq_cycle_of_internal_protected p c hsup hA hP hbA hs hf
  exact hbeq.trans this

end GraphPath

end Nikoghosyan
