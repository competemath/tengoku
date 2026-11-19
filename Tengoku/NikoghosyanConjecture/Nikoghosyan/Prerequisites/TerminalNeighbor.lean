/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Tengoku.NikoghosyanConjecture.Nikoghosyan.Prerequisites.TerminalCover

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/canghaimeng/Nikoghosyan-conjecture@ccc8514d6801, `Nikoghosyan/Prerequisites/TerminalNeighbor.lean`: removed 2 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-!
# Derived original-host neighbor condition and terminal pieces

From `AllCographSides` and `NoInducedP4UnionP1`, an original edge `b-v`
with `b ∈ B`, `v ∈ W` and a missing edge `b-w` for `w ∈ W` forces the
original edge `v-w`. Together with cograph `K = B ∪ W` this nests the
`B`-neighborhoods in `W`.

Deleting an independent terminal set `B` from a `B`-terminal cover of
`K` yields an ordinary path cover of `K \ B` whose cardinality `r`
satisfies the additive identity `r + q = |B|`.
-/

universe u


open Classical
open Finset Function SimpleGraph

namespace Nikoghosyan

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Original-host neighbor condition on a pair `(K, B)`: missing `b-w` with
present `b-v` forces the original edge `v-w` inside `K \ B`.-/
def NeighborCondition (K B : Finset V) : Prop :=
  ∀ ⦃b v w : V⦄, b ∈ B → v ∈ K \ B → w ∈ K \ B →
    G.Adj b v → ¬ G.Adj b w → G.Adj v w

/-- Repaired terminal hypothesis: cograph carrier, independent terminals,
actual component-count cuts, and the derived neighbor condition.-/
def RepairedTerminalHypothesis (K B : Finset V) : Prop :=
  IsCograph G K ∧ B ⊆ K ∧ Independent (G := G) B ∧
    TerminalHypothesis (G := G) K B ∧ NeighborCondition (G := G) K B

namespace AllCographSides

variable (P : AllCographSides G)

/--
@isnad1 id=le.0h3v.s5.e9d093e227a6 from=translated src=- shape=a7b495b4 vocab=aeb692e9
-/
lemma B_subset_K : P.B ⊆ P.B ∪ P.W := subset_union_left

/--
@isnad1 id=le.0h3v.s5.4dbea8af7b6a from=translated src=- shape=beb6ba0d vocab=aeb692e9
-/
lemma W_subset_K : P.W ⊆ P.B ∪ P.W := subset_union_right

/--
@isnad1 id=eq.0h3v.s5.29a08f89f2d5 from=translated src=- shape=ba9dcc82 vocab=a3fc0aac
-/
lemma K_sdiff_B : (P.B ∪ P.W) \ P.B = P.W := by
  ext x
  constructor
  · intro hx
    have hxUW := (mem_sdiff.1 hx).1
    have hxB := (mem_sdiff.1 hx).2
    rcases mem_union.1 hxUW with hB | hW
    · exact (hxB hB).elim
    · exact hW
  · intro hx
    refine mem_sdiff.2 ⟨mem_union.2 (Or.inr hx), ?_⟩
    intro hB
    exact disjoint_left.1 P.hdisjBW hB hx

/--
@isnad1 id=iff.0h4v.s6.0cf20ddb99a9 from=translated src=- shape=952fca86 vocab=2ac0b319
-/
lemma mem_W_iff_mem_K_sdiff_B {x : V} :
    x ∈ P.W ↔ x ∈ (P.B ∪ P.W) \ P.B := by
  rw [K_sdiff_B]

/-- `u-a-b-v` is an original induced `P₄` from the stated complete and
anticomplete interfaces.
@isnad1 id=inducedp.5h7v.s6.fe0c500699d7 from=translated src=- shape=75af6258 vocab=ee29927b
-/
lemma inducedP4_uabv
    {u a b v : V} (hu : u ∈ P.U) (ha : a ∈ P.A) (hb : b ∈ P.B) (hv : v ∈ P.W)
    (hbv : G.Adj b v) : InducedP4 G u a b v := by
  have hUA : u ≠ a := fun h => disjoint_left.1 P.hdisjAU ha (h ▸ hu)
  have hUB : u ≠ b := fun h => disjoint_left.1 P.hdisjBU hb (h ▸ hu)
  have hUV : u ≠ v := fun h => disjoint_left.1 P.hdisjUW hu (h ▸ hv)
  have hAB : a ≠ b := fun h => disjoint_left.1 P.disjoint_A_B ha (h ▸ hb)
  have hAV : a ≠ v := fun h => disjoint_left.1 P.hdisjAW ha (h ▸ hv)
  have hBV : b ≠ v := fun h => disjoint_left.1 P.hdisjBW hb (h ▸ hv)
  have hadj_ua : G.Adj u a := (P.hAU ha hu).symm
  have hadj_ab : G.Adj a b := P.hAB ha hb
  have nadj_ub : ¬ G.Adj u b := P.hUantiB u hu b hb
  have nadj_uv : ¬ G.Adj u v := P.hUantiW u hu v hv
  have nadj_av : ¬ G.Adj a v := fun h => P.hWantiA v hv a ha h.symm
  exact ⟨hUA, hUB, hUV, hAB, hAV, hBV, hadj_ua, hadj_ab, hbv,
    nadj_ub, nadj_uv, nadj_av⟩

/-- Host neighbor condition on `W`, with no toughness premise.
@isnad1 id=adj.6h6v.s6.2db32e520902 from=translated src=- shape=b75018d8 vocab=69723a17
-/
lemma adj_of_missing_B_neighbor (hpat : NoInducedP4UnionP1 G)
    {b v w : V} (hb : b ∈ P.B) (hv : v ∈ P.W) (hw : w ∈ P.W)
    (hbv : G.Adj b v) (hbw : ¬ G.Adj b w) : G.Adj v w := by
  obtain ⟨u, hu⟩ := P.hUne
  obtain ⟨a, ha⟩ := P.A_nonempty
  have hp4 : InducedP4 G u a b v := P.inducedP4_uabv hu ha hb hv hbv
  have hwU : w ≠ u := fun h => disjoint_left.1 P.hdisjUW hu (h ▸ hw)
  have hwA : w ≠ a := fun h => disjoint_left.1 P.hdisjAW ha (h ▸ hw)
  have hwB : w ≠ b := fun h => disjoint_left.1 P.hdisjBW hb (h ▸ hw)
  have hwV : w ≠ v := fun h => hbw (h ▸ hbv)
  have nadj_wu : ¬ G.Adj w u := fun h => P.hUantiW u hu w hw h.symm
  have nadj_wa : ¬ G.Adj w a := P.hWantiA w hw a ha
  have nadj_wb : ¬ G.Adj w b := fun h => hbw h.symm
  have hmeet := hpat hp4 hwU hwA hwB hwV
  rcases hmeet with hwu | hwa | hwb | hwv
  · exact (nadj_wu hwu).elim
  · exact (nadj_wa hwa).elim
  · exact (nadj_wb hwb).elim
  · exact hwv.symm

/--
@isnad1 id=neighbor.1h3v.s5.cd849226a57b from=translated src=- shape=aa73d284 vocab=ec371855
-/
lemma neighborCondition_K (hpat : NoInducedP4UnionP1 G) :
    NeighborCondition (G := G) (P.B ∪ P.W) P.B := by
  intro b v w hb hv hw hbv hbw
  have hvW : v ∈ P.W := (P.mem_W_iff_mem_K_sdiff_B).2 hv
  have hwW : w ∈ P.W := (P.mem_W_iff_mem_K_sdiff_B).2 hw
  exact P.adj_of_missing_B_neighbor hpat hb hvW hwW hbv hbw

end AllCographSides

/-- Incomparable `B`-neighborhoods inside a cograph produce an induced `P₄`.
@isnad1 id=false.12h8v.s7.c36fb3213902 from=translated src=- shape=47dc8390 vocab=a5567fa6
-/
lemma not_incomparable_B_neighbors {K B : Finset V}
    (hK : IsCograph G K) (hB : Independent (G := G) B) (hBK : B ⊆ K)
    (hN : NeighborCondition (G := G) K B)
    {b b' v w : V} (hb : b ∈ B) (hb' : b' ∈ B)
    (hv : v ∈ K \ B) (hw : w ∈ K \ B)
    (hbv : G.Adj b v) (hnb'v : ¬ G.Adj b' v)
    (hb'w : G.Adj b' w) (hnbw : ¬ G.Adj b w) : False := by
  have hvw : G.Adj v w := hN hb hv hw hbv hnbw
  have hbK : b ∈ K := hBK hb
  have hb'K : b' ∈ K := hBK hb'
  have hvK : v ∈ K := (mem_sdiff.1 hv).1
  have hwK : w ∈ K := (mem_sdiff.1 hw).1
  have hne_bv : b ≠ v := fun h => (mem_sdiff.1 hv).2 (h ▸ hb)
  have hne_bw : b ≠ w := fun h => (mem_sdiff.1 hw).2 (h ▸ hb)
  have hne_bb' : b ≠ b' := fun h => hnb'v (h ▸ hbv)
  have hne_vw : v ≠ w := fun h => hnbw (h ▸ hbv)
  have hne_vb' : v ≠ b' := fun h => (mem_sdiff.1 hv).2 (h ▸ hb')
  have hne_wb' : w ≠ b' := fun h => (mem_sdiff.1 hw).2 (h ▸ hb')
  have nadj_bb' : ¬ G.Adj b b' := hB hb hb'
  have nadj_vb' : ¬ G.Adj v b' := fun h => hnb'v h.symm
  have hp4 : InducedP4 G b v w b' :=
    ⟨hne_bv, hne_bw, hne_bb', hne_vw, hne_vb', hne_wb',
      hbv, hvw, hb'w.symm, hnbw, nadj_bb', nadj_vb'⟩
  exact hK hbK hvK hwK hb'K hp4

/-- Neighborhoods of terminals inside `K \ B` are nested.
@isnad1 id=or.6h6v.s7.ea1ff42ab9b4 from=translated src=- shape=299d7d26 vocab=39ac714e
-/
lemma neighborSet_nested {K B : Finset V}
    (hK : IsCograph G K) (hB : Independent (G := G) B) (hBK : B ⊆ K)
    (hN : NeighborCondition (G := G) K B)
    {b b' : V} (hb : b ∈ B) (hb' : b' ∈ B) :
    (K \ B).filter (fun x => G.Adj b x) ⊆ (K \ B).filter (fun x => G.Adj b' x) ∨
      (K \ B).filter (fun x => G.Adj b' x) ⊆
        (K \ B).filter (fun x => G.Adj b x) := by
  by_contra h
  have h1 : ¬ ((K \ B).filter (fun x => G.Adj b x) ⊆
      (K \ B).filter (fun x => G.Adj b' x)) := fun hst => h (Or.inl hst)
  have h2 : ¬ ((K \ B).filter (fun x => G.Adj b' x) ⊆
      (K \ B).filter (fun x => G.Adj b x)) := fun hts => h (Or.inr hts)
  obtain ⟨v, hv, hv'⟩ := not_subset.1 h1
  obtain ⟨w, hw, hw'⟩ := not_subset.1 h2
  have hv1 := mem_filter.1 hv
  have hw1 := mem_filter.1 hw
  have hnb'v : ¬ G.Adj b' v := fun hadj =>
    hv' (mem_filter.2 ⟨hv1.1, hadj⟩)
  have hnbw : ¬ G.Adj b w := fun hadj =>
    hw' (mem_filter.2 ⟨hw1.1, hadj⟩)
  exact not_incomparable_B_neighbors (G := G) hK hB hBK hN hb hb'
    hv1.1 hw1.1 hv1.2 hnb'v hw1.2 hnbw

/-- Under the neighbor condition, a `B`–`(K \ B)` edge places every
nonterminal of `K` in the same induced component as that edge.
@isnad1 id=reachabl.6h7v.s7.b9da415749a5 from=translated src=- shape=2729ab1b vocab=5dcf5d4e
-/
lemma reachable_all_nonterminals_of_neighbor {K B : Finset V}
    (hN : NeighborCondition (G := G) K B) (hBK : B ⊆ K)
    {b v w : V} (hb : b ∈ B) (hv : v ∈ K \ B) (hw : w ∈ K \ B)
    (hadj : G.Adj b v) :
    (G.induce (K : Set V)).Reachable ⟨v, (mem_sdiff.1 hv).1⟩
      ⟨w, (mem_sdiff.1 hw).1⟩ := by
  have hbK : b ∈ K := hBK hb
  have hvK : v ∈ K := (mem_sdiff.1 hv).1
  have hwK : w ∈ K := (mem_sdiff.1 hw).1
  by_cases hbw : G.Adj b w
  · have hvb : (G.induce (K : Set V)).Adj ⟨v, hvK⟩ ⟨b, hbK⟩ := by
      simpa [induce_adj] using hadj.symm
    have hbw' : (G.induce (K : Set V)).Adj ⟨b, hbK⟩ ⟨w, hwK⟩ := by
      simpa [induce_adj] using hbw
    exact (Adj.reachable hvb).trans (Adj.reachable hbw')
  · have hvw : G.Adj v w := hN hb hv hw hadj hbw
    have : (G.induce (K : Set V)).Adj ⟨v, hvK⟩ ⟨w, hwK⟩ := by
      simpa [induce_adj] using hvw
    exact Adj.reachable this

/-- The union of `support ∩ B` over a path cover of `K` is exactly `B`
when `B ⊆ K`.
@isnad1 id=eq.1h5v.s6.9c8776933775 from=translated src=- shape=44f80dba vocab=8310e0d2
-/
lemma PathCover.biUnion_support_inter_eq {K B : Finset V} (pc : PathCover G K)
    (hBK : B ⊆ K) :
    (pc.paths.toFinset.biUnion fun p => p.support ∩ B) = B := by
  ext x
  constructor
  · intro hx
    obtain ⟨p, _hp, hxp⟩ := mem_biUnion.1 hx
    exact (mem_inter.1 hxp).2
  · intro hx
    have hxK : x ∈ K := hBK hx
    obtain ⟨p, hp, hxp⟩ := (pc.mem_iff x).1 hxK
    exact mem_biUnion.2 ⟨p, List.mem_toFinset.2 hp, mem_inter.2 ⟨hxp, hx⟩⟩

/-- Supports of distinct cover paths are disjoint, so their `B`-slices
are disjoint.
@isnad1 id=pairwise.0h5v.s6.aa8d3db3034b from=translated src=- shape=d87d654a vocab=81b57815
-/
lemma PathCover.pairwiseDisjoint_support_inter {K B : Finset V}
    (pc : PathCover G K) :
    (pc.paths.toFinset : Set (GraphPath G)).PairwiseDisjoint
      fun p => p.support ∩ B := by
  intro p hp q hq hne
  have hp' : p ∈ pc.paths := List.mem_toFinset.1 hp
  have hq' : q ∈ pc.paths := List.mem_toFinset.1 hq
  have hd :=
    PathCover.pairwise_disjoint_of_mem_refinement pc.disjoint hp' hq' hne
  exact disjoint_of_subset_left inter_subset_left
    (disjoint_of_subset_right inter_subset_left hd)

/-- Sum of `(support ∩ B).card` over a path cover of `K` equals `|B|`.
@isnad1 id=eq.1h5v.s6.5f7cb8c03fbb from=translated src=- shape=09d91c88 vocab=3e96bb70
-/
lemma PathCover.sum_support_inter_card {K B : Finset V} (pc : PathCover G K)
    (hBK : B ⊆ K) :
    ∑ p ∈ pc.paths.toFinset, (p.support ∩ B).card = B.card := by
  have hdisj := pc.pairwiseDisjoint_support_inter (B := B)
  rw [← card_biUnion hdisj, pc.biUnion_support_inter_eq hBK]

/--
@isnad1 id=le.1h4v.s5.46ef4f884c6c from=translated src=- shape=902166f3 vocab=c9bcd905
-/
lemma IsTerminalPath.one_le_support_inter_card {B : Finset V} {p : GraphPath G}
    (h : IsTerminalPath (G := G) B p) : 1 ≤ (p.support ∩ B).card :=
  card_pos.mpr ⟨p.start, mem_inter.2 ⟨p.start_mem_support, h.1⟩⟩

/--
@isnad1 id=eq.0h4v.s5.49bd9465d127 from=translated src=- shape=4ef90c12 vocab=dee09d1f
-/
lemma PathCover.paths_toFinset_card {K : Finset V} (pc : PathCover G K) :
    pc.paths.toFinset.card = pc.card :=
  List.toFinset_card_of_nodup pc.nodup_paths

/-- Additive identity for an actual `B`-terminal cover: writing
`t(p) = |p.support ∩ B|` for each path, one has
`∑ (t(p) - 1) + q = |B|`. Each `t(p) - 1` counts the nonempty
original-edge pieces of that path after deleting `B`, because `B` is
independent so no two `B`-vertices are adjacent on a path, and both
endpoints lie in `B`.
@isnad1 id=eq.2h5v.s6.80c763400b14 from=translated src=- shape=ca1493b9 vocab=de8929dc
-/
lemma PathCover.terminal_excess_add {K B : Finset V} (pc : PathCover G K)
    (hBK : B ⊆ K) (hterm : IsTerminalCover (G := G) B pc) :
    ∑ p ∈ pc.paths.toFinset, ((p.support ∩ B).card - 1) + pc.card =
      B.card := by
  have hge : ∀ p ∈ pc.paths.toFinset, 1 ≤ (p.support ∩ B).card := by
    intro p hp
    have hp' : p ∈ pc.paths := List.mem_toFinset.1 hp
    exact (hterm p hp').one_le_support_inter_card
  have hsum := pc.sum_support_inter_card hBK
  have hsub :
      ∑ p ∈ pc.paths.toFinset, ((p.support ∩ B).card - 1) =
        ∑ p ∈ pc.paths.toFinset, (p.support ∩ B).card -
          ∑ p ∈ pc.paths.toFinset, 1 :=
    Finset.sum_tsub_distrib pc.paths.toFinset hge
  have hone : ∑ p ∈ pc.paths.toFinset, 1 = pc.card := by
    simp [sum_const, pc.paths_toFinset_card]
  have hle : pc.card ≤ B.card := terminalCover_card_le (G := G) pc hterm
  have hex :
      ∑ p ∈ pc.paths.toFinset, ((p.support ∩ B).card - 1) =
        B.card - pc.card := by
    rw [hsub, hsum, hone]
  rw [hex]
  exact Nat.sub_add_cancel hle

/-- After deleting every terminal, every remaining induced component is
`B`-free, so `z_B(K-B) = c(K \ B)`.
@isnad1 id=eq.0h4v.s5.c7910aa318da from=translated src=- shape=a8ad90f5 vocab=babc095e
-/
lemma terminalComponentCount_eq_componentCount_sdiff_B {K B : Finset V} :
    terminalComponentCount (G := G) K B B = componentCount G (K \ B) := by
  unfold terminalComponentCount componentCount
  refine Nat.card_congr ?_
  refine Equiv.subtypeUnivEquiv ?_
  intro C
  unfold IsFreeComponent
  simp

/--
@isnad1 id=le.3h4v.s6.27156756c651 from=translated src=- shape=72bf0d37 vocab=093e1622
-/
lemma componentCount_sdiff_B_le_of_terminalHypothesis {K B : Finset V}
    (h : TerminalHypothesis (G := G) K B) (hBK : B ⊆ K) (hne : B.Nonempty) :
    componentCount G (K \ B) ≤ B.card - 1 := by
  have := h.2 B hBK hne
  rwa [terminalComponentCount_eq_componentCount_sdiff_B] at this

/-- `RepairedTerminalHypothesis` on the original side `K = B ∪ W`.
@isnad1 id=repaired.2h3v.s6.05cffa4edfc1 from=translated src=- shape=4d92f882 vocab=b08a3cfd
-/
lemma repairedTerminalHypothesis_of_sides (P : AllCographSides G)
    (hpat : NoInducedP4UnionP1 G)
    (hterm : TerminalHypothesis (G := G) (P.B ∪ P.W) P.B) :
    RepairedTerminalHypothesis (G := G) (P.B ∪ P.W) P.B :=
  ⟨P.hKcog, P.B_subset_K, P.hBind, hterm, P.neighborCondition_K hpat⟩

end Nikoghosyan
