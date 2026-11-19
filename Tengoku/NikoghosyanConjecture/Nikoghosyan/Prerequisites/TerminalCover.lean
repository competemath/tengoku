/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Tengoku.NikoghosyanConjecture.Nikoghosyan.Cograph.EndpointCuts
import Tengoku.NikoghosyanConjecture.Nikoghosyan.Cograph.PathCoverJoin
import Tengoku.NikoghosyanConjecture.Nikoghosyan.Cograph.PathCoverRefinement

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/canghaimeng/Nikoghosyan-conjecture@ccc8514d6801, `Nikoghosyan/Prerequisites/TerminalCover.lean`: removed 2 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-!
# B-terminal original-edge path covers of a cograph

For a finite cograph on `K` and an independent terminal set `B ⊆ K`, a
`B`-terminal cover is an ordinary `PathCover` of `K` whose every path has
both endpoints in `B` (singleton `B`-paths allowed).

`z_B(K-S)` counts actual induced components of `G[K \ S]` that miss the
surviving terminals `B \ S`. This module also records the original-graph
cut capacities used by the all-cograph replacement plan.
-/

universe u


open Classical
open Finset Function SimpleGraph

namespace Nikoghosyan

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- No original edge has both ends in `B`.-/
def Independent (B : Finset V) : Prop :=
  ∀ ⦃x y : V⦄, x ∈ B → y ∈ B → ¬ G.Adj x y

/--
@isnad1 id=not.3h5v.s5.b668b867596d from=translated src=- shape=e0410b96 vocab=cb174518
-/
lemma Independent.anti {B : Finset V} (h : Independent (G := G) B)
    {x y : V} (hx : x ∈ B) (hy : y ∈ B) : ¬ G.Adj x y :=
  h hx hy

/--
@isnad1 id=independ.2h4v.s5.8abd09c2efcf from=translated src=- shape=a77a430f vocab=33bf5cfb
-/
lemma Independent.mono {B C : Finset V} (h : Independent (G := G) C)
    (hBC : B ⊆ C) : Independent (G := G) B :=
  fun _ _ hx hy => h (hBC hx) (hBC hy)

/--
@isnad1 id=not.3h5v.s5.047206df0ff5 from=translated src=- shape=399d117e vocab=cb174518
-/
lemma Independent.not_mem_of_adj {B : Finset V} (h : Independent (G := G) B)
    {x y : V} (hy : y ∈ B) (hadj : G.Adj x y) : x ∉ B :=
  fun hx => h hx hy hadj

/-- Both endpoints of an original-edge path lie in the terminal set.-/
def IsTerminalPath (B : Finset V) (p : GraphPath G) : Prop :=
  p.start ∈ B ∧ p.finish ∈ B

/-- Ordinary original-edge path cover with every path `B`-ended.-/
def IsTerminalCover {K : Finset V} (B : Finset V) (pc : PathCover G K) : Prop :=
  ∀ p ∈ pc.paths, IsTerminalPath (G := G) B p

/--
@isnad1 id=istermin.2h6v.s5.d4797f83d7f5 from=translated src=- shape=5ae8826b vocab=737e07de
-/
lemma IsTerminalCover.of_subset {K B C : Finset V} {pc : PathCover G K}
    (h : IsTerminalCover (G := G) B pc) (hBC : B ⊆ C) :
    IsTerminalCover (G := G) C pc :=
  fun p hp =>
    have ⟨hs, hf⟩ := h p hp
    ⟨hBC hs, hBC hf⟩

/--
@isnad1 id=nonempty.1h4v.s5.4529b446bfdd from=translated src=- shape=ab40873b vocab=ab39a242
-/
lemma IsTerminalPath.inter_nonempty {B : Finset V} {p : GraphPath G}
    (h : IsTerminalPath (G := G) B p) : (B ∩ p.support).Nonempty :=
  ⟨p.start, mem_inter.2 ⟨h.1, p.start_mem_support⟩⟩

namespace GraphPath

/--
@isnad1 id=adj.1h3v.s5.c9bb36735214 from=translated src=- shape=c4d0b005 vocab=f9a3d459
-/
lemma adj_start_trimStart (p : GraphPath G) (h : ¬ p.walk.Nil) :
    G.Adj p.start (p.trimStart h).start := by
  rcases p with ⟨u, v, walk, isPath⟩
  cases walk with
  | nil => exact (h Walk.nil_nil).elim
  | cons hadj q => simpa [trimStart] using hadj

/--
@isnad1 id=le.1h4v.s5.d014c705c3d2 from=translated src=- shape=941d0d9c vocab=cf4e3005
-/
lemma takeUntil_support_subset (p : GraphPath G) {x : V} (hx : x ∈ p.support) :
    (p.takeUntil hx).support ⊆ p.support := by
  intro y hy
  have : y ∈ (p.takeUntil hx).support ∪ (p.dropUntil hx).support :=
    mem_union.2 (Or.inl hy)
  rwa [support_takeUntil_union_dropUntil] at this

/--
@isnad1 id=le.1h4v.s5.96d15c1f04af from=translated src=- shape=941d0d9c vocab=b4aedb5c
-/
lemma dropUntil_support_subset (p : GraphPath G) {x : V} (hx : x ∈ p.support) :
    (p.dropUntil hx).support ⊆ p.support := by
  intro y hy
  have : y ∈ (p.takeUntil hx).support ∪ (p.dropUntil hx).support :=
    mem_union.2 (Or.inr hy)
  rwa [support_takeUntil_union_dropUntil] at this

/--
@isnad1 id=lt.1h3v.s5.880814d138cb from=translated src=- shape=9c542440 vocab=77e1705d
-/
lemma trimStart_support_card_lt (p : GraphPath G) (h : ¬ p.walk.Nil) :
    (p.trimStart h).support.card < p.support.card := by
  rw [support_trimStart]
  exact card_erase_lt_of_mem p.start_mem_support

/--
@isnad1 id=lt.1h3v.s5.3dbedebc4248 from=translated src=- shape=9c542440 vocab=83adea81
-/
lemma trimFinish_support_card_lt (p : GraphPath G) (h : ¬ p.walk.Nil) :
    (p.trimFinish h).support.card < p.support.card := by
  rw [support_trimFinish]
  exact card_erase_lt_of_mem p.finish_mem_support

/--
@isnad1 id=lt.2h4v.s6.9744b38bb969 from=translated src=- shape=d775745d vocab=0c167eb3
-/
lemma trimFinish_takeUntil_support_card_lt (p : GraphPath G) {x : V}
    (hx : x ∈ p.support) (hs : x ≠ p.start) :
    ((p.takeUntil hx).trimFinish
        (fun hn => hs ((takeUntil_nil_iff p hx).1 hn))).support.card <
      p.support.card := by
  have hnil : ¬ (p.takeUntil hx).walk.Nil := fun hn =>
    hs ((takeUntil_nil_iff p hx).1 hn)
  exact (trimFinish_support_card_lt (p.takeUntil hx) hnil).trans_le
    (card_le_card (takeUntil_support_subset p hx))

/--
@isnad1 id=lt.2h4v.s6.d08ba5bf94c1 from=translated src=- shape=a87f9e97 vocab=af02cc2a
-/
lemma trimStart_dropUntil_support_card_lt (p : GraphPath G) {x : V}
    (hx : x ∈ p.support) (hf : x ≠ p.finish) :
    ((p.dropUntil hx).trimStart
        (fun hn => hf ((dropUntil_nil_iff p hx).1 hn))).support.card <
      p.support.card := by
  have hnil : ¬ (p.dropUntil hx).walk.Nil := fun hn =>
    hf ((dropUntil_nil_iff p hx).1 hn)
  exact (trimStart_support_card_lt (p.dropUntil hx) hnil).trans_le
    (card_le_card (dropUntil_support_subset p hx))

/--
@isnad1 id=not.3h4v.s6.1a5debb21ad3 from=translated src=- shape=71eeb1c8 vocab=a76112ec
-/
lemma trimStart_start_not_mem {B : Finset V} (hB : Independent (G := G) B)
    (p : GraphPath G) (h : ¬ p.walk.Nil) (hs : p.start ∈ B) :
    (p.trimStart h).start ∉ B :=
  hB.not_mem_of_adj hs (adj_start_trimStart p h).symm

end GraphPath

/-- A component of `G[K \ S]` is `B`-free when it misses surviving terminals.-/
def IsFreeComponent (K B S : Finset V)
    (C : (G.induce ((K \ S : Finset V) : Set V)).ConnectedComponent) : Prop :=
  componentFinset G (K \ S) C ∩ (B \ S) = ∅

/-- `z_B(K-S)`: number of actual induced components of `G[K \ S]` disjoint
from the surviving terminal set `B \ S`.-/
noncomputable def terminalComponentCount (K B S : Finset V) : ℕ :=
  Nat.card { C : (G.induce ((K \ S : Finset V) : Set V)).ConnectedComponent //
    IsFreeComponent (G := G) K B S C }

/-- Terminal cut hypothesis on `(K,B)`.-/
def TerminalHypothesis (K B : Finset V) : Prop :=
  terminalComponentCount (G := G) K B ∅ = 0 ∧
    ∀ S ⊆ K, S.Nonempty →
      terminalComponentCount (G := G) K B S ≤ S.card - 1

/-- Structural original-edge partition used by the all-cograph replacement.
Manuscript `V` is named `W` here to avoid clashing with the vertex type.-/
structure AllCographSides (G : SimpleGraph V) where
  A : Finset V
  B : Finset V
  U : Finset V
  W : Finset V
  m : ℕ
  hAind : Independent (G := G) A
  hBind : Independent (G := G) B
  hAcard : A.card = m
  hBcard : B.card = m
  hm : 2 ≤ m
  hAB : G.IsCompleteBetween (A : Set V) (B : Set V)
  hAU : G.IsCompleteBetween (A : Set V) (U : Set V)
  hUantiB : ∀ u ∈ U, ∀ b ∈ B, ¬ G.Adj u b
  hUantiW : ∀ u ∈ U, ∀ w ∈ W, ¬ G.Adj u w
  hWantiA : ∀ w ∈ W, ∀ a ∈ A, ¬ G.Adj w a
  hUne : U.Nonempty
  hWne : W.Nonempty
  hUcog : IsCograph G U
  hKcog : IsCograph G (B ∪ W)
  hdisjAU : Disjoint A U
  hdisjAW : Disjoint A W
  hdisjBU : Disjoint B U
  hdisjBW : Disjoint B W
  hdisjUW : Disjoint U W
  hcover : A ∪ B ∪ U ∪ W = univ

namespace AllCographSides

variable (P : AllCographSides G)

/--
@isnad1 id=disjoint.0h3v.s5.f1ad3b044e16 from=translated src=- shape=4e36572f vocab=92cfc3de
-/
lemma disjoint_A_B : Disjoint P.A P.B :=
  disjoint_of_completeBetween (G := G) P.hAB

/--
@isnad1 id=nonempty.0h3v.s5.920f06d1b76f from=translated src=- shape=ced2601a vocab=9e91ad3f
-/
lemma K_card_pos : (P.B ∪ P.W).Nonempty := by
  refine union_nonempty.2 (Or.inl (card_pos.mp ?_))
  have hm := P.hm
  have hcard := P.hBcard
  omega

/--
@isnad1 id=nonempty.0h3v.s4.1f84aef5e18b from=translated src=- shape=628ae653 vocab=3155d27b
-/
lemma A_nonempty : P.A.Nonempty := by
  refine card_pos.mp ?_
  have hm := P.hm
  have hcard := P.hAcard
  omega

/--
@isnad1 id=not.2h5v.s6.e7d6fb591638 from=translated src=- shape=151331e7 vocab=712095e8
-/
lemma U_anti_K : ∀ u ∈ P.U, ∀ x ∈ P.B ∪ P.W, ¬ G.Adj u x := by
  intro u hu x hx
  rcases mem_union.1 hx with hB | hW
  · exact P.hUantiB u hu x hB
  · exact P.hUantiW u hu x hW

/--
@isnad1 id=disjoint.0h3v.s5.12cb324d8ce4 from=translated src=- shape=1a8f7165 vocab=111a8f18
-/
lemma disjoint_U_K : Disjoint P.U (P.B ∪ P.W) :=
  disjoint_union_right.2 ⟨P.hdisjBU.symm, P.hdisjUW⟩

/--
@isnad1 id=disjoint.0h3v.s5.8abb868db9c7 from=translated src=- shape=1a8f7165 vocab=3149a509
-/
lemma disjoint_A_K : Disjoint P.A (P.B ∪ P.W) :=
  disjoint_union_right.2 ⟨P.disjoint_A_B, P.hdisjAW⟩

end AllCographSides

/-- An independent set induces an edgeless graph, so components are singletons.
@isnad1 id=eq.1h3v.s4.9ac7a0906a4b from=translated src=- shape=6a71f045 vocab=2bf17bfb
-/
lemma componentCount_of_independent {A : Finset V}
    (h : Independent (G := G) A) : componentCount G A = A.card := by
  refine Finset.induction
    (motive := fun A => Independent (G := G) A → componentCount G A = A.card)
    ?empty ?insert A h
  · intro _h
    simp [componentCount_empty]
  · intro a s ha ih h
    have hs : Independent (G := G) s := h.mono (subset_insert a s)
    have hnocross : ∀ x ∈ ({a} : Finset V), ∀ b ∈ s, ¬ G.Adj x b := by
      intro x hx b hb
      obtain rfl := mem_singleton.1 hx
      exact h (mem_insert_self x s) (mem_insert_of_mem hb)
    have hdisj : Disjoint ({a} : Finset V) s :=
      disjoint_singleton_left.2 ha
    have hunion :=
      Cograph.componentCount_union_of_no_cross (G := G) hdisj hnocross
    have ha1 := componentCount_singleton (G := G) a
    have hins : (insert a s : Finset V) = {a} ∪ s := insert_eq a s
    rw [hins, hunion, ha1, ih hs, card_union_of_disjoint hdisj, card_singleton]

/-- First original cut: delete `A ∪ F(U) ∪ F(K)` and apply 1-toughness together
with the cograph F-cut identities on `U` and on `K = B ∪ W`.
@isnad1 id=le.1h3v.s6.3baa82a6e798 from=translated src=- shape=c5ecaae9 vocab=d2ae64dd
-/
lemma pathCoverNumber_add_le_m (P : AllCographSides G)
    (htough : OneTough G) :
    pathCoverNumber G P.U + pathCoverNumber G (P.B ∪ P.W) ≤ P.m := by
  set K : Finset V := P.B ∪ P.W with hKdef
  set FU := ineligibleSet G P.U with hFUdef
  set FK := ineligibleSet G K with hFKdef
  set S : Finset V := P.A ∪ FU ∪ FK
  have hFU : FU ⊆ P.U := ineligibleSet_subset (G := G) P.U
  have hFK : FK ⊆ K := ineligibleSet_subset (G := G) K
  have hdisjAFU : Disjoint P.A FU :=
    disjoint_of_subset_right hFU P.hdisjAU
  have hdisjAFK : Disjoint P.A FK :=
    disjoint_of_subset_right hFK P.disjoint_A_K
  have hdisjFUFK : Disjoint FU FK :=
    disjoint_of_subset_left hFU
      (disjoint_of_subset_right hFK P.disjoint_U_K)
  have hSU : univ \ S = (P.U \ FU) ∪ (K \ FK) := by
    have hcover : P.A ∪ K ∪ P.U = univ := by
      simpa [K, union_assoc, union_left_comm, union_comm] using P.hcover
    ext x
    constructor
    · intro hx
      have hxuniv : x ∈ univ := (mem_sdiff.1 hx).1
      have hxS : x ∉ S := (mem_sdiff.1 hx).2
      have hxAUK : x ∈ P.A ∪ K ∪ P.U := hcover ▸ hxuniv
      rcases mem_union.1 hxAUK with hAK | hU
      · rcases mem_union.1 hAK with hA | hK
        · exact (hxS (by exact mem_union.2 (Or.inl (mem_union.2 (Or.inl hA))))).elim
        · refine mem_union.2 (Or.inr (mem_sdiff.2 ⟨hK, fun hF =>
            hxS (mem_union.2 (Or.inr hF))⟩))
      · refine mem_union.2 (Or.inl (mem_sdiff.2 ⟨hU, fun hF =>
          hxS (mem_union.2 (Or.inl (mem_union.2 (Or.inr hF))))⟩))
    · intro hx
      refine mem_sdiff.2 ⟨mem_univ x, ?_⟩
      intro hS
      rcases mem_union.1 hx with hxU | hxK
      · have hxU' : x ∈ P.U := (mem_sdiff.1 hxU).1
        have hxFU : x ∉ FU := (mem_sdiff.1 hxU).2
        rcases mem_union.1 hS with hAF | hFK'
        · rcases mem_union.1 hAF with hA | hFU'
          · exact (disjoint_left.1 P.hdisjAU hA hxU').elim
          · exact hxFU hFU'
        · exact (disjoint_left.1 P.disjoint_U_K hxU' (hFK hFK')).elim
      · have hxK' : x ∈ K := (mem_sdiff.1 hxK).1
        have hxFK : x ∉ FK := (mem_sdiff.1 hxK).2
        rcases mem_union.1 hS with hAF | hFK'
        · rcases mem_union.1 hAF with hA | hFU'
          · exact (disjoint_left.1 P.disjoint_A_K hA hxK').elim
          · exact (disjoint_left.1 P.disjoint_U_K (hFU hFU') hxK').elim
        · exact hxFK hFK'
  have hnocross :
      ∀ a ∈ P.U \ FU, ∀ b ∈ K \ FK, ¬ G.Adj a b := by
    intro a ha b hb
    exact P.U_anti_K a (mem_sdiff.1 ha).1 b (mem_sdiff.1 hb).1
  have hdisjRem : Disjoint (P.U \ FU) (K \ FK) :=
    disjoint_of_subset_left sdiff_subset
      (disjoint_of_subset_right sdiff_subset P.disjoint_U_K)
  have hadd :=
    Cograph.componentCount_union_of_no_cross (G := G) hdisjRem hnocross
  have hcU :=
    Cograph.componentCount_sdiff_ineligibleSet_eq_of_canonical (G := G) P.hUcog
  have hcK :=
    Cograph.componentCount_sdiff_ineligibleSet_eq_of_canonical (G := G) P.hKcog
  have hc : componentCount G (univ \ S) =
      FU.card + pathCoverNumber G P.U + FK.card + pathCoverNumber G K := by
    calc componentCount G (univ \ S)
        = componentCount G ((P.U \ FU) ∪ (K \ FK)) := by rw [hSU]
      _ = componentCount G (P.U \ FU) + componentCount G (K \ FK) := hadd
      _ = componentCount G (P.U \ ineligibleSet G P.U) +
            componentCount G (K \ ineligibleSet G K) := by
              simp [hFUdef, hFKdef]
      _ = (ineligibleSet G P.U).card + pathCoverNumber G P.U +
            ((ineligibleSet G K).card + pathCoverNumber G K) := by
              simpa [hKdef] using congrArg₂ (· + ·) hcU hcK
      _ = FU.card + pathCoverNumber G P.U + FK.card + pathCoverNumber G K := by
            simp [hFUdef, hFKdef, add_assoc]
  have hUpos : 1 ≤ pathCoverNumber G P.U :=
    one_le_pathCoverNumber_of_nonempty (G := G) P.hUne
  have hKpos : 1 ≤ pathCoverNumber G K :=
    one_le_pathCoverNumber_of_nonempty (G := G) P.K_card_pos
  have hge : 2 ≤ componentCount G (univ \ S) := by
    have : 2 ≤ FU.card + pathCoverNumber G P.U + FK.card + pathCoverNumber G K := by
      omega
    simpa [hc] using this
  have ht := htough S hge
  have hScard : S.card = P.m + FU.card + FK.card := by
    have h2 : Disjoint (P.A ∪ FU) FK :=
      disjoint_union_left.2 ⟨hdisjAFK, hdisjFUFK⟩
    calc S.card
        = (P.A ∪ FU).card + FK.card := card_union_of_disjoint h2
      _ = P.A.card + FU.card + FK.card := by rw [card_union_of_disjoint hdisjAFU]
      _ = P.m + FU.card + FK.card := by rw [P.hAcard]
  have : componentCount G (univ \ S) ≤ S.card := ht
  have : FU.card + pathCoverNumber G P.U + FK.card + pathCoverNumber G K ≤
      P.m + FU.card + FK.card := by
    simpa [hc, hScard] using this
  omega

/-- Third original cut: delete `B ∪ U ∪ F(W)` leaving the independent set `A`
together with `W \ F(W)`. Toughness yields `p(W) ≤ |U|`.
@isnad1 id=le.2h3v.s5.aec20d534bc3 from=translated src=- shape=80b2b503 vocab=7207d799
-/
lemma pathCoverNumber_W_le_card_U (P : AllCographSides G)
    (htough : OneTough G) (hWcog : IsCograph G P.W) :
    pathCoverNumber G P.W ≤ P.U.card := by
  set FW := ineligibleSet G P.W with hFWdef
  set S : Finset V := P.B ∪ P.U ∪ FW
  have hFW : FW ⊆ P.W := ineligibleSet_subset (G := G) P.W
  have hdisjBU : Disjoint P.B P.U := P.hdisjBU
  have hdisjBFW : Disjoint P.B FW :=
    disjoint_of_subset_right hFW P.hdisjBW
  have hdisjUFW : Disjoint P.U FW :=
    disjoint_of_subset_right hFW P.hdisjUW
  have hSU : univ \ S = P.A ∪ (P.W \ FW) := by
    ext x
    constructor
    · intro hx
      have hxuniv : x ∈ univ := (mem_sdiff.1 hx).1
      have hxS : x ∉ S := (mem_sdiff.1 hx).2
      have hxAll : x ∈ P.A ∪ P.B ∪ P.U ∪ P.W := P.hcover ▸ hxuniv
      rcases mem_union.1 hxAll with hABU | hW
      · rcases mem_union.1 hABU with hAB | hU
        · rcases mem_union.1 hAB with hA | hB
          · exact mem_union.2 (Or.inl hA)
          · exact (hxS (mem_union.2 (Or.inl (mem_union.2 (Or.inl hB))))).elim
        · exact (hxS (mem_union.2 (Or.inl (mem_union.2 (Or.inr hU))))).elim
      · refine mem_union.2 (Or.inr (mem_sdiff.2 ⟨hW, fun hF =>
          hxS (mem_union.2 (Or.inr hF))⟩))
    · intro hx
      refine mem_sdiff.2 ⟨mem_univ x, ?_⟩
      intro hS
      rcases mem_union.1 hx with hA | hW
      · rcases mem_union.1 hS with hBU | hFW'
        · rcases mem_union.1 hBU with hB | hU
          · exact (disjoint_left.1 P.disjoint_A_B hA hB).elim
          · exact (disjoint_left.1 P.hdisjAU hA hU).elim
        · exact (disjoint_left.1 P.hdisjAW hA (hFW hFW')).elim
      · have hxW : x ∈ P.W := (mem_sdiff.1 hW).1
        have hxFW : x ∉ FW := (mem_sdiff.1 hW).2
        rcases mem_union.1 hS with hBU | hFW'
        · rcases mem_union.1 hBU with hB | hU
          · exact (disjoint_left.1 P.hdisjBW hB hxW).elim
          · exact (disjoint_left.1 P.hdisjUW hU hxW).elim
        · exact hxFW hFW'
  have hnocross : ∀ a ∈ P.A, ∀ b ∈ P.W \ FW, ¬ G.Adj a b := by
    intro a ha b hb hadj
    exact P.hWantiA b (mem_sdiff.1 hb).1 a ha hadj.symm
  have hdisjRem : Disjoint P.A (P.W \ FW) :=
    disjoint_of_subset_right sdiff_subset P.hdisjAW
  have hadd :=
    Cograph.componentCount_union_of_no_cross (G := G) hdisjRem hnocross
  have hcA := componentCount_of_independent (G := G) P.hAind
  have hcW :=
    Cograph.componentCount_sdiff_ineligibleSet_eq_of_canonical (G := G) hWcog
  have hc : componentCount G (univ \ S) =
      P.m + FW.card + pathCoverNumber G P.W := by
    calc componentCount G (univ \ S)
        = componentCount G (P.A ∪ (P.W \ FW)) := by rw [hSU]
      _ = componentCount G P.A + componentCount G (P.W \ FW) := hadd
      _ = P.A.card + componentCount G (P.W \ ineligibleSet G P.W) := by
            simp [hcA, hFWdef]
      _ = P.m + ((ineligibleSet G P.W).card + pathCoverNumber G P.W) := by
            rw [P.hAcard, hcW]
      _ = P.m + FW.card + pathCoverNumber G P.W := by
            simp [hFWdef, add_assoc]
  have hge : 2 ≤ componentCount G (univ \ S) := by
    have : 2 ≤ P.m + FW.card + pathCoverNumber G P.W := by
      have hm := P.hm
      have hpos : 1 ≤ pathCoverNumber G P.W :=
        one_le_pathCoverNumber_of_nonempty (G := G) P.hWne
      omega
    simpa [hc] using this
  have ht := htough S hge
  have hScard : S.card = P.m + P.U.card + FW.card := by
    have h2 : Disjoint (P.B ∪ P.U) FW :=
      disjoint_union_left.2 ⟨hdisjBFW, hdisjUFW⟩
    calc S.card
        = (P.B ∪ P.U).card + FW.card := card_union_of_disjoint h2
      _ = P.B.card + P.U.card + FW.card := by rw [card_union_of_disjoint hdisjBU]
      _ = P.m + P.U.card + FW.card := by rw [P.hBcard]
  have : P.m + FW.card + pathCoverNumber G P.W ≤ P.m + P.U.card + FW.card := by
    simpa [hc, hScard] using ht
  omega

/--
@isnad1 id=iscograp.0h3v.s4.ca67cb93619d from=translated src=- shape=8d5d1bfe vocab=688152b9
-/
lemma isCograph_W (P : AllCographSides G) : IsCograph G P.W :=
  fun _ _ _ _ ha hb hc hd hp =>
    P.hKcog (mem_union.2 (Or.inr ha)) (mem_union.2 (Or.inr hb))
      (mem_union.2 (Or.inr hc)) (mem_union.2 (Or.inr hd)) hp

/-- Same cut with the `W`-cograph hypothesis derived from `IsCograph` on
`K = B ∪ W`.
@isnad1 id=le.1h3v.s5.e3d317562f40 from=translated src=- shape=b2be0394 vocab=906f05c0
-/
lemma pathCoverNumber_W_le_card_U_of_sides (P : AllCographSides G)
    (htough : OneTough G) :
    pathCoverNumber G P.W ≤ P.U.card :=
  pathCoverNumber_W_le_card_U P htough (isCograph_W P)

/-- Empty carrier: the unique cover is empty and is `B`-terminal for any `B`.
@isnad1 id=istermin.0h3v.s5.152b88b1fa85 from=translated src=- shape=4902d7c5 vocab=927d25f4
-/
lemma isTerminalCover_empty (B : Finset V) :
    IsTerminalCover (G := G) B (PathCover.singletons (G := G) (∅ : Finset V)) := by
  intro p hp
  have : p ∈ (∅ : Finset V).toList.map (GraphPath.singleton (G := G)) := hp
  simp at this

/--
@isnad1 id=ex.0h3v.s6.cd3ca7ca1d7e from=translated src=- shape=85e68562 vocab=a43be676
-/
lemma pathCoverNumber_empty_terminal (B : Finset V) :
    ∃ pc : PathCover G (∅ : Finset V),
      pc.card = pathCoverNumber G (∅ : Finset V) ∧
        IsTerminalCover (G := G) B pc := by
  refine ⟨PathCover.singletons (G := G) ∅, ?_, isTerminalCover_empty B⟩
  simp [pathCoverNumber_empty, PathCover.singletons_card]

/-- Singleton `{b}` with `b ∈ B` admits a `B`-terminal minimum cover.
@isnad1 id=ex.1h4v.s6.52efa82801e1 from=translated src=- shape=9268ce6a vocab=5f811b18
-/
lemma exists_terminalCover_singleton {B : Finset V} {b : V}
    (hb : b ∈ B) :
    ∃ pc : PathCover G ({b} : Finset V),
      pc.card = pathCoverNumber G ({b} : Finset V) ∧
        IsTerminalCover (G := G) B pc := by
  let pc := PathCover.singletons (G := G) ({b} : Finset V)
  refine ⟨pc, ?_, ?_⟩
  · have hcard : pc.card = 1 := by
      simp [pc, PathCover.singletons_card]
    have hmin : pathCoverNumber G ({b} : Finset V) = 1 :=
      Cograph.pathCoverNumber_singleton (G := G) b
    exact hcard.trans hmin.symm
  · intro p hp
    have : p ∈ ({b} : Finset V).toList.map (GraphPath.singleton (G := G)) := hp
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 this
    have hx' : x = b := mem_singleton.1 (mem_toList.1 hx)
    subst hx'
    exact ⟨hb, hb⟩

/-- Each path of a `B`-terminal cover contributes a distinct `B`-vertex as
its start, so the cover cardinality cannot exceed `|B|`.
@isnad1 id=le.1h5v.s5.9c6e6b2e2c19 from=translated src=- shape=1a6d4098 vocab=561e8389
-/
lemma terminalCover_card_le {K B : Finset V} (pc : PathCover G K)
    (hterm : IsTerminalCover (G := G) B pc) : pc.card ≤ B.card := by
  let starts := pc.paths.map GraphPath.start
  have hlen : starts.length = pc.card := by
    simp [starts, PathCover.card]
  have hnodup : starts.Nodup := by
    rw [List.nodup_map_iff_inj_on pc.nodup_paths]
    intro p hp q hq heq
    by_contra hne
    have hdisj := PathCover.pairwise_disjoint_of_mem_refinement pc.disjoint hp hq hne
    exact (disjoint_left.1 hdisj p.start_mem_support (heq ▸ q.start_mem_support)).elim
  have hsub : starts.toFinset ⊆ B := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hx)
    exact (hterm p hp).1
  have hcard : starts.toFinset.card = starts.length :=
    List.toFinset_card_of_nodup hnodup
  have : starts.toFinset.card ≤ B.card := card_le_card hsub
  omega

/-- Concatenating `B`-terminal covers of a no-cross partition remains
`B`-terminal.
@isnad1 id=istermin.3h7v.s6.ac5f3cccbccd from=translated src=- shape=32a8d071 vocab=5a57eabd
-/
lemma isTerminalCover_unionDisjoint {A C B : Finset V}
    (hdisj : Disjoint A C)
    (pcA : PathCover G A) (pcC : PathCover G C)
    (hA : IsTerminalCover (G := G) B pcA)
    (hC : IsTerminalCover (G := G) B pcC) :
    IsTerminalCover (G := G) B
      (Cograph.PathCover.unionDisjoint hdisj pcA pcC) := by
  intro p hp
  have hp' : p ∈ pcA.paths ++ pcC.paths := hp
  rcases List.mem_append.1 hp' with h | h
  · exact hA p h
  · exact hC p h

end Nikoghosyan
