/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tengoku.NikoghosyanConjecture.Nikoghosyan.Cograph.PathCoverJoin

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/canghaimeng/Nikoghosyan-conjecture@ccc8514d6801, `Nikoghosyan/Cograph/SaturatedJoin.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-!
# Saturated complete-join endpoint identities

For a complete join `U = A ∪ B` with dominant child `A`, that is
`p(A) = p(U) + |B|` and `p(U) ≥ 1`, every eligible vertex of `U` already
lies in `A`, iterated `PathCover.deleteVertex` transports a prescribed
minimum-cover endpoint from `U` to a minimum cover of `A`, and a marked
dominant-child construction transports a prescribed `A`-endpoint forward
to `U`. Consequently `E(U) = E(A)` and `F(U) = B ∪ F(A)`.

The exported existence of some `A`-ended minimum cover is not used as a
substitute for these identities: a desired endpoint remains an endpoint
of one actual minimum cover.
-/

universe u


namespace Nikoghosyan

open scoped Classical
open SimpleGraph Finset

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/--
@isnad1 id=eq.1h3v.s5.93e02580dade from=translated src=- shape=68a34c3b vocab=99e27771
-/
lemma union_sdiff_eq_left_of_disjoint {A B : Finset V} (h : Disjoint A B) :
    (A ∪ B) \ B = A := by
  ext x
  simp only [mem_sdiff, mem_union]
  constructor
  · intro hx
    rcases hx with ⟨hA | hB, hnB⟩
    · exact hA
    · exact (hnB hB).elim
  · intro hxA
    exact ⟨Or.inl hxA, fun hxB => Finset.disjoint_left.1 h hxA hxB⟩

/--
@isnad1 id=eq.4h4v.s6.91a4e5212f2d from=translated src=- shape=794f4914 vocab=a9fc3d29
-/
lemma pathCoverNumber_eq_sub_of_dominant {A B : Finset V}
    (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
    (hdom : B.card < pathCoverNumber G A) :
    pathCoverNumber G (A ∪ B) = pathCoverNumber G A - B.card := by
  have hj := pathCoverNumber_complete_join hAne hBne hAB
  have hBnot : pathCoverNumber G B ≤ A.card := by
    by_contra h
    exact not_both_dominant hdom (Nat.lt_of_not_ge h)
  have hq : 1 ≤ pathCoverNumber G A - B.card := by omega
  have hmax :
      max 1 (max (pathCoverNumber G A - B.card)
        (pathCoverNumber G B - A.card)) =
      pathCoverNumber G A - B.card := by
    simp [Nat.sub_eq_zero_of_le hBnot, max_eq_right hq]
  exact hj.trans hmax

/--
@isnad1 id=eq.4h4v.s6.ac6853d189fb from=translated src=- shape=c286e226 vocab=454558de
-/
lemma pathCoverNumber_add_card_of_dominant {A B : Finset V}
    (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
    (hdom : B.card < pathCoverNumber G A) :
    pathCoverNumber G A =
      pathCoverNumber G (A ∪ B) + B.card := by
  have h := pathCoverNumber_eq_sub_of_dominant hAne hBne hAB hdom
  omega

/-- No eligible vertex of a saturated join `A ∪ B` can lie in the
non-dominant side `B`.
@isnad1 id=false.6h5v.s6.ff12e16defeb from=translated src=- shape=2d7d2a92 vocab=0d840b57
-/
lemma not_eligible_mem_B_of_dominant {A B : Finset V} {x : V}
    (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
    (hdom : B.card < pathCoverNumber G A)
    (hxB : x ∈ B) (hE : Eligible G (A ∪ B) x) : False := by
  have hdisj := disjoint_of_completeBetween hAB
  have hsub : B ⊆ A ∪ B := subset_union_right
  have hle :=
    pathCoverNumber_sdiff_le_of_eligible (G := G) (U := A ∪ B) (X := B)
      hsub hxB hE
  have hEq : (A ∪ B) \ B = A := union_sdiff_eq_left_of_disjoint hdisj
  have hsat := pathCoverNumber_add_card_of_dominant hAne hBne hAB hdom
  have hpos : 1 ≤ B.card := Nat.succ_le_of_lt (card_pos.2 hBne)
  rw [hEq] at hle
  omega

/--
@isnad1 id=mem.5h5v.s6.f0975221b40a from=translated src=- shape=3d4835ac vocab=0d840b57
-/
lemma eligible_mem_left_of_dominant {A B : Finset V} {x : V}
    (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
    (hdom : B.card < pathCoverNumber G A)
    (hE : Eligible G (A ∪ B) x) : x ∈ A := by
  have hxU : x ∈ A ∪ B := hE.mem
  rcases mem_union.1 hxU with hxA | hxB
  · exact hxA
  · exact (not_eligible_mem_B_of_dominant hAne hBne hAB hdom hxB hE).elim

namespace PathCover

/--
@isnad1 id=iff.1h6v.s5.e5dc09f05231 from=translated src=- shape=5dd493ac vocab=9bc52903
-/
lemma cast_IsEndpoint {U W : Finset V} (pc : PathCover G U) (h : U = W) {x : V} :
    (pc.cast h).IsEndpoint x ↔ pc.IsEndpoint x := by
  subst h
  rfl

/-- Replace one cover path by another path with the same support.-/
noncomputable def replacePath_sat {U : Finset V} (pc : PathCover G U)
    {p : GraphPath G} (hp : p ∈ pc.paths) (r : GraphPath G)
    (hr : r.support = p.support) : PathCover G U where
  paths := (pc.paths.filter fun q => decide (q ≠ p)) ++ [r]
  disjoint := by
    refine List.pairwise_append.mpr ⟨List.Pairwise.filter _ pc.disjoint,
      List.pairwise_singleton _ _, ?_⟩
    intro s hs t ht
    have ht' : t = r := List.mem_singleton.1 ht
    subst ht'
    have hs0 := List.mem_filter.1 hs
    have hsp : s ≠ p := of_decide_eq_true hs0.2
    have hdisj : Disjoint s.support p.support :=
      pairwise_disjoint_of_mem pc.disjoint hs0.1 hp hsp
    simpa [hr] using hdisj
  mem_iff := by
    intro x
    constructor
    · intro hx
      obtain ⟨q, hq, hxq⟩ := (pc.mem_iff x).1 hx
      by_cases hqp : q = p
      · subst hqp
        refine ⟨r, List.mem_append.mpr (Or.inr (List.mem_singleton.2 rfl)), ?_⟩
        rwa [hr]
      · exact ⟨q, List.mem_append.mpr (Or.inl (List.mem_filter.2 ⟨hq, decide_eq_true hqp⟩)),
          hxq⟩
    · intro ⟨q, hq, hxq⟩
      rcases List.mem_append.1 hq with hL | hR
      · have hq' := List.mem_filter.1 hL
        exact (pc.mem_iff x).2 ⟨q, hq'.1, hxq⟩
      · have : q = r := List.mem_singleton.1 hR
        subst this
        have hx' : x ∈ p.support := by rwa [← hr]
        exact (pc.mem_iff x).2 ⟨p, hp, hx'⟩

/--
@isnad1 id=eq.2h6v.s6.5d654c9092b1 from=translated src=- shape=3347f1a9 vocab=e4b074cc
-/
lemma replacePath_sat_card {U : Finset V} (pc : PathCover G U)
    {p : GraphPath G} (hp : p ∈ pc.paths) (r : GraphPath G)
    (hr : r.support = p.support) :
    (pc.replacePath_sat hp r hr).card = pc.card := by
  have hlen := length_filter_ne_of_mem_nodup (a := p) (l := pc.paths) hp pc.nodup_paths
  have hpos : 1 ≤ pc.paths.length := Nat.succ_le_of_lt (List.length_pos_of_mem hp)
  simp only [replacePath_sat, PathCover.card, List.length_append, List.length_cons,
    List.length_nil]
  omega

/--
@isnad1 id=or.3h7v.s7.79aa5adb1e43 from=translated src=- shape=216ea912 vocab=c1128fa3
-/
lemma replacePath_sat_mem_paths {U : Finset V} (pc : PathCover G U)
    {p : GraphPath G} (hp : p ∈ pc.paths) (r : GraphPath G)
    (hr : r.support = p.support) {s : GraphPath G}
    (hs : s ∈ (pc.replacePath_sat hp r hr).paths) :
    s = r ∨ s ∈ pc.paths ∧ s ≠ p := by
  rcases List.mem_append.1 hs with hL | hR
  · have hs0 := List.mem_filter.1 hL
    exact Or.inr ⟨hs0.1, of_decide_eq_true hs0.2⟩
  · exact Or.inl (List.mem_singleton.1 hR)

/--
@isnad1 id=mem.2h6v.s6.c078ed8e378f from=translated src=- shape=e2a5ce0f vocab=c1128fa3
-/
lemma replacePath_sat_self_mem {U : Finset V} (pc : PathCover G U)
    {p : GraphPath G} (hp : p ∈ pc.paths) (r : GraphPath G)
    (hr : r.support = p.support) :
    r ∈ (pc.replacePath_sat hp r hr).paths :=
  List.mem_append.mpr (Or.inr (List.mem_singleton.2 rfl))

/--
@isnad1 id=eq.0h3v.s4.a5d1e8b1234c from=translated src=- shape=13ae0f74 vocab=c30c1ddf
-/
lemma GraphPath.start_reverse (p : GraphPath G) : p.reverse.start = p.finish :=
  rfl

/--
@isnad1 id=eq.0h3v.s4.5911ed78d24e from=translated src=- shape=13ae0f74 vocab=c30c1ddf
-/
lemma GraphPath.finish_reverse (p : GraphPath G) : p.reverse.finish = p.start :=
  rfl

/-- Iterate single-vertex deletion, keeping a prescribed surviving endpoint
and paying at most one extra path per deleted vertex.
@isnad1 id=ex.3h6v.s7.58d116035b58 from=translated src=- shape=37badd04 vocab=bba20e67
-/
lemma exists_deleteFinset_keepEndpoint {U S : Finset V}
    (pc : PathCover G U) (hS : S ⊆ U) {x : V}
    (hx : pc.IsEndpoint x) (hxS : x ∉ S) :
    ∃ pc' : PathCover G (U \ S),
      pc'.card ≤ pc.card + S.card ∧ pc'.IsEndpoint x := by
  induction S using Finset.induction generalizing U pc with
  | empty =>
    refine ⟨pc.cast (by simp), ?_, ?_⟩
    · simp [PathCover.cast_card]
    · exact (cast_IsEndpoint pc (by simp)).2 hx
  | insert b S hb ih =>
    have hbU : b ∈ U := hS (mem_insert_self b S)
    have hSsub : S ⊆ U.erase b := by
      intro y hy
      exact mem_erase.2 ⟨fun hby => hb (hby ▸ hy), hS (mem_insert_of_mem hy)⟩
    have hxne : x ≠ b := fun hxb => hxS (by simp [hxb])
    have hx' : (pc.deleteVertex b).IsEndpoint x :=
      IsEndpoint_deleteVertex pc hx hxne
    have hxS' : x ∉ S := fun h => hxS (mem_insert_of_mem h)
    obtain ⟨pc1, hcard1, hend1⟩ :=
      ih (U := U.erase b) (pc.deleteVertex b) hSsub hx' hxS'
    have hEq : U.erase b \ S = U \ insert b S := by
      rw [sdiff_insert, erase_sdiff_distrib, erase_eq_of_notMem hb]
    refine ⟨pc1.cast hEq, ?_, ?_⟩
    · have hdv := pc.card_deleteVertex_le b
      have hcard := card_insert_of_notMem (s := S) hb
      rw [PathCover.cast_card]
      omega
    · exact (cast_IsEndpoint pc1 hEq).2 hend1

/--
@isnad1 id=ex.2h5v.s6.b5b2401e05d7 from=translated src=- shape=d9a7a78d vocab=b2be4c67
-/
lemma exists_other_path_sat {U : Finset V} (pc : PathCover G U)
    {p : GraphPath G} (_hp : p ∈ pc.paths) (h2 : 2 ≤ pc.card) :
    ∃ q, q ∈ pc.paths ∧ q ≠ p := by
  obtain ⟨p0, q0, hp0, hq0, hne⟩ := pc.exists_two_distinct h2
  by_cases h : p = p0
  · refine ⟨q0, hq0, ?_⟩
    intro h'
    exact hne (h.symm.trans h'.symm)
  · exact ⟨p0, hp0, fun hp0p => h hp0p.symm⟩

/-- Merge the marked `A`-ended chain on the left with another cover path
through an unused `B`-vertex. The marked start is preserved.
@isnad1 id=ex.7h9v.s8.5b7be38ff65c from=translated src=- shape=5987b360 vocab=8ca501d6
-/
lemma exists_marked_splice_two_through {A B U : Finset V} {b x : V}
    {p : GraphPath G}
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
    (pc : PathCover G U) (hp : p ∈ pc.paths) (hstart : p.start = x)
    (h2 : 2 ≤ pc.card)
    (hend : ∀ q ∈ pc.paths, q.start ∈ A ∧ q.finish ∈ A)
    (hb : b ∈ B) (hbU : b ∉ U) :
    ∃ (pc' : PathCover G (insert b U)) (p' : GraphPath G),
      pc'.card = pc.card - 1 ∧
        p' ∈ pc'.paths ∧ p'.start = x ∧
          (∀ q ∈ pc'.paths, q.start ∈ A ∧ q.finish ∈ A) := by
  obtain ⟨q, hq, hne⟩ := pc.exists_other_path_sat hp h2
  have hpb : b ∉ p.support := fun h => hbU (pc.support_subset hp h)
  have hqb : b ∉ q.support := fun h => hbU (pc.support_subset hq h)
  obtain ⟨r, hr, hs, hf⟩ :=
    exists_spliceABA hAB p b q (hend p hp).2 hb (hend q hq).1 hpb hqb
      (pairwise_disjoint_of_mem pc.disjoint hp hq hne.symm)
  refine ⟨pc.spliceTwoInsert hp hq hne.symm b hbU r hr,
    r, pc.spliceTwoInsert_card hp hq hne.symm b hbU r hr, ?_, ?_, ?_⟩
  · exact List.mem_append.mpr (Or.inr (List.mem_singleton.2 rfl))
  · exact hs.trans hstart
  · intro s hsmem
    rcases pc.spliceTwoInsert_mem_paths hp hq hne.symm b hbU r hr hsmem with hseq | ⟨hspc, _, _⟩
    · subst hseq
      rw [hs, hf]
      exact ⟨(hend p hp).1, (hend q hq).2⟩
    · exact hend s hspc

end PathCover

/-- Deleting the non-dominant side from a witnessing minimum `U`-cover yields
a minimum `A`-cover that retains every prescribed surviving endpoint.
@isnad1 id=ex.5h5v.s6.2a307e84714e from=translated src=- shape=39b8c610 vocab=e26abe35
-/
lemma exists_min_cover_left_of_dominant_endpoint {A B : Finset V} {x : V}
    (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
    (hdom : B.card < pathCoverNumber G A)
    (hE : Eligible G (A ∪ B) x) :
    ∃ pc : PathCover G A,
      pc.card = pathCoverNumber G A ∧ pc.IsEndpoint x := by
  have hEkeep := hE
  obtain ⟨pcU, hU, p, hp, hxend⟩ := hE
  have hxA := eligible_mem_left_of_dominant hAne hBne hAB hdom hEkeep
  have hdisj := disjoint_of_completeBetween hAB
  have hxB : x ∉ B := fun hxB => Finset.disjoint_left.1 hdisj hxA hxB
  have hBsub : B ⊆ A ∪ B := subset_union_right
  obtain ⟨pc1, hcard1, hend1⟩ :=
    PathCover.exists_deleteFinset_keepEndpoint (U := A ∪ B) (S := B)
      pcU hBsub ⟨p, hp, hxend⟩ hxB
  have hEq : (A ∪ B) \ B = A := union_sdiff_eq_left_of_disjoint hdisj
  let pcA : PathCover G A := pc1.cast hEq
  have hsat := pathCoverNumber_add_card_of_dominant hAne hBne hAB hdom
  have hcard : pcA.card ≤ pathCoverNumber G A := by
    rw [PathCover.cast_card]
    omega
  have hmin : pcA.card = pathCoverNumber G A := by
    have hle := pathCoverNumber_le (G := G) pcA
    omega
  exact ⟨pcA, hmin, (PathCover.cast_IsEndpoint pc1 hEq).2 hend1⟩

/--
@isnad1 id=eligible.5h5v.s6.2c6d6268b579 from=translated src=- shape=fa48786b vocab=c66a5d9a
-/
lemma eligible_left_of_dominant {A B : Finset V} {x : V}
    (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
    (hdom : B.card < pathCoverNumber G A)
    (hE : Eligible G (A ∪ B) x) : Eligible G A x := by
  obtain ⟨pc, hpc, hend⟩ :=
    exists_min_cover_left_of_dominant_endpoint hAne hBne hAB hdom hE
  obtain ⟨p, hp, hx⟩ := hend
  exact ⟨pc, hpc, p, hp, hx⟩

/--
@isnad1 id=ex.3h7v.s7.a9c3332af635 from=translated src=- shape=225f3c8b vocab=3f85a262
-/
lemma exists_orientStart_marked {A U : Finset V} {x : V}
    (pc : PathCover G U) {p : GraphPath G} (hp : p ∈ pc.paths)
    (hx : x = p.start ∨ x = p.finish)
    (hend : ∀ q ∈ pc.paths, q.start ∈ A ∧ q.finish ∈ A) :
    ∃ (pc' : PathCover G U) (p' : GraphPath G),
      pc'.card = pc.card ∧
        p' ∈ pc'.paths ∧ p'.start = x ∧ p'.support = p.support ∧
          (∀ q ∈ pc'.paths, q.start ∈ A ∧ q.finish ∈ A) := by
  by_cases hs : x = p.start
  · exact ⟨pc, p, rfl, hp, hs.symm, rfl, hend⟩
  · have hf : x = p.finish := hx.resolve_left hs
    let r := p.reverse
    have hr : r.support = p.support := GraphPath.support_reverse p
    refine ⟨pc.replacePath_sat hp r hr, r, pc.replacePath_sat_card hp r hr,
      pc.replacePath_sat_self_mem hp r hr, ?_, hr, ?_⟩
    · simp [r, PathCover.GraphPath.start_reverse, hf]
    · intro q hq
      rcases pc.replacePath_sat_mem_paths hp r hr hq with hqr | ⟨hspc, _⟩
      · subst hqr
        rw [PathCover.GraphPath.start_reverse, PathCover.GraphPath.finish_reverse]
        exact ⟨(hend p hp).2, (hend p hp).1⟩
      · exact hend q hspc

/-- Dominant-child construction starting from a prescribed minimum `A`-cover
endpoint: the marked chain is always the left splice operand, so its start
survives every insertion.
@isnad1 id=ex.3h5v.s7.ffb55a4721b4 from=translated src=- shape=b4ae10e6 vocab=a3375c59
-/
lemma exists_pathCover_complete_join_dominant_marked {A B : Finset V} {x : V}
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
    (hdom : B.card < pathCoverNumber G A)
    (hE : Eligible G A x) :
    ∃ pc : PathCover G (A ∪ B),
      pc.card = pathCoverNumber G A - B.card ∧ pc.IsEndpoint x ∧
        (∀ p ∈ pc.paths, p.start ∈ A ∧ p.finish ∈ A) := by
  obtain ⟨pc0, h0, p0, hp0, hxend⟩ := hE
  have hend0 : ∀ q ∈ pc0.paths, q.start ∈ A ∧ q.finish ∈ A := by
    intro q hq
    exact ⟨pc0.support_subset hq q.start_mem_support,
      pc0.support_subset hq q.finish_mem_support⟩
  obtain ⟨pc0o, p0o, hcard0o, hp0o, hstart0, _, hend0o⟩ :=
    exists_orientStart_marked (A := A) pc0 hp0 hxend hend0
  have aux :
      ∀ (k : ℕ) (S : Finset V) (pc : PathCover G (A ∪ S)) (p : GraphPath G),
        S ⊆ B → (B \ S).card = k →
          pc.card = pathCoverNumber G A - S.card →
            p ∈ pc.paths → p.start = x →
              (∀ q ∈ pc.paths, q.start ∈ A ∧ q.finish ∈ A) →
                ∃ (pc' : PathCover G (A ∪ B)),
                  pc'.card = pathCoverNumber G A - B.card ∧
                    pc'.IsEndpoint x ∧
                      (∀ q ∈ pc'.paths, q.start ∈ A ∧ q.finish ∈ A) := by
    intro k
    induction k with
    | zero =>
      intro S pc p hS hk hcard hp hstart hend
      have hBS : B \ S = ∅ := Finset.card_eq_zero.mp hk
      have hBeq : S = B :=
        subset_antisymm hS (sdiff_eq_empty_iff_subset.mp hBS)
      subst hBeq
      exact ⟨pc, hcard, ⟨p, hp, Or.inl hstart.symm⟩, hend⟩
    | succ k ih =>
      intro S pc p hS hk hcard hp hstart hend
      have hne : (B \ S).Nonempty :=
        card_pos.mp (by omega : 0 < (B \ S).card)
      obtain ⟨b, hb⟩ := hne
      have hbB : b ∈ B := (mem_sdiff.1 hb).1
      have hbS : b ∉ S := (mem_sdiff.1 hb).2
      have hdisjAB := disjoint_of_completeBetween hAB
      have hbU : b ∉ A ∪ S := by
        intro h
        rcases mem_union.1 h with hA | hS'
        · exact Finset.disjoint_left.1 hdisjAB hA hbB
        · exact hbS hS'
      have hsum : S.card + (B \ S).card = B.card := by
        rw [← card_union_of_disjoint, union_sdiff_of_subset hS]
        exact disjoint_sdiff
      have h2 : 2 ≤ pc.card := by omega
      obtain ⟨pc1, p1, hcard1, hp1, hstart1, hend1⟩ :=
        PathCover.exists_marked_splice_two_through (x := x) (p := p)
          hAB pc hp hstart h2 hend hbB hbU
      have hU : insert b (A ∪ S) = A ∪ insert b S := by
        ext z
        simp [mem_insert, mem_union]
      let pc1' : PathCover G (A ∪ insert b S) := pc1.cast hU
      have hS' : insert b S ⊆ B := insert_subset hbB hS
      have hrem : B \ insert b S = (B \ S).erase b := sdiff_insert B S b
      have hk' : (B \ insert b S).card = k := by
        rw [hrem, card_erase_of_mem hb, hk]
        omega
      have hcard' : pc1'.card = pathCoverNumber G A - (insert b S).card := by
        rw [PathCover.cast_card, hcard1, hcard, card_insert_of_notMem hbS]
        omega
      have hp1' : p1 ∈ pc1'.paths := by
        rw [PathCover.cast_paths pc1 hU]
        exact hp1
      have hend1' : ∀ q ∈ pc1'.paths, q.start ∈ A ∧ q.finish ∈ A := by
        intro q hq
        rw [PathCover.cast_paths pc1 hU] at hq
        exact hend1 q hq
      exact ih (insert b S) pc1' p1 hS' hk' hcard' hp1' hstart1 hend1'
  have hA : A ∪ (∅ : Finset V) = A := union_empty A
  let pc0' : PathCover G (A ∪ ∅) := pc0o.cast hA.symm
  have hcard0 : pc0'.card = pathCoverNumber G A - (∅ : Finset V).card := by
    rw [PathCover.cast_card, hcard0o, h0, card_empty, Nat.sub_zero]
  have hp0' : p0o ∈ pc0'.paths := by
    rw [PathCover.cast_paths pc0o hA.symm]
    exact hp0o
  have hend0' : ∀ q ∈ pc0'.paths, q.start ∈ A ∧ q.finish ∈ A := by
    intro q hq
    rw [PathCover.cast_paths pc0o hA.symm] at hq
    exact hend0o q hq
  exact aux B.card ∅ pc0' p0o (empty_subset B) (by simp) hcard0 hp0' hstart0 hend0'

/--
@isnad1 id=eligible.5h5v.s6.6bff2183197a from=translated src=- shape=21a38054 vocab=c66a5d9a
-/
lemma eligible_of_dominant_left {A B : Finset V} {x : V}
    (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
    (hdom : B.card < pathCoverNumber G A)
    (hE : Eligible G A x) : Eligible G (A ∪ B) x := by
  obtain ⟨pc, hpc, hend, _⟩ :=
    exists_pathCover_complete_join_dominant_marked hAB hdom hE
  have hmin : pc.card = pathCoverNumber G (A ∪ B) := by
    have hj := pathCoverNumber_eq_sub_of_dominant hAne hBne hAB hdom
    omega
  obtain ⟨p, hp, hx⟩ := hend
  exact ⟨pc, hmin, p, hp, hx⟩

/--
@isnad1 id=iff.4h5v.s6.178dc19ca482 from=translated src=- shape=ef43aa86 vocab=c66a5d9a
-/
lemma eligible_complete_join_dominant_iff {A B : Finset V} {x : V}
    (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
    (hdom : B.card < pathCoverNumber G A) :
    Eligible G (A ∪ B) x ↔ Eligible G A x :=
  ⟨eligible_left_of_dominant hAne hBne hAB hdom,
    eligible_of_dominant_left hAne hBne hAB hdom⟩

/-- Saturated complete join: eligible vertices of the union are exactly the
eligible vertices of the dominant child.
@isnad1 id=eq.4h4v.s6.035157e21eb1 from=translated src=- shape=8c12be52 vocab=cd1210a9
-/
lemma eligibleSet_complete_join_dominant {A B : Finset V}
    (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
    (hdom : B.card < pathCoverNumber G A) :
    eligibleSet G (A ∪ B) = eligibleSet G A := by
  ext x
  constructor
  · intro hx
    rw [mem_eligibleSet_iff] at hx
    have hEA := eligible_left_of_dominant hAne hBne hAB hdom hx.2
    exact (mem_eligibleSet_iff (G := G)).2 ⟨hEA.mem, hEA⟩
  · intro hx
    rw [mem_eligibleSet_iff] at hx
    have hEU := eligible_of_dominant_left hAne hBne hAB hdom hx.2
    exact (mem_eligibleSet_iff (G := G)).2 ⟨hEU.mem, hEU⟩

/-- Saturated complete join: ineligible vertices are the whole non-dominant
side together with the ineligible vertices of the dominant child.
@isnad1 id=eq.4h4v.s6.80f9dc4f8015 from=translated src=- shape=2b4b033e vocab=6b843612
-/
lemma ineligibleSet_complete_join_dominant {A B : Finset V}
    (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
    (hdom : B.card < pathCoverNumber G A) :
    ineligibleSet G (A ∪ B) = B ∪ ineligibleSet G A := by
  ext x
  constructor
  · intro hx
    rw [mem_ineligibleSet_iff] at hx
    rcases mem_union.1 hx.1 with hxA | hxB
    · refine mem_union.2 (Or.inr ?_)
      rw [mem_ineligibleSet_iff]
      refine ⟨hxA, ?_⟩
      intro hEA
      exact hx.2 (eligible_of_dominant_left hAne hBne hAB hdom hEA)
    · exact mem_union.2 (Or.inl hxB)
  · intro hx
    rw [mem_ineligibleSet_iff]
    rcases mem_union.1 hx with hxB | hxA
    · refine ⟨mem_union.2 (Or.inr hxB), ?_⟩
      intro hEU
      exact not_eligible_mem_B_of_dominant hAne hBne hAB hdom hxB hEU
    · rw [mem_ineligibleSet_iff] at hxA
      refine ⟨mem_union.2 (Or.inl hxA.1), ?_⟩
      intro hEU
      exact hxA.2 (eligible_left_of_dominant hAne hBne hAB hdom hEU)

/--
@isnad1 id=eq.4h4v.s6.3aeba85450f2 from=translated src=- shape=578e4d79 vocab=2614b8f7
-/
lemma sdiff_ineligibleSet_complete_join_dominant {A B : Finset V}
    (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hAB : G.IsCompleteBetween (A : Set V) (B : Set V))
    (hdom : B.card < pathCoverNumber G A) :
    (A ∪ B) \ ineligibleSet G (A ∪ B) = A \ ineligibleSet G A := by
  have hF := ineligibleSet_complete_join_dominant hAne hBne hAB hdom
  have hdisj := disjoint_of_completeBetween hAB
  ext x
  constructor
  · intro hx
    have hxAB : x ∈ A ∪ B := (mem_sdiff.1 hx).1
    have hnot : x ∉ ineligibleSet G (A ∪ B) := (mem_sdiff.1 hx).2
    have hnot' : x ∉ B ∪ ineligibleSet G A := by rwa [hF] at hnot
    have hxA : x ∈ A := by
      rcases mem_union.1 hxAB with hxA | hxB
      · exact hxA
      · exact (hnot' (mem_union.2 (Or.inl hxB))).elim
    refine mem_sdiff.2 ⟨hxA, ?_⟩
    intro hxF
    exact hnot' (mem_union.2 (Or.inr hxF))
  · intro hx
    have hxA : x ∈ A := (mem_sdiff.1 hx).1
    have hxF : x ∉ ineligibleSet G A := (mem_sdiff.1 hx).2
    refine mem_sdiff.2 ⟨mem_union.2 (Or.inl hxA), ?_⟩
    intro hmem
    have hmem' : x ∈ B ∪ ineligibleSet G A := by rwa [hF] at hmem
    rcases mem_union.1 hmem' with hxB | hxFA
    · exact Finset.disjoint_left.1 hdisj hxA hxB
    · exact hxF hxFA

end Nikoghosyan
