/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tengoku.NikoghosyanConjecture.Nikoghosyan.Cograph.CycleProfileSegments

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/canghaimeng/Nikoghosyan-conjecture@ccc8514d6801, `Nikoghosyan/Cograph/ProfileEndpoints.lean`: removed 2 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-!
# Exact spanning-path neighbourhood and incompatible saturated profiles

Manuscript `prof:prop:endpoints` and `prof:prop:incompatible`.

From one actual original-edge cycle on `U` and a saturated nonempty
`A ⊆ U` whose remainder is a cograph, every vertex of `U \ S_A` is the
start of an original spanning `U`-path that ends in `A`. The reverse
inclusion is the already-checked both-endpoints cut. Incompatible
profiles then follow by neighbourhood plus canonical-container
maximality; `A` and `B` need not be disjoint.
-/

universe u


namespace Nikoghosyan
namespace Cograph

open scoped Classical
open SimpleGraph Finset
open Nikoghosyan.GraphPath

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/--
@isnad1 id=le.1h6v.s6.9e9706aeb7ec from=translated src=- shape=e2e5617f vocab=a0eee1f1
-/
lemma support_subset_of_sdiff {U A : Finset V} (pc : PathCover G (U \ A))
    {Q : GraphPath G} (hQ : Q ∈ pc.paths) :
    Q.support ⊆ U :=
  (pc.support_subset hQ).trans sdiff_subset

/--
@isnad1 id=disjoint.1h5v.s5.fb51c421844d from=translated src=- shape=d30d37d4 vocab=7e510f37
-/
lemma disjoint_of_complement {U : Finset V} {Q r : GraphPath G}
    (hr : r.support = U \ Q.support) :
    Disjoint Q.support r.support := by
  refine disjoint_left.2 ?_
  intro x hxQ hxR
  have hx' : x ∈ U \ Q.support := by simpa [hr] using hxR
  exact (mem_sdiff.1 hx').2 hxQ

/--
@isnad1 id=eq.2h5v.s6.53c0ef686788 from=translated src=- shape=10658540 vocab=c4e32487
-/
lemma union_of_complement {U : Finset V} {Q r : GraphPath G}
    (hr : r.support = U \ Q.support) (hQ : Q.support ⊆ U) :
    Q.support ∪ r.support = U := by
  rw [hr]
  exact union_sdiff_of_subset hQ

/--
@isnad1 id=ne.2h6v.s6.fd87fabc1871 from=translated src=- shape=6be0ee81 vocab=6cd2bd8a
-/
lemma ne_complement_start {U : Finset V} {Q r : GraphPath G} {b : V}
    (hr : r.support = U \ Q.support) (hbQ : b ∈ Q.support) :
    b ≠ r.start := by
  intro heq
  have hbR : b ∈ r.support := by simpa [heq] using r.start_mem_support
  have hb' : b ∈ U \ Q.support := by simpa [hr] using hbR
  exact (mem_sdiff.1 hb').2 hbQ

/--
@isnad1 id=ne.2h6v.s6.d6d79cbd195f from=translated src=- shape=6be0ee81 vocab=7d1b3f1f
-/
lemma ne_complement_finish {U : Finset V} {Q r : GraphPath G} {b : V}
    (hr : r.support = U \ Q.support) (hbQ : b ∈ Q.support) :
    b ≠ r.finish := by
  intro heq
  have hbR : b ∈ r.support := by simpa [heq] using r.finish_mem_support
  have hb' : b ∈ U \ Q.support := by simpa [hr] using hbR
  exact (mem_sdiff.1 hb').2 hbQ

/--
@isnad1 id=eq.1h3v.s5.c3f183e594b2 from=translated src=- shape=38d3c260 vocab=f3470725
-/
lemma support_card_eq_one_of_not_two {Q : GraphPath G}
    (h2 : ¬ 2 ≤ Q.support.card) : Q.support.card = 1 := by
  have hpos : 1 ≤ Q.support.card := by
    rw [GraphPath.card_support]
    exact Nat.succ_le_succ (Nat.zero_le _)
  omega

/--
@isnad1 id=nil.1h3v.s5.ed356e56f8f3 from=translated src=- shape=bfa58fb3 vocab=49a8d959
-/
lemma nil_of_support_card_eq_one {Q : GraphPath G}
    (h1 : Q.support.card = 1) : Q.walk.Nil := by
  have hlen : Q.walk.length = 0 := by
    have := GraphPath.card_support Q
    omega
  exact Walk.length_eq_zero_iff.1 hlen

/-- Splice a leftover singleton `Q = {b}` to `r.reverse` along the
predecessor original seam.
@isnad1 id=ex.6h7v.s7.50c681c759b8 from=translated src=- shape=cd2c673e vocab=0c5569fa
-/
lemma spanning_of_singleton_leftover {U A : Finset V} {Q r : GraphPath G} {b : V}
    (h1 : Q.support.card = 1) (hbQ : b ∈ Q.support)
    (hr : r.support = U \ Q.support) (hQU : Q.support ⊆ U)
    (hpred : G.Adj r.finish Q.start) (rstartA : r.start ∈ A) :
    ∃ a ∈ A, SpanningPathCompatible (G := G) U b a := by
  have hnil : Q.walk.Nil := nil_of_support_card_eq_one h1
  have hsing : Q.support = {Q.start} :=
    GraphPath.support_eq_singleton_of_nil Q hnil
  have hbEq : b = Q.start := by
    have : b ∈ ({Q.start} : Finset V) := by simpa [hsing] using hbQ
    exact mem_singleton.1 this
  have hfin : Q.finish = Q.start :=
    ((GraphPath.nil_iff_start_eq_finish Q).1 hnil).symm
  have hd : Disjoint Q.support r.reverse.support := by
    simpa [GraphPath.support_reverse] using disjoint_of_complement hr
  have hadj : G.Adj Q.finish r.reverse.start := by
    have h2 : r.reverse.start = r.finish := rfl
    rw [hfin, h2]
    exact hpred.symm
  let s := Q.splice r.reverse hadj hd
  have hst : s.start = b := by
    change Q.start = b
    exact hbEq.symm
  have hfn : s.finish = r.start := rfl
  have hsup : s.support = U := by
    rw [show s.support = Q.support ∪ r.reverse.support from
        support_splice Q r.reverse hadj hd,
      GraphPath.support_reverse]
    exact union_of_complement hr hQU
  have hne : s.start ≠ s.finish := by
    rw [hst, hfn]
    exact ne_complement_start hr hbQ
  refine ⟨r.start, rstartA, ?_⟩
  have hR0 := spanningPathCompatible_of_path s hne
  rw [← hsup, ← hst, ← hfn]
  exact hR0

/-- Local `Q`-path from `b` to `Q.start`, spliced to `r.reverse` along the
predecessor original seam. The resulting `U`-path ends at `r.start ∈ A`.
@isnad1 id=ex.7h8v.s7.26385d402204 from=translated src=- shape=ca2e25fb vocab=af095697
-/
lemma spanning_of_pred_seam {U A : Finset V} {Q r q : GraphPath G} {b : V}
    (hq : q.support = Q.support) (hstq : q.start = b)
    (hfinq : q.finish = Q.start)
    (hr : r.support = U \ Q.support) (hQU : Q.support ⊆ U)
    (hpred : G.Adj r.finish Q.start) (rstartA : r.start ∈ A) :
    ∃ a ∈ A, SpanningPathCompatible (G := G) U b a := by
  have hbQ : b ∈ Q.support := by
    have : q.start ∈ q.support := q.start_mem_support
    simpa [hstq, hq] using this
  have hd : Disjoint q.support r.reverse.support := by
    simpa [hq, GraphPath.support_reverse] using disjoint_of_complement hr
  have hadj : G.Adj q.finish r.reverse.start := by
    have h2 : r.reverse.start = r.finish := rfl
    rw [hfinq, h2]
    exact hpred.symm
  let s := q.splice r.reverse hadj hd
  have hst : s.start = b := by
    change q.start = b
    exact hstq
  have hfn : s.finish = r.start := rfl
  have hsup : s.support = U := by
    rw [show s.support = q.support ∪ r.reverse.support from
        support_splice q r.reverse hadj hd,
      hq, GraphPath.support_reverse]
    exact union_of_complement hr hQU
  have hne : s.start ≠ s.finish := by
    rw [hst, hfn]
    exact ne_complement_start hr hbQ
  refine ⟨r.start, rstartA, ?_⟩
  have hR0 := spanningPathCompatible_of_path s hne
  rw [← hsup, ← hst, ← hfn]
  exact hR0

/-- Local `Q`-path from `b` to `Q.finish`, spliced to `r` along the
successor original seam. The resulting `U`-path ends at `r.finish ∈ A`.
@isnad1 id=ex.7h8v.s7.61aa57e1ef5e from=translated src=- shape=73dfd89e vocab=af095697
-/
lemma spanning_of_succ_seam {U A : Finset V} {Q r q : GraphPath G} {b : V}
    (hq : q.support = Q.support) (hstq : q.start = b)
    (hfinq : q.finish = Q.finish)
    (hr : r.support = U \ Q.support) (hQU : Q.support ⊆ U)
    (hsucc : G.Adj Q.finish r.start) (rfinishA : r.finish ∈ A) :
    ∃ a ∈ A, SpanningPathCompatible (G := G) U b a := by
  have hbQ : b ∈ Q.support := by
    have : q.start ∈ q.support := q.start_mem_support
    simpa [hstq, hq] using this
  have hd : Disjoint q.support r.support := by
    simpa [hq] using disjoint_of_complement hr
  have hadj : G.Adj q.finish r.start := by
    simpa [hfinq] using hsucc
  let s := q.splice r hadj hd
  have hst : s.start = b := by
    change q.start = b
    exact hstq
  have hfn : s.finish = r.finish := rfl
  have hsup : s.support = U := by
    rw [show s.support = q.support ∪ r.support from
        support_splice q r hadj hd, hq]
    exact union_of_complement hr hQU
  have hne : s.start ≠ s.finish := by
    rw [hst, hfn]
    exact ne_complement_finish hr hbQ
  refine ⟨r.finish, rfinishA, ?_⟩
  have hR0 := spanningPathCompatible_of_path s hne
  rw [← hsup, ← hst, ← hfn]
  exact hR0

/-- From `b ∈ U \ S_A`, the saturated leftover cover of the opened cycle
supplies an original spanning `U`-path from `b` into `A`. No external
cover, complement, or local-eligibility certificate is assumed.
@isnad1 id=ex.6h6v.s6.64cc39471b43 from=translated src=- shape=3ea2fb0c vocab=e825e282
-/
lemma exists_spanning_from_sdiff_container {U A : Finset V} {b : V}
    (c : GraphCycle G) (hc : c.support = U)
    (hA : A ⊆ U) (hAne : A.Nonempty)
    (hK : Nikoghosyan.IsCograph G (U \ A))
    (hSat : Saturated (G := G) U A)
    (hb : b ∈ U \ canonicalContainer (G := G) U A) :
    ∃ a ∈ A, SpanningPathCompatible (G := G) U b a := by
  obtain ⟨p, pc, hp, hsA, hclose, _hedges, hmin, hpaths, _hsub⟩ :=
    cycle_leftover_cover_min_of_saturated c hc hA hAne hSat
  have hbE := eligible_of_mem_sdiff_container (G := G) (U := U) (A := A) hb
  obtain ⟨Q, hQ, hbQ⟩ := exists_path_of_mem_cover pc hbE.1
  have hK' : IsCograph G (U \ A) := isCograph_iff.2 hK
  have hEloc : Eligible G Q.support b :=
    restriction_eligible_on_selected_path hK' pc hmin hQ hbE.2 hbQ
  obtain ⟨r, hr, rstartA, rfinishA, hpred, hsucc⟩ :=
    exists_complement_arc_of_mem_leftover c hc hA hAne hp hsA hclose hpaths hQ
  have hQU : Q.support ⊆ U := support_subset_of_sdiff pc hQ
  by_cases h2 : 2 ≤ Q.support.card
  · have hQcog : IsCograph G Q.support :=
      hK'.subset (pc.support_subset hQ)
    rcases exists_compatible_old_end h2 hQcog hEloc hbQ with hRu | hRv
    · obtain ⟨q, hq, qst, qfin⟩ := exists_oriented_path_from hRu
      exact spanning_of_pred_seam (A := A) hq qst qfin hr hQU hpred rstartA
    · obtain ⟨q, hq, qst, qfin⟩ := exists_oriented_path_from hRv
      exact spanning_of_succ_seam (A := A) hq qst qfin hr hQU hsucc rfinishA
  · have h1 : Q.support.card = 1 := support_card_eq_one_of_not_two h2
    exact spanning_of_singleton_leftover (A := A) h1 hbQ hr hQU hpred rstartA

/-- Forward neighbourhood: every vertex of `U \ S_A` is `R(U)`-adjacent
to `A`.
@isnad1 id=le.5h5v.s6.a7321520e4a3 from=translated src=- shape=36ebef5a vocab=7e7b2ac2
-/
lemma sdiff_container_subset_spanningPathNeighbors {U A : Finset V}
    (c : GraphCycle G) (hc : c.support = U)
    (hA : A ⊆ U) (hAne : A.Nonempty)
    (hK : Nikoghosyan.IsCograph G (U \ A))
    (hSat : Saturated (G := G) U A) :
    U \ canonicalContainer (G := G) U A ⊆
      spanningPathNeighbors (G := G) U A := by
  intro b hb
  have hbU : b ∈ U := (mem_sdiff.1 hb).1
  obtain ⟨a, haA, hR⟩ :=
    exists_spanning_from_sdiff_container c hc hA hAne hK hSat hb
  exact mem_spanningPathNeighbors_iff.2
    ⟨hbU, a, haA, spanningPathCompatible_symm hR⟩

/-- Manuscript `prof:prop:endpoints`: on an actual original cycle support,
with nonempty saturated `A` and cograph remainder, `N_R(A) = U \ S_A`.
@isnad1 id=eq.5h5v.s6.7f37dbae7cc7 from=translated src=- shape=dd5a8cc8 vocab=7e7b2ac2
-/
lemma spanningPathNeighbors_eq_sdiff_container {U A : Finset V}
    (c : GraphCycle G) (hc : c.support = U)
    (hA : A ⊆ U) (hAne : A.Nonempty)
    (hK : Nikoghosyan.IsCograph G (U \ A))
    (hSat : Saturated (G := G) U A) :
    spanningPathNeighbors (G := G) U A =
      U \ canonicalContainer (G := G) U A := by
  apply subset_antisymm
  · exact spanningPathNeighbors_subset_sdiff_container hA
      (isCograph_iff.2 hK) hAne hSat
  · exact sdiff_container_subset_spanningPathNeighbors c hc hA hAne hK hSat

/-- No original spanning `A`–`B` path and saturation of `A` force
`B ⊆ S_A`.
@isnad1 id=le.7h6v.s7.0f2fd280943c from=translated src=- shape=40b6c2d3 vocab=e825e282
-/
lemma subset_canonicalContainer_of_no_spanning {U A B : Finset V}
    (c : GraphCycle G) (hc : c.support = U)
    (hA : A ⊆ U) (hAne : A.Nonempty)
    (hK : Nikoghosyan.IsCograph G (U \ A))
    (hB : B ⊆ U)
    (hSatA : Saturated (G := G) U A)
    (hno : ∀ a ∈ A, ∀ b ∈ B, ¬ SpanningPathCompatible (G := G) U a b) :
    B ⊆ canonicalContainer (G := G) U A := by
  intro b hbB
  have hbU : b ∈ U := hB hbB
  by_contra hbS
  have hbN : b ∈ U \ canonicalContainer (G := G) U A :=
    mem_sdiff.2 ⟨hbU, hbS⟩
  have hbN' : b ∈ spanningPathNeighbors (G := G) U A := by
    rw [spanningPathNeighbors_eq_sdiff_container c hc hA hAne hK hSatA]
    exact hbN
  obtain ⟨_, a, haA, hR⟩ := mem_spanningPathNeighbors_iff.1 hbN'
  exact hno a haA b hbB hR

/-- Manuscript `prof:prop:incompatible`: if there is no original spanning
`U`-path with one end in `A` and the other in `B`, and at least one of
the two profiles is saturated, then both are saturated and
`S_A = S_B`. The sets `A,B` need not be disjoint.
@isnad1 id=and.9h6v.s7.aee4ac17f42a from=translated src=- shape=e46abf8e vocab=e825e282
-/
lemma incompatible_saturated_profiles {U A B : Finset V}
    (c : GraphCycle G) (hc : c.support = U)
    (hA : A ⊆ U) (hAne : A.Nonempty)
    (hKA : Nikoghosyan.IsCograph G (U \ A))
    (hB : B ⊆ U) (hBne : B.Nonempty)
    (hKB : Nikoghosyan.IsCograph G (U \ B))
    (hSat : Saturated (G := G) U A ∨ Saturated (G := G) U B)
    (hno : ∀ a ∈ A, ∀ b ∈ B, ¬ SpanningPathCompatible (G := G) U a b) :
    B ⊆ canonicalContainer (G := G) U A ∧
      Saturated (G := G) U A ∧ Saturated (G := G) U B ∧
        canonicalContainer (G := G) U A =
          canonicalContainer (G := G) U B := by
  have hno' : ∀ b ∈ B, ∀ a ∈ A, ¬ SpanningPathCompatible (G := G) U b a := by
    intro b hbB a haA hR
    exact hno a haA b hbB (spanningPathCompatible_symm hR)
  rcases hSat with hSatA | hSatB
  · have hBA : B ⊆ canonicalContainer (G := G) U A :=
      subset_canonicalContainer_of_no_spanning c hc hA hAne hKA hB hSatA hno
    have hTA :=
      (canonical_saturated_container_spec_of_canonical hA hAne hKA hSatA).1
    have hSatB : Saturated (G := G) U B :=
      Saturated_of_tight_container c hc hB hBne hBA hTA
    have heq :=
      coincidence_canonical_containers_of_canonical hA hAne hKA hB hBne hKB
        hSatA hSatB hBA
    exact ⟨hBA, hSatA, hSatB, heq⟩
  · have hAB : A ⊆ canonicalContainer (G := G) U B :=
      subset_canonicalContainer_of_no_spanning c hc hB hBne hKB hA hSatB hno'
    have hTB :=
      (canonical_saturated_container_spec_of_canonical hB hBne hKB hSatB).1
    have hSatA : Saturated (G := G) U A :=
      Saturated_of_tight_container c hc hA hAne hAB hTB
    have heqBA :=
      coincidence_canonical_containers_of_canonical hB hBne hKB hA hAne hKA
        hSatB hSatA hAB
    have hBA : B ⊆ canonicalContainer (G := G) U A := by
      intro x hx
      have hxB : x ∈ canonicalContainer (G := G) U B :=
        mem_canonicalContainer_of_mem_A hx
      simpa [heqBA] using hxB
    exact ⟨hBA, hSatA, hSatB, heqBA.symm⟩

end Cograph
end Nikoghosyan
