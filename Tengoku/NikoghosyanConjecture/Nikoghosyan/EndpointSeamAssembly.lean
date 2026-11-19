/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Tengoku.NikoghosyanConjecture.Nikoghosyan.FactorAssembly
import Tengoku.NikoghosyanConjecture.Nikoghosyan.PathCover

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/canghaimeng/Nikoghosyan-conjecture@ccc8514d6801, `Nikoghosyan/EndpointSeamAssembly.lean`: removed 2 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-!
Phase 13: generic original-edge endpoint-seam cycle assembly.

Given a finite vertex set `A` disjoint from a carrier `K`, an actual
original-edge `PathCover` of `K` of cardinality `m = |A| ≥ 2`, and every
original seam from every vertex of `A` to both endpoints of every cover
path, attach each enumerated `A`-vertex to the finish of the matching
cover path and close the resulting `m` blocks cyclically by the original
seams from each attached vertex to the next path start.

This does not assume `A` is complete to all of `K`. Singleton cover paths
are allowed. The output is one genuine original `GraphCycle` whose support
is exactly `A ∪ K`. It is not by itself a structural Hamiltonicity theorem.
-/


open Classical
open Finset Function SimpleGraph

namespace Nikoghosyan

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}

/-! ### Path-cover concatenation on a disjoint partition -/

namespace PathCover

/-- Concatenate actual path covers of disjoint carriers. No no-cross
hypothesis is used: membership and support disjointness suffice.-/
noncomputable def appendDisjoint {A B : Finset V} (hdisj : Disjoint A B)
    (pcA : PathCover G A) (pcB : PathCover G B) : PathCover G (A ∪ B) where
  paths := pcA.paths ++ pcB.paths
  disjoint := by
    refine List.pairwise_append.mpr ⟨pcA.disjoint, pcB.disjoint, ?_⟩
    intro p hp q hq
    exact Finset.disjoint_of_subset_left (pcA.support_subset hp)
      (Finset.disjoint_of_subset_right (pcB.support_subset hq) hdisj)
  mem_iff := by
    intro x
    constructor
    · intro hx
      rcases mem_union.1 hx with hxA | hxB
      · obtain ⟨p, hp, hxp⟩ := (pcA.mem_iff x).1 hxA
        exact ⟨p, List.mem_append.2 (Or.inl hp), hxp⟩
      · obtain ⟨p, hp, hxp⟩ := (pcB.mem_iff x).1 hxB
        exact ⟨p, List.mem_append.2 (Or.inr hp), hxp⟩
    · intro ⟨p, hp, hxp⟩
      rcases List.mem_append.1 hp with hpA | hpB
      · exact mem_union.2 (Or.inl ((pcA.mem_iff x).2 ⟨p, hpA, hxp⟩))
      · exact mem_union.2 (Or.inr ((pcB.mem_iff x).2 ⟨p, hpB, hxp⟩))

/--
@isnad1 id=eq.1h6v.s6.be38c5aad927 from=translated src=- shape=9e0d2f3e vocab=46489531
-/
lemma appendDisjoint_card {A B : Finset V} (hdisj : Disjoint A B)
    (pcA : PathCover G A) (pcB : PathCover G B) :
    (appendDisjoint hdisj pcA pcB).card = pcA.card + pcB.card := by
  simp [appendDisjoint, PathCover.card, List.length_append]

/--
@isnad1 id=iff.1h7v.s6.477280ebcfb2 from=translated src=- shape=10cda5f2 vocab=95572487
-/
lemma appendDisjoint_mem_iff {A B : Finset V} (hdisj : Disjoint A B)
    (pcA : PathCover G A) (pcB : PathCover G B) {p : GraphPath G} :
    p ∈ (appendDisjoint hdisj pcA pcB).paths ↔
      p ∈ pcA.paths ∨ p ∈ pcB.paths := by
  simp [appendDisjoint, List.mem_append]

/--
@isnad1 id=and.1h5v.s6.786e2741d765 from=translated src=- shape=450d036b vocab=e245a813
-/
lemma endpoints_mem {U : Finset V} (pc : PathCover G U) {p : GraphPath G}
    (hp : p ∈ pc.paths) : p.start ∈ U ∧ p.finish ∈ U :=
  ⟨pc.support_subset hp p.start_mem_support,
    pc.support_subset hp p.finish_mem_support⟩

end PathCover

/-! ### Indexed vertices / cover paths -/

/-- The `i`-th vertex of a duplicate-free enumeration of `A`.-/
noncomputable def vertexAt (A : Finset V) (i : Fin A.card) : V :=
  A.toList.get ⟨i.1, by simpa [A.length_toList] using i.2⟩

/--
@isnad1 id=mem.0h3v.s4.c5082e31af74 from=translated src=- shape=e125d370 vocab=1a4a1617
-/
lemma vertexAt_mem (A : Finset V) (i : Fin A.card) : vertexAt A i ∈ A :=
  mem_toList.1 (List.get_mem _ _)

/--
@isnad1 id=injectiv.0h2v.s4.a46400b659a8 from=translated src=- shape=cff3e3d8 vocab=6b358e37
-/
lemma vertexAt_injective (A : Finset V) : Injective (vertexAt (A := A)) := by
  intro i j h
  have hnd : A.toList.Nodup := A.nodup_toList
  have hi : i.1 < A.toList.length := by simpa [A.length_toList] using i.2
  have hj : j.1 < A.toList.length := by simpa [A.length_toList] using j.2
  have hget :
      A.toList.get ⟨i.1, hi⟩ = A.toList.get ⟨j.1, hj⟩ := by
    simpa [vertexAt] using h
  have hij : (⟨i.1, hi⟩ : Fin A.toList.length) = ⟨j.1, hj⟩ :=
    (List.Nodup.get_inj_iff hnd).1 hget
  have hval : i.1 = j.1 := congrArg (fun t : Fin A.toList.length => t.1) hij
  exact Fin.ext hval

/--
@isnad1 id=ex.1h3v.s5.2f32bebd64f0 from=translated src=- shape=9af5dc5a vocab=1a4a1617
-/
lemma exists_vertexAt {A : Finset V} {a : V} (ha : a ∈ A) :
    ∃ i : Fin A.card, vertexAt A i = a := by
  have hmem : a ∈ A.toList := mem_toList.2 ha
  obtain ⟨i, rfl⟩ := List.get_of_mem hmem
  refine ⟨⟨i.1, by simpa [A.length_toList] using i.2⟩, ?_⟩
  simp [vertexAt]

/-- The `i`-th path of an actual cover, indexed by cover cardinality.-/
noncomputable def pathAt {K : Finset V} (pc : PathCover G K) (i : Fin pc.card) :
    GraphPath G :=
  pc.paths.get ⟨i.1, by simpa [PathCover.card] using i.2⟩

/--
@isnad1 id=mem.0h5v.s5.f583654c1016 from=translated src=- shape=8a36d53e vocab=1da949f1
-/
lemma pathAt_mem {K : Finset V} (pc : PathCover G K) (i : Fin pc.card) :
    pathAt pc i ∈ pc.paths :=
  List.get_mem _ _

/--
@isnad1 id=le.0h5v.s5.ffbc2c94abd0 from=translated src=- shape=6a780278 vocab=ced8b8cb
-/
lemma pathAt_support_subset {K : Finset V} (pc : PathCover G K)
    (i : Fin pc.card) : (pathAt pc i).support ⊆ K :=
  pc.support_subset (pathAt_mem pc i)

/--
@isnad1 id=ex.1h5v.s6.ea0ad3d88827 from=translated src=- shape=c892a89c vocab=1da949f1
-/
lemma exists_pathAt {K : Finset V} (pc : PathCover G K) {p : GraphPath G}
    (hp : p ∈ pc.paths) : ∃ i : Fin pc.card, pathAt pc i = p := by
  obtain ⟨i, rfl⟩ := List.get_of_mem hp
  refine ⟨⟨i.1, by simpa [PathCover.card] using i.2⟩, ?_⟩
  simp [pathAt]

/--
@isnad1 id=disjoint.1h6v.s6.17bc1083129f from=translated src=- shape=441cbc55 vocab=20ce1250
-/
lemma pathAt_disjoint {K : Finset V} (pc : PathCover G K)
    {i j : Fin pc.card} (hij : i ≠ j) :
    Disjoint (pathAt pc i).support (pathAt pc j).support := by
  have hpw :=
    (List.pairwise_iff_get (R := fun p q : GraphPath G =>
      Disjoint p.support q.support)).1 pc.disjoint
  have hi : i.1 < pc.paths.length := by simpa [PathCover.card] using i.2
  have hj : j.1 < pc.paths.length := by simpa [PathCover.card] using j.2
  rcases Nat.lt_trichotomy i.1 j.1 with hlt | heq | hgt
  · simpa [pathAt] using hpw ⟨i.1, hi⟩ ⟨j.1, hj⟩ hlt
  · exact (hij (Fin.ext heq)).elim
  · simpa [pathAt] using (hpw ⟨j.1, hj⟩ ⟨i.1, hi⟩ hgt).symm

/-! ### Support-union cardinality -/

/--
@isnad1 id=le.1h3v.s5.216728b98e38 from=translated src=- shape=f0bf1e52 vocab=eb1484a5
-/
lemma card_supportUnion_ge_length {ps : List (GraphPath G)}
    (hdisj : ps.Pairwise fun p q => Disjoint p.support q.support) :
    ps.length ≤ (GraphPath.supportUnion ps).card := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    have hpw := List.pairwise_cons.1 hdisj
    have ih' := ih hpw.2
    have hd : Disjoint p.support (GraphPath.supportUnion ps) := by
      rw [disjoint_iff_inter_eq_empty]
      ext x
      constructor
      · intro hx
        obtain ⟨q, hq, hxq⟩ := GraphPath.mem_supportUnion.1 (mem_inter.1 hx).2
        exact (disjoint_left.1 (hpw.1 q hq) (mem_inter.1 hx).1 hxq).elim
      · intro h
        exact (notMem_empty x h).elim
    have hcard := card_union_of_disjoint hd
    have hpos : 1 ≤ p.support.card := card_pos.2 p.support_nonempty
    rw [GraphPath.supportUnion_cons, hcard, List.length_cons]
    omega

/--
@isnad1 id=eq.0h4v.s5.e3f83377b0e8 from=translated src=- shape=63fcd27d vocab=188dd484
-/
lemma PathCover.supportUnion_eq {U : Finset V} (pc : PathCover G U) :
    GraphPath.supportUnion pc.paths = U := by
  ext x
  constructor
  · intro hx
    obtain ⟨p, hp, hxp⟩ := GraphPath.mem_supportUnion.1 hx
    exact (pc.mem_iff x).2 ⟨p, hp, hxp⟩
  · intro hx
    obtain ⟨p, hp, hxp⟩ := (pc.mem_iff x).1 hx
    exact GraphPath.mem_supportUnion.2 ⟨p, hp, hxp⟩

/--
@isnad1 id=le.0h4v.s5.d3109dbd2b08 from=translated src=- shape=078b167b vocab=7b8db82e
-/
lemma PathCover.card_le_card {U : Finset V} (pc : PathCover G U) :
    pc.card ≤ U.card := by
  have hge := card_supportUnion_ge_length pc.disjoint
  simpa [PathCover.card, pc.supportUnion_eq] using hge

/--
@isnad1 id=iff.0h5v.s6.81fbb07ea57c from=translated src=- shape=7a7b2e47 vocab=eb23f943
-/
lemma mem_supportUnion_ofFn {n : ℕ} (f : Fin n → GraphPath G) {x : V} :
    x ∈ GraphPath.supportUnion (List.ofFn f) ↔
      ∃ i : Fin n, x ∈ (f i).support := by
  constructor
  · intro hx
    obtain ⟨p, hp, hxp⟩ := GraphPath.mem_supportUnion.1 hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hp
    exact ⟨i, hxp⟩
  · intro ⟨i, hxi⟩
    exact GraphPath.mem_supportUnion.2 ⟨f i, List.mem_ofFn.2 ⟨i, rfl⟩, hxi⟩

/-! ### Attaching an `A`-vertex to a cover-path finish -/

/-- Original-edge block obtained by splicing the singleton at `a` onto the
finish of `p`. The new start is `p.start` and the new finish is `a`.-/
def attachFinish (p : GraphPath G) (a : V) (hadj : G.Adj p.finish a)
    (ha : a ∉ p.support) : GraphPath G :=
  p.splice (GraphPath.singleton (G := G) a) hadj (by
    simpa [GraphPath.support_singleton] using (disjoint_singleton_right.2 ha))

/--
@isnad1 id=eq.2h4v.s5.9a53ef4a183d from=translated src=- shape=329a53b2 vocab=e87c3471
-/
lemma start_attachFinish (p : GraphPath G) (a : V) (hadj : G.Adj p.finish a)
    (ha : a ∉ p.support) : (attachFinish p a hadj ha).start = p.start :=
  GraphPath.start_splice p (GraphPath.singleton (G := G) a) hadj _

/--
@isnad1 id=eq.2h4v.s5.87f79576041b from=translated src=- shape=1dfce10a vocab=a3b05d09
-/
lemma finish_attachFinish (p : GraphPath G) (a : V) (hadj : G.Adj p.finish a)
    (ha : a ∉ p.support) : (attachFinish p a hadj ha).finish = a :=
  GraphPath.finish_splice p (GraphPath.singleton (G := G) a) hadj _

/--
@isnad1 id=eq.2h4v.s6.3432b2f99637 from=translated src=- shape=4da2a83d vocab=d3d7e94b
-/
lemma support_attachFinish (p : GraphPath G) (a : V) (hadj : G.Adj p.finish a)
    (ha : a ∉ p.support) :
    (attachFinish p a hadj ha).support = p.support ∪ {a} := by
  simpa [attachFinish, GraphPath.support_singleton] using
    GraphPath.support_splice p (GraphPath.singleton (G := G) a) hadj _

/-! ### Indexed seam blocks -/

namespace EndpointSeam

variable {A K : Finset V}

/--
@isnad1 id=not.3h7v.s6.27582ed28277 from=translated src=- shape=8024da4b vocab=30219d7a
-/
lemma not_mem_path_of_disjoint (hAK : Disjoint A K) {a : V} (ha : a ∈ A)
    {p : GraphPath G} {pc : PathCover G K} (hp : p ∈ pc.paths) :
    a ∉ p.support :=
  fun h => disjoint_left.1 hAK ha (pc.support_subset hp h)

noncomputable def seamPath (pc : PathCover G K)
    (hcard : A.card = pc.card) (hAK : Disjoint A K)
    (hseams : ∀ a ∈ A, ∀ p ∈ pc.paths, G.Adj a p.start ∧ G.Adj a p.finish)
    (i : Fin A.card) : GraphPath G :=
  let a := vertexAt A i
  let p := pathAt pc (i.cast hcard)
  attachFinish p a
    ((hseams a (vertexAt_mem A i) p (pathAt_mem pc (i.cast hcard))).2.symm)
    (not_mem_path_of_disjoint hAK (vertexAt_mem A i)
      (pathAt_mem pc (i.cast hcard)))

/--
@isnad1 id=eq.3h6v.s7.013f0172e995 from=translated src=- shape=dc8ffe67 vocab=f508648c
-/
lemma seamPath_start (pc : PathCover G K)
    (hcard : A.card = pc.card) (hAK : Disjoint A K)
    (hseams : ∀ a ∈ A, ∀ p ∈ pc.paths, G.Adj a p.start ∧ G.Adj a p.finish)
    (i : Fin A.card) :
    (seamPath pc hcard hAK hseams i).start =
      (pathAt pc (i.cast hcard)).start := by
  simp [seamPath, start_attachFinish]

/--
@isnad1 id=eq.3h6v.s7.290ae72f555f from=translated src=- shape=29ec708a vocab=59121d84
-/
lemma seamPath_finish (pc : PathCover G K)
    (hcard : A.card = pc.card) (hAK : Disjoint A K)
    (hseams : ∀ a ∈ A, ∀ p ∈ pc.paths, G.Adj a p.start ∧ G.Adj a p.finish)
    (i : Fin A.card) :
    (seamPath pc hcard hAK hseams i).finish = vertexAt A i := by
  simp [seamPath, finish_attachFinish]

/--
@isnad1 id=eq.3h6v.s7.41e54f73b77b from=translated src=- shape=906c73d3 vocab=21a7de1c
-/
lemma seamPath_support (pc : PathCover G K)
    (hcard : A.card = pc.card) (hAK : Disjoint A K)
    (hseams : ∀ a ∈ A, ∀ p ∈ pc.paths, G.Adj a p.start ∧ G.Adj a p.finish)
    (i : Fin A.card) :
    (seamPath pc hcard hAK hseams i).support =
      (pathAt pc (i.cast hcard)).support ∪ {vertexAt A i} := by
  simp [seamPath, support_attachFinish]

noncomputable def seamList (pc : PathCover G K)
    (hcard : A.card = pc.card) (hAK : Disjoint A K)
    (hseams : ∀ a ∈ A, ∀ p ∈ pc.paths, G.Adj a p.start ∧ G.Adj a p.finish) :
    List (GraphPath G) :=
  List.ofFn (seamPath pc hcard hAK hseams)

/--
@isnad1 id=eq.3h5v.s6.c6eed05bb695 from=translated src=- shape=fe069860 vocab=b87caf0c
-/
lemma length_seamList (pc : PathCover G K)
    (hcard : A.card = pc.card) (hAK : Disjoint A K)
    (hseams : ∀ a ∈ A, ∀ p ∈ pc.paths, G.Adj a p.start ∧ G.Adj a p.finish) :
    (seamList pc hcard hAK hseams).length = A.card := by
  simp [seamList]

/--
@isnad1 id=eq.4h6v.s7.d48488109861 from=translated src=- shape=711e9bc4 vocab=3659d5c7
-/
lemma seamList_get (pc : PathCover G K)
    (hcard : A.card = pc.card) (hAK : Disjoint A K)
    (hseams : ∀ a ∈ A, ∀ p ∈ pc.paths, G.Adj a p.start ∧ G.Adj a p.finish)
    {i : ℕ} (hi : i < (seamList pc hcard hAK hseams).length) :
    (seamList pc hcard hAK hseams).get ⟨i, hi⟩ =
      seamPath pc hcard hAK hseams ⟨i, by simpa [length_seamList] using hi⟩ := by
  simp [seamList, List.get_ofFn]

/--
@isnad1 id=pairwise.3h5v.s7.101e93f7807f from=translated src=- shape=5c6fc73a vocab=7983c440
-/
lemma pairwise_seamList (pc : PathCover G K)
    (hcard : A.card = pc.card) (hAK : Disjoint A K)
    (hseams : ∀ a ∈ A, ∀ p ∈ pc.paths, G.Adj a p.start ∧ G.Adj a p.finish) :
    (seamList pc hcard hAK hseams).Pairwise
      fun p q => Disjoint p.support q.support := by
  rw [List.pairwise_iff_get]
  intro i j hij
  have hi : i.1 < A.card := by simpa [length_seamList] using i.2
  have hj : j.1 < A.card := by simpa [length_seamList] using j.2
  have hne : (⟨i.1, hi⟩ : Fin A.card) ≠ ⟨j.1, hj⟩ := by
    intro h
    exact Nat.ne_of_lt hij (Fin.mk.inj_iff.mp h)
  have hcast :
      ((⟨i.1, hi⟩ : Fin A.card).cast hcard) ≠
        ((⟨j.1, hj⟩ : Fin A.card).cast hcard) := by
    intro h
    exact hne (Fin.ext (by simpa [Fin.cast] using congrArg Fin.val h))
  have hp := pathAt_disjoint pc hcast
  have ha :
      vertexAt A ⟨i.1, hi⟩ ≠ vertexAt A ⟨j.1, hj⟩ :=
    fun h => hne (vertexAt_injective A h)
  have haiK : vertexAt A ⟨i.1, hi⟩ ∉
      (pathAt pc ((⟨j.1, hj⟩ : Fin A.card).cast hcard)).support :=
    not_mem_path_of_disjoint hAK (vertexAt_mem A _) (pathAt_mem pc _)
  have hajK : vertexAt A ⟨j.1, hj⟩ ∉
      (pathAt pc ((⟨i.1, hi⟩ : Fin A.card).cast hcard)).support :=
    not_mem_path_of_disjoint hAK (vertexAt_mem A _) (pathAt_mem pc _)
  rw [seamList_get, seamList_get, seamPath_support, seamPath_support]
  refine disjoint_union_left.2
    ⟨disjoint_union_right.2 ⟨hp, disjoint_singleton_right.2 hajK⟩,
      disjoint_union_right.2 ⟨disjoint_singleton_left.2 haiK,
        disjoint_singleton_left.2 (mt mem_singleton.1 ha)⟩⟩

/--
@isnad1 id=adj.4h6v.s7.6ef5b32c658c from=translated src=- shape=b322d475 vocab=c53839b3
-/
lemma hedges_seamList (pc : PathCover G K)
    (hcard : A.card = pc.card) (hAK : Disjoint A K)
    (hseams : ∀ a ∈ A, ∀ p ∈ pc.paths, G.Adj a p.start ∧ G.Adj a p.finish) :
    ∀ i (hi : i + 1 < (seamList pc hcard hAK hseams).length),
      G.Adj
        ((seamList pc hcard hAK hseams).get ⟨i, Nat.lt_of_succ_lt hi⟩).finish
        ((seamList pc hcard hAK hseams).get ⟨i + 1, hi⟩).start := by
  intro i hi
  have hi' : i + 1 < A.card := by simpa [length_seamList] using hi
  have hi0 : i < A.card := Nat.lt_of_succ_lt hi'
  rw [seamList_get, seamList_get, seamPath_finish, seamPath_start]
  exact (hseams (vertexAt A ⟨i, hi0⟩) (vertexAt_mem A _)
    (pathAt pc ((⟨i + 1, hi'⟩ : Fin A.card).cast hcard))
    (pathAt_mem pc _)).1

/--
@isnad1 id=ne.4h5v.s7.6c827845632c from=translated src=- shape=2c56e639 vocab=51ff3bfe
-/
lemma seamList_ne_nil (pc : PathCover G K)
    (hcard : A.card = pc.card) (hAK : Disjoint A K)
    (hseams : ∀ a ∈ A, ∀ p ∈ pc.paths, G.Adj a p.start ∧ G.Adj a p.finish)
    (hm : 2 ≤ A.card) : seamList pc hcard hAK hseams ≠ [] := by
  intro h
  have hlen := length_seamList pc hcard hAK hseams
  simp [h] at hlen
  omega

/--
@isnad1 id=adj.4h5v.s7.1dd75e1daef6 from=translated src=- shape=971c156f vocab=bea3d274
-/
lemma hclose_seamList (pc : PathCover G K)
    (hcard : A.card = pc.card) (hAK : Disjoint A K)
    (hseams : ∀ a ∈ A, ∀ p ∈ pc.paths, G.Adj a p.start ∧ G.Adj a p.finish)
    (hm : 2 ≤ A.card) :
    G.Adj
      ((seamList pc hcard hAK hseams).getLast
        (seamList_ne_nil pc hcard hAK hseams hm)).finish
      ((seamList pc hcard hAK hseams).head
        (seamList_ne_nil pc hcard hAK hseams hm)).start := by
  have hne := seamList_ne_nil pc hcard hAK hseams hm
  have hlen := length_seamList pc hcard hAK hseams
  have hlastIdx : A.card - 1 < A.card := by omega
  have hlast :
      (seamList pc hcard hAK hseams).getLast hne =
        seamPath pc hcard hAK hseams ⟨A.card - 1, hlastIdx⟩ := by
    rw [List.getLast_eq_getElem hne]
    have : (seamList pc hcard hAK hseams).length - 1 = A.card - 1 := by omega
    simp [seamList, this]
  have hhead :
      (seamList pc hcard hAK hseams).head hne =
        seamPath pc hcard hAK hseams ⟨0, by omega⟩ := by
    rw [List.head_eq_getElem_zero hne]
    simp [seamList]
  rw [hlast, hhead, seamPath_finish, seamPath_start]
  exact (hseams (vertexAt A ⟨A.card - 1, hlastIdx⟩) (vertexAt_mem A _)
    (pathAt pc ((⟨0, by omega⟩ : Fin A.card).cast hcard))
    (pathAt_mem pc _)).1

/--
@isnad1 id=eq.3h5v.s7.80d464a9c417 from=translated src=- shape=a91ce711 vocab=3e7dd629
-/
lemma supportUnion_seamList (pc : PathCover G K)
    (hcard : A.card = pc.card) (hAK : Disjoint A K)
    (hseams : ∀ a ∈ A, ∀ p ∈ pc.paths, G.Adj a p.start ∧ G.Adj a p.finish) :
    GraphPath.supportUnion (seamList pc hcard hAK hseams) = A ∪ K := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hxi⟩ := (mem_supportUnion_ofFn (seamPath pc hcard hAK hseams)).1
      (by simpa [seamList] using hx)
    rw [seamPath_support] at hxi
    rcases mem_union.1 hxi with hp | ha
    · exact mem_union.2 (Or.inr (pathAt_support_subset pc _ hp))
    · exact mem_union.2 (Or.inl (by
        rw [mem_singleton.1 ha]
        exact vertexAt_mem A i))
  · intro hx
    rcases mem_union.1 hx with hxA | hxK
    · obtain ⟨i, rfl⟩ := exists_vertexAt hxA
      refine GraphPath.mem_supportUnion.2
        ⟨seamPath pc hcard hAK hseams i,
          by simp [seamList, List.mem_ofFn], ?_⟩
      rw [seamPath_support]
      exact mem_union.2 (Or.inr (mem_singleton_self _))
    · obtain ⟨p, hp, hxp⟩ := (pc.mem_iff x).1 hxK
      obtain ⟨j, rfl⟩ := exists_pathAt pc hp
      let i : Fin A.card := ⟨j.1, by simpa [hcard] using j.2⟩
      have hj : j = i.cast hcard := Fin.ext (by simp [i, Fin.cast])
      refine GraphPath.mem_supportUnion.2
        ⟨seamPath pc hcard hAK hseams i,
          by simp [seamList, List.mem_ofFn], ?_⟩
      rw [seamPath_support, ← hj]
      exact mem_union.2 (Or.inl hxp)

/--
@isnad1 id=le.4h5v.s7.404525a93374 from=translated src=- shape=2d3779ef vocab=a9b8a01a
-/
lemma three_le_supportUnion_seamList (pc : PathCover G K)
    (hcard : A.card = pc.card) (hAK : Disjoint A K)
    (hseams : ∀ a ∈ A, ∀ p ∈ pc.paths, G.Adj a p.start ∧ G.Adj a p.finish)
    (hm : 2 ≤ A.card) :
    3 ≤ (GraphPath.supportUnion (seamList pc hcard hAK hseams)).card := by
  have hK : pc.card ≤ K.card := pc.card_le_card
  have hAU : (A ∪ K).card = A.card + K.card := card_union_of_disjoint hAK
  have hge : 2 * A.card ≤ (A ∪ K).card := by
    have : A.card + A.card ≤ A.card + K.card := Nat.add_le_add_left
      (hcard ▸ hK) _
    simpa [two_mul, hAU] using this
  have : 4 ≤ (A ∪ K).card := by
    have : 2 * 2 ≤ 2 * A.card := Nat.mul_le_mul_left 2 hm
    omega
  have h3 : 3 ≤ (A ∪ K).card := Nat.le_trans (by decide : (3 : ℕ) ≤ 4) this
  simpa [supportUnion_seamList pc hcard hAK hseams] using h3

/-- Genuine original-edge cycle on the exact support `A ∪ K`, assembled from
an actual cover of `K` by original endpoint seams with `A`. No completeness
of `A` to the interior of `K` is used.-/
noncomputable def assembledCycle (pc : PathCover G K)
    (hcard : A.card = pc.card) (hAK : Disjoint A K)
    (hseams : ∀ a ∈ A, ∀ p ∈ pc.paths, G.Adj a p.start ∧ G.Adj a p.finish)
    (hm : 2 ≤ A.card) : GraphCycle G :=
  GraphPath.assembleCycle (seamList pc hcard hAK hseams)
    (by simpa [length_seamList] using hm)
    (pairwise_seamList pc hcard hAK hseams)
    (hedges_seamList pc hcard hAK hseams)
    (hclose_seamList pc hcard hAK hseams hm)
    (three_le_supportUnion_seamList pc hcard hAK hseams hm)

/--
@isnad1 id=eq.4h5v.s7.c6f38f9091f8 from=translated src=- shape=6eab5a49 vocab=cbdc4fce
-/
lemma support_assembledCycle (pc : PathCover G K)
    (hcard : A.card = pc.card) (hAK : Disjoint A K)
    (hseams : ∀ a ∈ A, ∀ p ∈ pc.paths, G.Adj a p.start ∧ G.Adj a p.finish)
    (hm : 2 ≤ A.card) :
    (assembledCycle pc hcard hAK hseams hm).support = A ∪ K := by
  rw [assembledCycle, GraphPath.support_assembleCycle,
    supportUnion_seamList]

end EndpointSeam

/-- Generic original-edge endpoint-seam assembly. Inputs are an actual
`PathCover` of `K` of cardinality `|A| ≥ 2` together with every original
endpoint seam from `A`; the output is a genuine simple original cycle on
exactly `A ∪ K`.
@isnad1 id=ex.4h5v.s7.a45801576914 from=translated src=- shape=94c27f47 vocab=7fe9199c
-/
theorem exists_original_cycle_of_endpoint_seams
    {A K : Finset V} (pc : PathCover G K)
    (hcard : A.card = pc.card) (hAK : Disjoint A K)
    (hseams : ∀ a ∈ A, ∀ p ∈ pc.paths, G.Adj a p.start ∧ G.Adj a p.finish)
    (hm : 2 ≤ A.card) :
    ∃ c : GraphCycle G, c.support = A ∪ K :=
  ⟨EndpointSeam.assembledCycle pc hcard hAK hseams hm,
    EndpointSeam.support_assembledCycle pc hcard hAK hseams hm⟩

end Nikoghosyan
