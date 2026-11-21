/-
Copyright (c) 2026 TJC L.P.
SPDX-License-Identifier: MIT
Author: A. Richard Caputo III.
AI assistance: Weaver (exploration and formalization); GPT-5.6 Sol (review).

Formalization of the paper "How Far Can Goemans's Cost Conjecture Fail?"
(July 2026). This file proves Proposition 5.1.
-/
import Tengoku.Seed.Combinatorics.Quiver.Arborescence
import Tengoku.Seed.Data.List.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Proposition 5.1: no reconvergence rules out splices

This file is generic: a digraph is any pair of endpoint maps
`src dst : A → V`, a walk is an arc list whose endpoints chain up
(`IsWalk`), and acyclicity is witnessed by a rank function that strictly
increases along every arc. The paper's no-reconvergence hypothesis for a
pair of cheap paths `Zᵢ`, `Zⱼ` from a common source says their common
vertices all lie on a shared initial subpath `p`.

Under that hypothesis, `splice_prefix_eq` shows walk prefixes of `Zᵢ` and
`Zⱼ` ending at the same vertex coincide (prefix determinism through the
ranked-digraph lemma `IsWalk.prefix_unique`), and `splice_eq` concludes that
every splice — an initial segment of `Zⱼ` up to a common vertex, continued
by the tail of `Zᵢ` — is `Zᵢ` itself.

The family-level result `pathUnionArborescence` proves the follow-on
arborescence statement. It equips the union of a nonempty family of ranked
source-rooted paths with the quiver whose arrows are exactly the family
arcs. Pairwise no-reconvergence makes each non-root vertex have one incoming
arrow, so mathlib's `Quiver.arborescenceMk` gives a unique directed path from
the common source to every union vertex. Degree-two vertices do not affect
the arborescence property, so no suppression operation is needed.
-/

namespace Goemans

variable {V A : Type*} (src dst : A → V)

/-- `IsWalk src dst a b l`: the arc list `l` is a walk from `a` to `b` in the
digraph with endpoint maps `src`, `dst`.-/
def IsWalk : V → V → List A → Prop
  | a, b, [] => a = b
  | a, b, e :: l => src e = a ∧ IsWalk (dst e) b l

/-- The vertex trace of a walk starting at `a`.-/
def vertexTrace (a : V) (l : List A) : List V := a :: l.map dst

variable {src dst}

/--
@isnad1 id=eq.0h6v.s5.0d60f1660eb3 from=translated src=- shape=26af623a vocab=b57af831
-/
theorem vertexTrace_append (a : V) (l₁ l₂ : List A) :
    vertexTrace dst a (l₁ ++ l₂) = vertexTrace dst a l₁ ++ l₂.map dst := by
  simp [vertexTrace]

namespace IsWalk

/-- Concatenating two compatible walks gives a walk.
@isnad1 id=iswalk.2h9v.s5.f2d842146d1c from=translated src=- shape=5a2bd698 vocab=ce2f1610
-/
theorem append {a b c : V} {l₁ l₂ : List A}
    (h₁ : IsWalk src dst a b l₁) (h₂ : IsWalk src dst b c l₂) :
    IsWalk src dst a c (l₁ ++ l₂) := by
  induction l₁ generalizing a with
  | nil =>
    cases h₁
    exact h₂
  | cons e l ih =>
    exact ⟨h₁.1, ih h₁.2⟩

/--
@isnad1 id=ex.1h8v.s6.b7a243e627cd from=translated src=- shape=5445fe48 vocab=ce2f1610
-/
theorem append_inv {a b : V} {l₁ l₂ : List A}
    (h : IsWalk src dst a b (l₁ ++ l₂)) :
    ∃ c, IsWalk src dst a c l₁ ∧ IsWalk src dst c b l₂ := by
  induction l₁ generalizing a with
  | nil => exact ⟨a, rfl, h⟩
  | cons e l ih =>
    obtain ⟨c, hc, hb⟩ := ih h.2
    exact ⟨c, ⟨h.1, hc⟩, hb⟩

/--
@isnad1 id=mem.1h7v.s5.224759877309 from=translated src=- shape=0d8becf0 vocab=52996f4c
-/
theorem end_mem_vertexTrace {a b : V} {l : List A}
    (h : IsWalk src dst a b l) : b ∈ vertexTrace dst a l := by
  induction l generalizing a with
  | nil => simp [vertexTrace, h.symm]
  | cons e l ih =>
    have h' := ih h.2
    simp only [vertexTrace, List.map_cons, List.mem_cons] at h' ⊢
    exact Or.inr h'

/-- Walks strictly increase `rank`, one per arc.
@isnad1 id=le.2h8v.s6.02a3c6d9d596 from=translated src=- shape=35257dea vocab=7955de07
-/
theorem rank_add_length_le {rank : V → ℕ}
    (hrank : ∀ e, rank (src e) < rank (dst e)) {a b : V} {l : List A}
    (h : IsWalk src dst a b l) : rank a + l.length ≤ rank b := by
  induction l generalizing a with
  | nil =>
    have hab : a = b := h
    simp [hab]
  | cons e l ih =>
    have h1 := hrank e
    have h2 := ih h.2
    rw [h.1] at h1
    simp only [List.length_cons]
    omega

/-- In a ranked (acyclic) digraph the only closed walk is trivial.-/
theorem eq_nil_of_self {rank : V → ℕ}
    (hrank : ∀ e, rank (src e) < rank (dst e)) {a : V} {l : List A}
    (h : IsWalk src dst a a l) : l = [] := by
  have h1 := rank_add_length_le hrank h
  have h2 : l.length = 0 := by omega
  exact List.eq_nil_of_length_eq_zero h2

/--
@isnad1 id=ex.2h8v.s6.58bfdee18e90 from=translated src=- shape=c81b02fa vocab=a4ebe8c6
-/
theorem exists_prefix_of_mem_vertexTrace {a b v : V} {l : List A}
    (h : IsWalk src dst a b l) (hv : v ∈ vertexTrace dst a l) :
    ∃ l₁ l₂, l = l₁ ++ l₂ ∧ IsWalk src dst a v l₁ := by
  induction l generalizing a with
  | nil =>
    refine ⟨[], [], rfl, ?_⟩
    simp only [vertexTrace, List.map_nil, List.mem_singleton] at hv
    exact hv.symm
  | cons e l ih =>
    simp only [vertexTrace, List.map_cons, List.mem_cons] at hv
    rcases hv with hva | hv'
    · exact ⟨[], e :: l, rfl, hva.symm⟩
    · obtain ⟨l₁, l₂, hl, hw⟩ := ih h.2 (by simpa [vertexTrace] using hv')
      exact ⟨e :: l₁, l₂, by rw [hl, List.cons_append], h.1, hw⟩

/-- An arc occurring in a walk has a prefix ending at its source.
@isnad1 id=ex.2h8v.s6.ae3da2923140 from=translated src=- shape=036587a1 vocab=fc3cab60
-/
theorem exists_prefix_cons_of_mem {a b : V} {l : List A} {e : A}
    (h : IsWalk src dst a b l) (he : e ∈ l) :
    ∃ q r, l = q ++ e :: r ∧ IsWalk src dst a (src e) q := by
  obtain ⟨q, r, rfl⟩ := List.mem_iff_append.mp he
  obtain ⟨v, hq, her⟩ := append_inv h
  exact ⟨q, r, rfl, by simpa only [her.1] using hq⟩

/-- An arc occurring in a walk has a prefix through that arc, ending at its
destination.
@isnad1 id=ex.2h8v.s6.4725776cff82 from=translated src=- shape=7ca362f6 vocab=76905bcb
-/
theorem exists_prefix_through_of_mem {a b : V} {l : List A} {e : A}
    (h : IsWalk src dst a b l) (he : e ∈ l) :
    ∃ q r, l = (q ++ [e]) ++ r ∧
      IsWalk src dst a (dst e) (q ++ [e]) := by
  obtain ⟨q, r, hqr, hq⟩ := h.exists_prefix_cons_of_mem he
  refine ⟨q, r, ?_, hq.append ?_⟩
  · simpa only [List.append_assoc, List.singleton_append] using hqr
  · exact ⟨rfl, rfl⟩

/-- **Prefix determinism** in a ranked digraph: two walk prefixes of the same
arc list with the same endpoints are equal.
@isnad1 id=eq.4h11v.s6.9b898a3b3beb from=translated src=- shape=4af5dad1 vocab=a9777f83
-/
theorem prefix_unique {rank : V → ℕ}
    (hrank : ∀ e, rank (src e) < rank (dst e)) {a v : V}
    {q₁ s₁ q₂ s₂ : List A} (hq : q₁ ++ s₁ = q₂ ++ s₂)
    (hw₁ : IsWalk src dst a v q₁) (hw₂ : IsWalk src dst a v q₂) : q₁ = q₂ := by
  induction q₁ generalizing a q₂ with
  | nil =>
    have hv : a = v := hw₁
    subst hv
    exact (eq_nil_of_self hrank hw₂).symm
  | cons e q₁ ih =>
    cases q₂ with
    | nil =>
      have hv : a = v := hw₂
      subst hv
      exact absurd (eq_nil_of_self hrank hw₁) (by simp)
    | cons f q₂ =>
      simp only [List.cons_append, List.cons.injEq] at hq
      obtain ⟨rfl, hq'⟩ := hq
      rw [ih hq' hw₁.2 hw₂.2]

end IsWalk

section Splice

variable {rank : V → ℕ}

/-- **Proposition 5.1, core.** If the common vertices of `Zᵢ` and `Zⱼ` all lie
on a common initial subpath `p`, then any two walk prefixes of `Zᵢ` and `Zⱼ`
ending at the same vertex coincide.
@isnad1 id=eq.9h17v.s7.71832b6b4291 from=translated src=- shape=db182aee vocab=99898ff2
-/
theorem splice_prefix_eq (hrank : ∀ e, rank (src e) < rank (dst e))
    {sV ti v : V} {Zi Zj p ri rj qi si qj sj : List A}
    (hZi : IsWalk src dst sV ti Zi)
    (hpi : Zi = p ++ ri) (hpj : Zj = p ++ rj)
    (hcommon : ∀ x, x ∈ vertexTrace dst sV Zi → x ∈ vertexTrace dst sV Zj →
      x ∈ vertexTrace dst sV p)
    (hqi : Zi = qi ++ si) (hwi : IsWalk src dst sV v qi)
    (hqj : Zj = qj ++ sj) (hwj : IsWalk src dst sV v qj) :
    qj = qi := by
  -- the splice vertex is common to both paths
  have hvZi : v ∈ vertexTrace dst sV Zi := by
    rw [hqi, vertexTrace_append]
    exact List.mem_append_left _ hwi.end_mem_vertexTrace
  have hvZj : v ∈ vertexTrace dst sV Zj := by
    rw [hqj, vertexTrace_append]
    exact List.mem_append_left _ hwj.end_mem_vertexTrace
  have hvp : v ∈ vertexTrace dst sV p := hcommon v hvZi hvZj
  -- p is a walk from s, so it has a prefix `p₁` ending at `v`
  obtain ⟨m, hpm, -⟩ := IsWalk.append_inv (hpi ▸ hZi)
  obtain ⟨p₁, p₂, hp12, hwp1⟩ := hpm.exists_prefix_of_mem_vertexTrace hvp
  -- `p₁` is a prefix of both `Zi` and `Zj`; conclude by prefix determinism
  have hqi_eq : qi = p₁ :=
    IsWalk.prefix_unique hrank
      (by rw [← hqi, hpi, hp12, List.append_assoc]) hwi hwp1
  have hqj_eq : qj = p₁ :=
    IsWalk.prefix_unique hrank
      (by rw [← hqj, hpj, hp12, List.append_assoc]) hwj hwp1
  rw [hqi_eq, hqj_eq]

/-- **Proposition 5.1 (no reconvergence rules out splices).** If once two
cheap paths diverge they never share a vertex again (their common vertices
lie on the shared initial subpath `p`), then every splice — an initial
segment of `Zⱼ` up to a common vertex `v`, continued by the tail of `Zᵢ`
from `v` — is `Zᵢ` itself.
@isnad1 id=eq.9h17v.s7.d087d60ab8ee from=translated src=- shape=410dca4c vocab=99898ff2
-/
theorem splice_eq (hrank : ∀ e, rank (src e) < rank (dst e))
    {sV ti v : V} {Zi Zj p ri rj qi si qj sj : List A}
    (hZi : IsWalk src dst sV ti Zi)
    (hpi : Zi = p ++ ri) (hpj : Zj = p ++ rj)
    (hcommon : ∀ x, x ∈ vertexTrace dst sV Zi → x ∈ vertexTrace dst sV Zj →
      x ∈ vertexTrace dst sV p)
    (hqi : Zi = qi ++ si) (hwi : IsWalk src dst sV v qi)
    (hqj : Zj = qj ++ sj) (hwj : IsWalk src dst sV v qj) :
    qj ++ si = Zi := by
  rw [splice_prefix_eq hrank hZi hpi hpj hcommon hqi hwi hqj hwj]
  exact hqi.symm

end Splice

/-! ### The union of a no-reconvergence path family is an arborescence -/

section Arborescence

variable {ι : Type*} {rank : V → ℕ} {sV : V} {terminal : ι → V}

/-- Two source-rooted paths have the no-reconvergence property when they
share an exact initial arc prefix and every vertex common to both paths lies
on that prefix.-/
def CommonInitialPrefix (dst : A → V) (sV : V) (Zi Zj : List A) : Prop :=
  ∃ p ri rj, Zi = p ++ ri ∧ Zj = p ++ rj ∧
    ∀ x, x ∈ vertexTrace dst sV Zi → x ∈ vertexTrace dst sV Zj →
      x ∈ vertexTrace dst sV p

/-- Every path has itself as a common initial prefix.
@isnad1 id=commonin.0h5v.s4.197b4d63c2a9 from=translated src=- shape=db5e07d7 vocab=68a7f39a
-/
@[refl] theorem CommonInitialPrefix.refl (dst : A → V) (sV : V) (Z : List A) :
    CommonInitialPrefix dst sV Z Z := by
  exact ⟨Z, [], [], by simp, by simp, fun _ hx _ => hx⟩

/-- The common-initial-prefix relation is symmetric.
@isnad1 id=commonin.1h6v.s4.cf9bd0bd1abd from=translated src=- shape=dbd662b2 vocab=68a7f39a
-/
@[symm] theorem CommonInitialPrefix.symm
    {dst : A → V} {sV : V} {Zi Zj : List A}
    (h : CommonInitialPrefix dst sV Zi Zj) :
    CommonInitialPrefix dst sV Zj Zi := by
  obtain ⟨p, ri, rj, hpi, hpj, hcommon⟩ := h
  exact ⟨p, rj, ri, hpj, hpi, fun x hxj hxi => hcommon x hxi hxj⟩

/-- Pairwise no-reconvergence for a family of source-rooted paths.-/
def PairwiseNoReconvergence (dst : A → V) (sV : V) (Z : ι → List A) : Prop :=
  ∀ i j, CommonInitialPrefix dst sV (Z i) (Z j)

/-- To establish pairwise no-reconvergence it suffices to check distinct
indices; the diagonal cases are automatic.
@isnad1 id=pairwise.1h6v.s5.b2b1ed3f2f8f from=translated src=- shape=a6d0b3f0 vocab=640c7e0c
-/
theorem PairwiseNoReconvergence.of_ne
    {dst : A → V} {sV : V} {Z : ι → List A}
    (hno : ∀ i j, i ≠ j → CommonInitialPrefix dst sV (Z i) (Z j)) :
    PairwiseNoReconvergence dst sV Z := by
  intro i j
  by_cases hij : i = j
  · subst j
    exact CommonInitialPrefix.refl dst sV (Z i)
  · exact hno i j hij

/-- The vertices occurring on at least one path in `Z`. The endpoint maps are
both parameters so the induced quiver instance is determined by this type.-/
def PathUnionVertex (_src dst : A → V) (sV : V) (Z : ι → List A) : Type _ :=
  {v : V // ∃ i, v ∈ vertexTrace dst sV (Z i)}

/-- Union vertices are equal when their ambient vertices are equal.
@isnad1 id=eq.1h9v.s6.c3567e65b250 from=translated src=- shape=8169e840 vocab=e0285ff0
-/
@[ext]
theorem PathUnionVertex.ext {Z : ι → List A}
    {u v : PathUnionVertex src dst sV Z} (h : u.1 = v.1) : u = v := by
  exact Subtype.ext h

/-- An arrow in the path union is an ambient arc occurring on at least one
family path, with its endpoints restricted to union vertices.-/
@[ext]
structure PathUnionArrow (src dst : A → V) (sV : V) (Z : ι → List A)
    (u v : PathUnionVertex src dst sV Z) where
  /-- The underlying ambient arc.-/
  edge : A
  mem : ∃ i, edge ∈ Z i
  source_eq : src edge = u.1
  target_eq : dst edge = v.1

/-- The quiver structure on the union of a path family.-/
instance pathUnionQuiver (src dst : A → V) (sV : V) (Z : ι → List A) :
    Quiver (PathUnionVertex src dst sV Z) where
  Hom := PathUnionArrow src dst sV Z

/-- The common source, regarded as a vertex of a nonempty path family.-/
def pathUnionRoot (src dst : A → V) (sV : V) (Z : ι → List A) (i₀ : ι) :
    PathUnionVertex src dst sV Z :=
  ⟨sV, ⟨i₀, by simp [vertexTrace]⟩⟩

/-- Pairwise no-reconvergence makes source-to-vertex prefixes agree even
when the prefixes come from different family paths.
@isnad1 id=eq.7h16v.s7.b8a8c8b864cc from=translated src=- shape=954758c3 vocab=54e4eed0
-/
theorem path_prefix_eq
    (hrank : ∀ e, rank (src e) < rank (dst e))
    {Z : ι → List A} (hZ : ∀ i, IsWalk src dst sV (terminal i) (Z i))
    (hno : PairwiseNoReconvergence dst sV Z)
    {i j : ι} {v : V} {qi si qj sj : List A}
    (hqi : Z i = qi ++ si) (hwi : IsWalk src dst sV v qi)
    (hqj : Z j = qj ++ sj) (hwj : IsWalk src dst sV v qj) :
    qj = qi := by
  obtain ⟨p, ri, rj, hpi, hpj, hcommon⟩ := hno i j
  exact splice_prefix_eq hrank (hZ i) hpi hpj hcommon hqi hwi hqj hwj

/-- Every arrow in the path-union quiver strictly increases the ambient
rank.
@isnad1 id=lt.1h11v.s7.b529da2137ac from=translated src=- shape=313cba73 vocab=3b5ec9a5
-/
theorem pathUnionArrow_rank_lt
    (hrank : ∀ e, rank (src e) < rank (dst e))
    {Z : ι → List A} {u v : PathUnionVertex src dst sV Z}
    (e : u ⟶ v) :
    rank u.1 < rank v.1 := by
  simpa only [e.source_eq, e.target_eq] using hrank e.edge

/-- In a pairwise no-reconverging family, two union arrows with the same
target are the same ambient arc and therefore have the same source.
@isnad1 id=and.3h14v.s7.78930c9da144 from=translated src=- shape=22d85cd5 vocab=d3e73541
-/
theorem pathUnion_unique_incoming
    (hrank : ∀ e, rank (src e) < rank (dst e))
    {Z : ι → List A} (hZ : ∀ i, IsWalk src dst sV (terminal i) (Z i))
    (hno : PairwiseNoReconvergence dst sV Z)
    {u v w : PathUnionVertex src dst sV Z}
    (e : u ⟶ w) (f : v ⟶ w) :
    u = v ∧ e ≍ f := by
  obtain ⟨i, hei⟩ := e.mem
  obtain ⟨j, hfj⟩ := f.mem
  obtain ⟨qi, si, hqi, hwi⟩ := (hZ i).exists_prefix_through_of_mem hei
  obtain ⟨qj, sj, hqj, hwj⟩ := (hZ j).exists_prefix_through_of_mem hfj
  have hwi' : IsWalk src dst sV w.1 (qi ++ [e.edge]) := by
    simpa only [e.target_eq] using hwi
  have hwj' : IsWalk src dst sV w.1 (qj ++ [f.edge]) := by
    simpa only [f.target_eq] using hwj
  have hpref : qj ++ [f.edge] = qi ++ [e.edge] :=
    path_prefix_eq hrank hZ hno hqi hwi' hqj hwj'
  have hedge : f.edge = e.edge := by
    have hrev := congrArg List.reverse hpref
    have hp := by
      simpa only [List.reverse_append, List.reverse_singleton, List.singleton_append,
        List.cons.injEq] using hrev
    exact hp.1
  have huv : u = v := by
    apply PathUnionVertex.ext
    rw [← e.source_eq, ← f.source_eq, hedge]
  refine ⟨huv, ?_⟩
  subst v
  apply heq_of_eq
  apply PathUnionArrow.ext
  exact hedge.symm

/-- Every path-union vertex is the common source or has an incoming union
arrow. This is the reachability premise used by `Quiver.arborescenceMk`.
@isnad1 id=or.1h10v.s6.43e69dfb06f9 from=translated src=- shape=00e13b97 vocab=4828bff3
-/
theorem pathUnion_root_or_incoming
    {Z : ι → List A} (hZ : ∀ i, IsWalk src dst sV (terminal i) (Z i))
    (i₀ : ι) (v : PathUnionVertex src dst sV Z) :
    v = pathUnionRoot src dst sV Z i₀ ∨
      ∃ u, Nonempty (u ⟶ v) := by
  by_cases hv : v.1 = sV
  · exact Or.inl (PathUnionVertex.ext hv)
  · rcases v.2 with ⟨i, hvi⟩
    simp only [vertexTrace, List.mem_cons] at hvi
    rcases hvi with hvi | hvi
    · exact False.elim (hv hvi)
    · obtain ⟨e, hei, hev⟩ := List.mem_map.mp hvi
      obtain ⟨q, r, hqr, hq⟩ := (hZ i).exists_prefix_cons_of_mem hei
      have hsrc : src e ∈ vertexTrace dst sV (Z i) := by
        rw [hqr, vertexTrace_append]
        exact List.mem_append_left _ hq.end_mem_vertexTrace
      let u : PathUnionVertex src dst sV Z := ⟨src e, ⟨i, hsrc⟩⟩
      refine Or.inr ⟨u, ⟨?_⟩⟩
      exact
        { edge := e
          mem := ⟨i, hei⟩
          source_eq := rfl
          target_eq := hev }

/-- **Proposition 5.1, arborescence form.** The quiver formed by the union of
a nonempty family of ranked source-rooted paths with pairwise
no-reconvergence is an out-arborescence rooted at their common source.-/
@[implicit_reducible]
noncomputable def pathUnionArborescence
    (hrank : ∀ e, rank (src e) < rank (dst e))
    {Z : ι → List A} (hZ : ∀ i, IsWalk src dst sV (terminal i) (Z i))
    (hno : PairwiseNoReconvergence dst sV Z) (i₀ : ι) :
    Quiver.Arborescence (PathUnionVertex src dst sV Z) :=
  Quiver.arborescenceMk (pathUnionRoot src dst sV Z i₀) (fun v => rank v.1)
    (fun ⦃_ _⦄ e =>
      pathUnionArrow_rank_lt (src := src) (dst := dst) (rank := rank) hrank e)
    (fun ⦃_ _ _⦄ e f =>
      pathUnion_unique_incoming (src := src) (dst := dst) (rank := rank)
        (sV := sV) (terminal := terminal) hrank hZ hno e f)
    (pathUnion_root_or_incoming (src := src) (dst := dst) (sV := sV)
      (terminal := terminal) hZ i₀)

/-- The root stored in the path-union arborescence is the common source.
@isnad1 id=eq.3h10v.s6.79e3eadc39b6 from=translated src=- shape=9b57a4ea vocab=0421cd9f
-/
theorem pathUnion_arborescence_root
    (hrank : ∀ e, rank (src e) < rank (dst e))
    {Z : ι → List A} (hZ : ∀ i, IsWalk src dst sV (terminal i) (Z i))
    (hno : PairwiseNoReconvergence dst sV Z) (i₀ : ι) :
    (pathUnionArborescence hrank hZ hno i₀).root =
      pathUnionRoot src dst sV Z i₀ := by
  unfold pathUnionArborescence Quiver.arborescenceMk
  rfl

/-- Every vertex in the path union is reachable from the common source.
@isnad1 id=nonempty.3h11v.s6.4c5141c48fcb from=translated src=- shape=f841555d vocab=b4601fdd
-/
theorem pathUnion_root_reachable
    (hrank : ∀ e, rank (src e) < rank (dst e))
    {Z : ι → List A} (hZ : ∀ i, IsWalk src dst sV (terminal i) (Z i))
    (hno : PairwiseNoReconvergence dst sV Z) (i₀ : ι)
    (v : PathUnionVertex src dst sV Z) :
    Nonempty (Quiver.Path (pathUnionRoot src dst sV Z i₀) v) := by
  have hUnique := (pathUnionArborescence hrank hZ hno i₀).uniquePath v
  rw [pathUnion_arborescence_root hrank hZ hno i₀] at hUnique
  exact ⟨hUnique.default⟩

/-- The directed path from the common source to a union vertex is unique.
@isnad1 id=eq.3h13v.s7.79d6f8c9727b from=translated src=- shape=8254c675 vocab=1ceb15d8
-/
theorem pathUnion_root_path_unique
    (hrank : ∀ e, rank (src e) < rank (dst e))
    {Z : ι → List A} (hZ : ∀ i, IsWalk src dst sV (terminal i) (Z i))
    (hno : PairwiseNoReconvergence dst sV Z) (i₀ : ι)
    {v : PathUnionVertex src dst sV Z}
    (p q : Quiver.Path (pathUnionRoot src dst sV Z i₀) v) :
    p = q := by
  have hUnique := (pathUnionArborescence hrank hZ hno i₀).uniquePath v
  rw [pathUnion_arborescence_root hrank hZ hno i₀] at hUnique
  exact (hUnique.uniq p).trans (hUnique.uniq q).symm

end Arborescence

end Goemans
