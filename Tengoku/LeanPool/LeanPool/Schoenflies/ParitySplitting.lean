/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import Tengoku.LeanPool.LeanPool.Schoenflies.PolygonalJordan
public import Tengoku.LeanPool.LeanPool.Schoenflies.OverlayGraph

/-!
# Parity splitting: a crosscut adds the two crossing counts

Lemma 2.7. A crosscut `P` of a simple closed polygon `C` cuts it into two arcs `A₁, A₂`, and
the two closed curves `Jᵢ = Aᵢ ∪ P` satisfy `π_C = π_{J₁} + π_{J₂}` off `C ∪ P`. The blueprint
calls this identity "the whole of the polygonal crosscut theorem": Lemma 2.6 exhibits two cells
of `Ω ∖ P`, and this is what says there are no others.

## Where the split is made, and why

The crossing count of `Schoenflies/Parity.lean` is a function of a `List Piece`, not of a set,
and not of a `ClosedPolygon`. Two edge lists with the same carrier can have different parity —
a list that traverses one segment twice is the obvious example — so the identity cannot be
stated for the sets `Aᵢ ∪ P`. It is stated, and proved, for **edge lists**:

    the edge list of `C` is `A₁ ++ A₂`, that of `Jᵢ` is `Aᵢ ++ K`,

where `K` is the edge list of the crosscut. Then `π_{J₁} + π_{J₂} = π_{A₁} + π_{A₂} + 2 π_K`
and the crosscut's contribution cancels mod `2`. That is `parity_split`, and it needs no
geometry at all — no simplicity, no direction, no separation. Everything the blueprint's
picture contributes is in the *hypothesis* that the lists decompose that way.

Two mismatches between "the edge list of `Jᵢ` is `Aᵢ` together with `K`" and literal list
equality have to be absorbed, because a consumer building `Jᵢ` as a `ClosedPolygon` controls
neither:

* the edges come in some cyclic order of that polygon's own choosing, and
* one of the two curves must traverse the crosscut backwards, so its pieces are the *reversed*
  pairs.

`SameEdges` is the equivalence that forgives exactly these two: a permutation of the lists
after each piece has been put in canonical order by `Schoenflies.orientPiece`. Parity, carrier,
closedness and non-levelness are all invariant under it (`SameEdges.parity_eq`,
`SameEdges.cover_eq`, `SameEdges.isChainFrom`, `SameEdges.hgt_ne`), so a consumer may hand over
its edge list in whatever order and orientation it happens to have —
`sameEdges_of_perm_reverse_swap` absorbs both mismatches in one step.

Nothing is assumed about the *sets*: `ClosedPolygon.carrier_eq_of_sameEdges` derives
`Jᵢ.carrier = Aᵢ ∪ P` from the edge lists alone, so the geometric hypothesis a consumer has to
discharge is only ever combinatorial.

## The construction

`ClosedPolygon.arcPieces C a k` is the edge list of the arc of `C` that leaves vertex `a` and
runs forward through `k` edges — the object the split produces, exported as an object rather
than hidden behind an existential. Its two governing facts are

* `ClosedPolygon.arcPieces_split_perm`: `arcPieces C a k ++ arcPieces C (a + k) (m + 3 - k)` is
  a permutation of `C.pieces` — the arcs really do partition the edges; and
* `ClosedPolygon.isChainFrom_arcPieces`: the arc's mod-`2` boundary is its two end vertices,
  which is what makes `Aᵢ ++ K` a *closed* chain and hence eligible for every parity theorem.

`IsChainFrom` is the open-path companion of `Schoenflies.IsClosedChain`, stated by the same
duality; `IsChainFrom.isClosedChain_append` is the one-line reason that an arc and a crosscut
with the same two ends close up. `pathPieces` turns a polyline into such a chain, which is how
the crosscut itself is normally presented.

The endpoints of the crosscut are taken to be **vertices** of `C`; the blueprint's opening
move, "subdivide `C` at `p` and `q`", is what puts them there, and is `parity_subdivide`
(Lemma 2.1) applied before any of this. Nothing below re-proves it. A consumer whose crosscut
lands in the interiors of edges rewrites with `parity_subdivide` first and then applies
`parity_split` to the subdivided list, whose hypotheses are about lists and not about polygons;
what such a consumer must supply for itself is the decomposition of the *subdivided* list into
two arcs, which `arcPieces` does not provide — `arcPieces` splits `C.pieces` at vertices.

## Blueprint

* `SameEdges`, `IsChainFrom`, `pathPieces`, `ClosedPolygon.arcPieces` — the definition of the
  split. "After the subdivision the edge set of `C` is the disjoint union of the edge sets of
  `A₁` and `A₂`, and the edge set of `Jᵢ` is that of `Aᵢ` together with that of `P`."
* `parity_split`, `ClosedPolygon.parity_splitting` — Lemma 2.7, equation (2.2)
  `π_C = π_{J₁} + π_{J₂}`.
* `ClosedPolygon.crosscut_inside_exactly_one`, `ClosedPolygon.crosscut_outside_agree` — the
  "Consequently" of Lemma 2.7, which is where Theorem 2.3 enters: a point of `Int(C)` off `P`
  lies inside exactly one of `J₁, J₂`, and a point of `Ext(C)` off `P` lies inside both or
  inside neither.
* `ClosedPolygon.parity_eq_one_iff` — the two halves of the last sentence of Theorem 2.3, read
  as a single criterion.
* `ClosedPolygon.carrier_eq_of_sameEdges`, `ClosedPolygon.notMem_carrier_of_sameEdges` — the
  bridge back to the sets: `Jᵢ` occupies `Aᵢ ∪ P`, so "off `C` and off `P`" is "off `Jᵢ`".

One lemma here strengthens one on `main`: `mark_swap'` drops the non-levelness hypothesis of
`Schoenflies.mark_swap`, because a level edge is crossed from nowhere and so contributes `0`
under either name. Its home is `Schoenflies/Parity.lean`.
-/

@[expose] public section

open Metric Set

namespace Schoenflies

variable {u p q r : Plane} {L L₁ L₂ L₃ : List Piece} {m : ℕ}

/-! ## Edge lists up to order and orientation

Parity, carrier and closedness are all functions of the *multiset of unoriented* edges. This
section says so, so that a consumer may present the edge list of a curve in any order and with
either name for each edge. -/

/-- A level edge is crossed from nowhere: the ray from `q` would have to leave at a height both
`≥` and `<` the common height of the two ends.
@isnad1 id=not.1h4v.s4.e7128fa852a0 from=translated src=- shape=afad9852 vocab=61e0d136
-/
theorem not_crosses_of_level {c d : Plane} (h : hgt u c = hgt u d) (q : Plane) :
    ¬ Crosses u (c, d) q := by
  intro hcr
  obtain ⟨h1, h2, -⟩ := hcr
  have e1 : ((c, d) : Piece).1 = c := rfl
  have e2 : ((c, d) : Piece).2 = d := rfl
  rw [e1, e2, h, min_self] at h1
  rw [e1, e2, h, max_self] at h2
  linarith

/-- **The contribution of an edge does not depend on which end is named first.** This is
`Schoenflies.mark_swap` with its non-levelness hypothesis removed: a level edge contributes `0`
under either name.
@isnad1 id=eq.0h3v.s4.4625f12ee498 from=translated src=- shape=2ca751d7 vocab=156aa66f
-/
theorem mark_swap' (u : Plane) (P : Piece) (q : Plane) : mark u (P.2, P.1) q = mark u P q := by
  obtain ⟨a, b⟩ := P
  by_cases h : hgt u a = hgt u b
  · rw [mark, mark,
      ite_eq_right (not_crosses_of_level h.symm q),
          ite_eq_right (not_crosses_of_level h q)]
  · exact mark_swap h q

/-- Reordering the edges does not change the count.
@isnad1 id=eq.1h4v.s4.f02670417299 from=translated src=- shape=da5b9769 vocab=ff8e4fa8
-/
theorem parity_perm (h : L₁.Perm L₂) (u q : Plane) : parity u L₁ q = parity u L₂ q :=
  (h.map fun P => mark u P q).sum_eq

/-- Reordering the edges does not change what they occupy.
@isnad1 id=eq.1h2v.s4.4c491c5446ca from=translated src=- shape=fb193f49 vocab=4e5ebaf3
-/
theorem cover_perm (h : L₁.Perm L₂) : cover L₁ = cover L₂ := by
  ext z
  simp only [cover, mem_iUnion, exists_prop]
  exact ⟨fun ⟨P, hP, hz⟩ => ⟨P, h.mem_iff.1 hP, hz⟩, fun ⟨P, hP, hz⟩ => ⟨P, h.mem_iff.2 hP, hz⟩⟩

/-- `orientPiece` either leaves a piece alone or reverses it; that is all this file uses.
@isnad1 id=or.0h1v.s4.b995b90b45e7 from=translated src=- shape=bf9b063a vocab=d626b6df
-/
theorem orientPiece_eq_or (P : Piece) : orientPiece P = P ∨ orientPiece P = (P.2, P.1) := by
  by_cases h : Precedes P.1 P.2
  · exact Or.inl (orientPiece_of_precedes h)
  · exact Or.inr (orientPiece_of_not_precedes h)

/--
@isnad1 id=eq.0h3v.s4.d8a7e8606109 from=translated src=- shape=8291d47a vocab=8842e4fc
-/
theorem mark_orientPiece (u : Plane) (P : Piece) (q : Plane) :
    mark u (orientPiece P) q = mark u P q := by
  rcases orientPiece_eq_or P with h | h
  · rw [h]
  · rw [h, mark_swap']

/--
@isnad1 id=eq.0h3v.s4.aa33fe6fe9ae from=translated src=- shape=cf709ba8 vocab=79e005d1
-/
theorem parity_map_orientPiece (u : Plane) (L : List Piece) (q : Plane) :
    parity u (L.map orientPiece) q = parity u L q := by
  simp only [parity, List.map_map]
  exact congrArg List.sum (List.map_congr_left fun P _ => mark_orientPiece u P q)

/--
@isnad1 id=ne.1h2v.s5.0a42277ac09e from=translated src=- shape=8bdc89e7 vocab=adad3589
-/
theorem hgt_ne_orientPiece {P : Piece} (h : hgt u P.1 ≠ hgt u P.2) :
    hgt u (orientPiece P).1 ≠ hgt u (orientPiece P).2 := by
  rcases orientPiece_eq_or P with e | e
  · rw [e]; exact h
  · rw [e]; exact fun hh => h hh.symm

/--
@isnad1 id=ne.1h2v.s5.f1197bb55827 from=translated src=- shape=6ab63e3b vocab=adad3589
-/
theorem hgt_ne_of_orientPiece {P : Piece} (h : hgt u (orientPiece P).1 ≠ hgt u (orientPiece P).2) :
    hgt u P.1 ≠ hgt u P.2 := by
  rcases orientPiece_eq_or P with e | e
  · rw [e] at h; exact h
  · rw [e] at h; exact fun hh => h hh.symm

/-- Orienting a piece does not change its mod-`2` boundary.
@isnad1 id=eq.0h2v.s8.0589cd724e1c from=translated src=- shape=f42ac4eb vocab=1dbe6ea2
-/
theorem chainSum_map_orientPiece (f : Plane → ZMod 2) (L : List Piece) :
    ((L.map orientPiece).map fun P => f P.1 + f P.2).sum
      = (L.map fun P => f P.1 + f P.2).sum := by
  simp only [List.map_map]
  refine congrArg List.sum (List.map_congr_left fun P _ => ?_)
  rcases orientPiece_eq_or P with e | e
  · rw [Function.comp_apply, e]
  · rw [Function.comp_apply, e]; exact add_comm _ _

/-- **Two edge lists carry the same edges**: they agree after reordering, each edge being free
to be named by either of its two ends first. This is the relation under which "the edge list of
`Jᵢ` is that of `Aᵢ` together with that of `P`" is true — a `ClosedPolygon` built on `Aᵢ ∪ P`
lists its edges in its own cyclic order, and traverses one of the two pieces backwards. -/
def SameEdges (L₁ L₂ : List Piece) : Prop := (L₁.map orientPiece).Perm (L₂.map orientPiece)

/--
@isnad1 id=sameedge.0h1v.s2.7a4d8510eb04 from=translated src=- shape=3bd27ae8 vocab=d6e78b28
-/
@[refl] theorem SameEdges.refl (L : List Piece) : SameEdges L L := List.Perm.refl _

/--
@isnad1 id=sameedge.1h2v.s3.c9b6401bc34f from=translated src=- shape=55c7d06a vocab=d6e78b28
-/
theorem SameEdges.symm (h : SameEdges L₁ L₂) : SameEdges L₂ L₁ := List.Perm.symm h

/--
@isnad1 id=sameedge.2h3v.s4.1aba54afee31 from=translated src=- shape=11350b13 vocab=d6e78b28
-/
theorem SameEdges.trans (h₁ : SameEdges L₁ L₂) (h₂ : SameEdges L₂ L₃) : SameEdges L₁ L₃ :=
  List.Perm.trans h₁ h₂

/-- A reordering is in particular the same edges.
@isnad1 id=sameedge.1h2v.s3.e0b05f91dbb3 from=translated src=- shape=5d62446c vocab=29d6d179
-/
theorem SameEdges.of_perm (h : L₁.Perm L₂) : SameEdges L₁ L₂ := h.map _

/--
@isnad1 id=sameedge.2h4v.s5.d8e0b7f82c73 from=translated src=- shape=42b4f87d vocab=370b02fd
-/
theorem SameEdges.append {L₁' L₂' : List Piece} (h₁ : SameEdges L₁ L₁') (h₂ : SameEdges L₂ L₂') :
    SameEdges (L₁ ++ L₂) (L₁' ++ L₂') := by
  simpa only [SameEdges, List.map_append] using List.Perm.append h₁ h₂

/--
@isnad1 id=sameedge.0h1v.s3.f7a473cf06f7 from=translated src=- shape=e14d3d90 vocab=8b6c2438
-/
theorem sameEdges_reverse (L : List Piece) : SameEdges L.reverse L :=
  SameEdges.of_perm (List.reverse_perm L)

/-- **Reversing every edge changes nothing.** This is the clause a consumer needs when its
second curve traverses the crosscut backwards.
@isnad1 id=sameedge.0h1v.s4.842b3b8f0e0a from=translated src=- shape=6a03c076 vocab=11458d5d
-/
theorem sameEdges_map_swap (L : List Piece) : SameEdges (L.map fun P => (P.2, P.1)) L := by
  have : (L.map fun P => (P.2, P.1)).map orientPiece = L.map orientPiece := by
    rw [List.map_map]
    exact List.map_congr_left fun P _ => orientPiece_swap P
  rw [SameEdges, this]

/-- **The shape a consumer arrives with.** A `ClosedPolygon` built on `Aᵢ ∪ P` lists its edges
in a cyclic order of its own choosing — any permutation — and one of the two must run the
crosscut backwards, which reverses the list and names every piece the other way round. All of
that is forgiven at once.
@isnad1 id=sameedge.1h3v.s6.84bfd5c06236 from=translated src=- shape=1ecdb8ee vocab=3b15d936
-/
theorem sameEdges_of_perm_reverse_swap {L A K : List Piece}
    (h : L.Perm (A ++ (K.map fun P => (P.2, P.1)).reverse)) : SameEdges L (A ++ K) :=
  (SameEdges.of_perm h).trans
    (SameEdges.append (SameEdges.refl A) ((sameEdges_reverse _).trans (sameEdges_map_swap K)))

/--
@isnad1 id=eq.1h4v.s4.e682051139cd from=translated src=- shape=3104a4aa vocab=df54a680
-/
theorem SameEdges.parity_eq (h : SameEdges L₁ L₂) (u q : Plane) :
    parity u L₁ q = parity u L₂ q := by
  rw [← parity_map_orientPiece u L₁ q, ← parity_map_orientPiece u L₂ q]
  exact parity_perm h u q

/--
@isnad1 id=eq.1h2v.s4.12c0437837a6 from=translated src=- shape=c6e7d9d0 vocab=f51d95d5
-/
theorem SameEdges.cover_eq (h : SameEdges L₁ L₂) : cover L₁ = cover L₂ := by
  rw [← cover_map_orientPiece L₁, ← cover_map_orientPiece L₂]
  exact cover_perm h

/-- Every edge of `L₁` is an edge of `L₂`, up to the naming of its two ends.
@isnad1 id=ex.2h3v.s5.77a42d958db1 from=translated src=- shape=9aac4eee vocab=f175e5fb
-/
theorem SameEdges.exists_mem (h : SameEdges L₁ L₂) {Q : Piece} (hQ : Q ∈ L₁) :
    ∃ R ∈ L₂, orientPiece R = orientPiece Q := by
  have hmem : orientPiece Q ∈ L₂.map orientPiece :=
    h.mem_iff.1 (List.mem_map_of_mem (f := orientPiece) hQ)
  obtain ⟨R, hR, hRQ⟩ := List.mem_map.1 hmem
  exact ⟨R, hR, hRQ⟩

/-- Non-levelness for a direction transfers: it is a property of the unoriented edge.
@isnad1 id=ne.3h4v.s5.41ac0dba12a3 from=translated src=- shape=cf54e664 vocab=8fa16ecb
-/
theorem SameEdges.hgt_ne (h : SameEdges L₁ L₂) (hL : ∀ Q ∈ L₂, hgt u Q.1 ≠ hgt u Q.2) :
    ∀ Q ∈ L₁, hgt u Q.1 ≠ hgt u Q.2 := by
  intro Q hQ
  obtain ⟨R, hR, hRQ⟩ := h.exists_mem hQ
  exact hgt_ne_of_orientPiece (hRQ ▸ hgt_ne_orientPiece (hL R hR))

/--
@isnad1 id=ne.3h4v.s6.c110ab5c474b from=translated src=- shape=21c3bac1 vocab=d0c5587b
-/
theorem hgt_ne_append (h₁ : ∀ Q ∈ L₁, hgt u Q.1 ≠ hgt u Q.2)
    (h₂ : ∀ Q ∈ L₂, hgt u Q.1 ≠ hgt u Q.2) : ∀ Q ∈ L₁ ++ L₂, hgt u Q.1 ≠ hgt u Q.2 := by
  intro Q hQ
  rcases List.mem_append.1 hQ with h | h
  · exact h₁ Q h
  · exact h₂ Q h

/-! ## Chains with two ends

`Schoenflies.IsClosedChain` says the mod-`2` boundary of an edge list vanishes. An arc and a
crosscut are not closed; each has a boundary, namely its two ends, and closing them up is the
statement that the two boundaries agree. Stated by the same duality as `IsClosedChain`, so that
the two definitions compose with nothing but `List.sum_append`. -/

/-- `L` is a **chain from `p` to `q`**: its mod-`2` boundary is `p` together with `q`. Stated by
duality, exactly as `Schoenflies.IsClosedChain` is. -/
def IsChainFrom (L : List Piece) (p q : Plane) : Prop :=
  ∀ f : Plane → ZMod 2, (L.map fun P => f P.1 + f P.2).sum = f p + f q

/-- A chain whose two ends coincide is a closed chain, and conversely.
@isnad1 id=iff.0h2v.s3.43e844656b19 from=translated src=- shape=e282d9a7 vocab=e082ee69
-/
theorem isChainFrom_self_iff : IsChainFrom L p p ↔ IsClosedChain L := by
  constructor <;> intro h f
  · rw [h f]; exact add_self_zmod_two _
  · rw [h f]; exact (add_self_zmod_two _).symm

/--
@isnad1 id=ischainf.0h1v.s2.5ea87725cdf3 from=translated src=- shape=7bbaa5c9 vocab=339bcd2a
-/
theorem isChainFrom_nil (p : Plane) : IsChainFrom [] p p := fun f => by
  simp [(add_self_zmod_two (f p)).symm]

/-- Chains compose end to end.
@isnad1 id=ischainf.2h5v.s5.dc939b42fdca from=translated src=- shape=2ca5a0f4 vocab=d210a3d5
-/
theorem IsChainFrom.append (h₁ : IsChainFrom L₁ p q) (h₂ : IsChainFrom L₂ q r) :
    IsChainFrom (L₁ ++ L₂) p r := by
  intro f
  rw [List.map_append, List.sum_append, h₁ f, h₂ f]
  linear_combination add_self_zmod_two (f q)

/-- **Two chains with the same two ends close up.** This is the whole reason `Aᵢ ∪ P` is a
closed curve as far as the crossing count is concerned.
@isnad1 id=isclosed.2h4v.s5.c58b553d1349 from=translated src=- shape=7b1c030f vocab=8480799e
-/
theorem IsChainFrom.isClosedChain_append (h₁ : IsChainFrom L₁ p q) (h₂ : IsChainFrom L₂ p q) :
    IsClosedChain (L₁ ++ L₂) := by
  intro f
  rw [List.map_append, List.sum_append, h₁ f, h₂ f]
  exact add_self_zmod_two _

/--
@isnad1 id=ischainf.2h4v.s4.bac7d426696a from=translated src=- shape=36343e3d vocab=346c86d9
-/
theorem SameEdges.isChainFrom (h : SameEdges L₁ L₂) (h₂ : IsChainFrom L₂ p q) :
    IsChainFrom L₁ p q := by
  intro f
  rw [← chainSum_map_orientPiece f L₁, (h.map fun P => f P.1 + f P.2).sum_eq,
    chainSum_map_orientPiece, h₂ f]

/--
@isnad1 id=isclosed.2h2v.s3.91391ea9c371 from=translated src=- shape=7967fad6 vocab=8081076b
-/
theorem SameEdges.isClosedChain (h : SameEdges L₁ L₂) (h₂ : IsClosedChain L₂) :
    IsClosedChain L₁ := by
  intro f
  rw [← chainSum_map_orientPiece f L₁, (h.map fun P => f P.1 + f P.2).sum_eq,
    chainSum_map_orientPiece, h₂ f]

/-! ### The edges of a polyline

How a crosscut is normally presented: a list of points. `pathPieces` reads off its edges, and
`isChainFrom_pathPieces` says its boundary is the two ends of the list. -/

/-- The edges of the polyline `v₀, v₁, …, v_k`. -/
def pathPieces : List Plane → List Piece
  | [] => []
  | [_] => []
  | v :: w :: rest => (v, w) :: pathPieces (w :: rest)

/--
@isnad1 id=eq.0h0v.s3.223bbaf0b899 from=translated src=- shape=1d803c6d vocab=c1959eff
-/
@[simp] theorem pathPieces_nil : pathPieces [] = [] := rfl

/--
@isnad1 id=eq.0h1v.s3.281d68a109fa from=translated src=- shape=54690142 vocab=c4811d08
-/
@[simp] theorem pathPieces_singleton (v : Plane) : pathPieces [v] = [] := rfl

/--
@isnad1 id=eq.0h3v.s5.29bacdc9d95a from=translated src=- shape=c15b86f2 vocab=544011a1
-/
@[simp] theorem pathPieces_cons_cons (v w : Plane) (rest : List Plane) :
    pathPieces (v :: w :: rest) = (v, w) :: pathPieces (w :: rest) := rfl

/-- **A polyline is a chain from its first point to its last.**
@isnad1 id=ischainf.0h3v.s5.84bbe3b2ea5f from=translated src=- shape=0d6545ed vocab=0ede5f25
-/
theorem isChainFrom_pathPieces (p : Plane) (mid : List Plane) (q : Plane) :
    IsChainFrom (pathPieces (p :: (mid ++ [q]))) p q := by
  induction mid generalizing p with
  | nil =>
    intro f
    simp
  | cons w ws ih =>
    intro f
    rw [List.cons_append, pathPieces_cons_cons, List.map_cons, List.sum_cons, ih w f]
    linear_combination add_self_zmod_two (f w)

/-- The edges of a polyline occupy the polyline.
@isnad1 id=eq.0h3v.s5.5a6512bf261f from=translated src=- shape=70981b7b vocab=18ac8a9b
-/
theorem cover_pathPieces (p : Plane) (mid : List Plane) (q : Plane) :
    cover (pathPieces (p :: (mid ++ [q]))) = poly (p :: (mid ++ [q])) := by
  induction mid generalizing p with
  | nil =>
    rw [List.nil_append, pathPieces_cons_cons, pathPieces_singleton, cover_cons, cover_nil,
      poly_cons_cons, poly_singleton, union_empty]
    exact (union_eq_self_of_subset_right
      (singleton_subset_iff.2 (right_mem_segment ℝ p q))).symm
  | cons w ws ih =>
    rw [List.cons_append, pathPieces_cons_cons, cover_cons, ih w, poly_cons_cons]
    rfl

/-! ## The two arcs of a polygon

`arcPieces C a k` is the edge list of the arc of `C` that leaves vertex `a` and runs forward
through `k` edges. Its two ends are vertices `a` and `a + k`, and for `k ≤ m + 3` the two arcs
`arcPieces C a k` and `arcPieces C (a + k) (m + 3 - k)` between them use each edge of `C`
exactly once. -/

namespace ClosedPolygon

variable {C : ClosedPolygon m} {a : ZMod (m + 3)} {k : ℕ}

/-- The edge list of the arc of `C` that leaves vertex `a` and runs forward through `k` edges.
For `k ≤ m + 3` this is one of the two arcs a crosscut with endpoints `C.vertex a` and
`C.vertex (a + k)` cuts `C` into; the other is `arcPieces C (a + k) (m + 3 - k)`. -/
def arcPieces (C : ClosedPolygon m) (a : ZMod (m + 3)) (k : ℕ) : List Piece :=
  (List.range k).map fun t : ℕ => (C.vertex (a + t), C.vertex (a + t + 1))

/--
@isnad1 id=eq.0h3v.s5.3f50b0505dfe from=translated src=- shape=70346f86 vocab=04b6ae74
-/
@[simp] theorem arcPieces_zero (C : ClosedPolygon m) (a : ZMod (m + 3)) :
    C.arcPieces a 0 = [] := rfl

/-- Running through `k + l` edges is running through `k` and then through `l`.
@isnad1 id=eq.0h5v.s8.a4610fdb8cb7 from=translated src=- shape=3fe6dbe5 vocab=a0a7f0f6
-/
theorem arcPieces_add (C : ClosedPolygon m) (a : ZMod (m + 3)) (k l : ℕ) :
    C.arcPieces a (k + l) = C.arcPieces a k ++ C.arcPieces (a + k) l := by
  rw [arcPieces, arcPieces, arcPieces, List.range_add, List.map_append, List.map_map]
  congr 1
  refine List.map_congr_left fun t _ => ?_
  simp only [Function.comp_apply, Nat.cast_add, ← add_assoc]

/-- Running through all `m + 3` edges from vertex `0` is the whole edge list.
@isnad1 id=eq.0h2v.s7.6ac5133e356e from=translated src=- shape=fea9ec01 vocab=74055e26
-/
theorem arcPieces_full (C : ClosedPolygon m) : C.arcPieces 0 (m + 3) = C.pieces := by
  rw [arcPieces, pieces]
  exact List.map_congr_left fun t _ => by rw [zero_add]

/-- Every edge of an arc is an edge of the polygon; non-levelness and nondegeneracy follow.
@isnad1 id=mem.1h5v.s5.798a6a6e9bee from=translated src=- shape=73f15037 vocab=310452a3
-/
theorem mem_pieces_of_mem_arcPieces {Q : Piece} (hQ : Q ∈ C.arcPieces a k) : Q ∈ C.pieces := by
  obtain ⟨t, -, rfl⟩ := List.mem_map.1 hQ
  exact C.mem_pieces _

/--
@isnad1 id=nondeg.1h5v.s5.afd00b3a5a15 from=translated src=- shape=526bd8cf vocab=e07c2c6a
-/
theorem arcPieces_nondeg (C : ClosedPolygon m) (a : ZMod (m + 3)) (k : ℕ) :
    ∀ Q ∈ C.arcPieces a k, Q.Nondeg :=
  fun _ hQ => C.pieces_nondeg _ (mem_pieces_of_mem_arcPieces hQ)

/--
@isnad1 id=ne.2h6v.s6.a03e0b0e87be from=translated src=- shape=5780bf1f vocab=0d286777
-/
theorem arcPieces_hgt_ne (hL : ∀ Q ∈ C.pieces, hgt u Q.1 ≠ hgt u Q.2) :
    ∀ Q ∈ C.arcPieces a k, hgt u Q.1 ≠ hgt u Q.2 :=
  fun _ hQ => hL _ (mem_pieces_of_mem_arcPieces hQ)

/-- **An arc is a chain from its first vertex to its last.** The telescoping sum of the
blueprint's "counting edge by edge", read off `Schoenflies.sum_range_boundary`.
@isnad1 id=ischainf.0h4v.s8.e36903ac6b90 from=translated src=- shape=3ca35c6e vocab=0876fd51
-/
theorem isChainFrom_arcPieces (C : ClosedPolygon m) (a : ZMod (m + 3)) (k : ℕ) :
    IsChainFrom (C.arcPieces a k) (C.vertex a) (C.vertex (a + k)) := by
  intro f
  have hmap : ((C.arcPieces a k).map fun P => f P.1 + f P.2)
      = (List.range k).map fun j : ℕ =>
          f (C.vertex (a + (j : ZMod (m + 3))))
            + f (C.vertex (a + ((j + 1 : ℕ) : ZMod (m + 3)))) := by
    rw [arcPieces, List.map_map]
    refine List.map_congr_left fun t _ => ?_
    simp only [Function.comp_apply, natCast_succ, ← add_assoc]
  have key := sum_range_boundary (fun i : ℕ => f (C.vertex (a + (i : ZMod (m + 3))))) k
  rw [hmap, key]
  simp

/-- **The two arcs from a vertex use every edge exactly once.** Cutting the cycle at `a` is a
rotation, and a rotation is a permutation: the list is `X ++ Y` and `C.pieces` is `Y ++ X`.
@isnad1 id=perm.0h3v.s5.f78f997c4f2d from=translated src=- shape=f59c1f65 vocab=bd588251
-/
theorem arcPieces_full_perm (C : ClosedPolygon m) (a : ZMod (m + 3)) :
    (C.arcPieces a (m + 3)).Perm C.pieces := by
  have hlt : a.val < m + 3 := ZMod.val_lt a
  have hcast : ((a.val : ℕ) : ZMod (m + 3)) = a := ZMod.natCast_rightInverse a
  -- the tail of the cycle, from `a` back round to `0`
  have hzero : a + ((m + 3 - a.val : ℕ) : ZMod (m + 3)) = 0 := by
    rw [Nat.cast_sub hlt.le, hcast]
    simp
  have hsplit1 : C.arcPieces a (m + 3)
      = C.arcPieces a (m + 3 - a.val) ++ C.arcPieces 0 a.val := by
    have h1 : (m + 3 - a.val) + a.val = m + 3 := by omega
    have h2 := arcPieces_add C a (m + 3 - a.val) a.val
    rwa [h1, hzero] at h2
  have hsplit2 : C.pieces = C.arcPieces 0 a.val ++ C.arcPieces a (m + 3 - a.val) := by
    have h1 : a.val + (m + 3 - a.val) = m + 3 := by omega
    have h2 := arcPieces_add C 0 a.val (m + 3 - a.val)
    rw [h1, arcPieces_full, zero_add, hcast] at h2
    exact h2
  rw [hsplit1, hsplit2]
  exact List.perm_append_comm

/-- **The split.** For `k ≤ m + 3` the two arcs at `a` and `a + k` between them use every edge
of `C` exactly once.
@isnad1 id=perm.1h4v.s8.a97791153379 from=translated src=- shape=91e399b4 vocab=aaa50dfb
-/
theorem arcPieces_split_perm (C : ClosedPolygon m) (a : ZMod (m + 3)) (hk : k ≤ m + 3) :
    (C.arcPieces a k ++ C.arcPieces (a + k) (m + 3 - k)).Perm C.pieces := by
  rw [← arcPieces_add, Nat.add_sub_cancel' hk]
  exact arcPieces_full_perm C a

/--
@isnad1 id=sameedge.1h4v.s8.7aaa2efd9dab from=translated src=- shape=ddbc1f62 vocab=86536b0e
-/
theorem sameEdges_arcPieces_split (C : ClosedPolygon m) (a : ZMod (m + 3)) (hk : k ≤ m + 3) :
    SameEdges C.pieces (C.arcPieces a k ++ C.arcPieces (a + k) (m + 3 - k)) :=
  SameEdges.of_perm (arcPieces_split_perm C a hk).symm

/-- The two arcs between them carry the polygon.
@isnad1 id=eq.1h4v.s8.466608624864 from=translated src=- shape=ba10137a vocab=72658aa8
-/
theorem cover_arcPieces_union (C : ClosedPolygon m) (a : ZMod (m + 3)) (hk : k ≤ m + 3) :
    cover (C.arcPieces a k) ∪ cover (C.arcPieces (a + k) (m + 3 - k)) = C.carrier := by
  rw [← cover_append, cover_perm (arcPieces_split_perm C a hk), cover_pieces]

/--
@isnad1 id=le.0h4v.s5.d0b13d2a1e64 from=translated src=- shape=b295532d vocab=471b34af
-/
theorem cover_arcPieces_subset (C : ClosedPolygon m) (a : ZMod (m + 3)) (k : ℕ) :
    cover (C.arcPieces a k) ⊆ C.carrier := by
  intro z hz
  obtain ⟨R, hR, hzR⟩ := exists_of_mem_cover hz
  rw [← cover_pieces]
  exact mem_cover (mem_pieces_of_mem_arcPieces hR) hzR

/-- **The two curves of the split are closed chains.** An arc from `C.vertex a` to
`C.vertex (a + k)` and a crosscut with the same two ends close up.
@isnad1 id=isclosed.1h5v.s8.3a9f81fd8bbd from=translated src=- shape=b7d5b905 vocab=e7e55264
-/
theorem isClosedChain_arcPieces_append {K : List Piece}
    (hK : IsChainFrom K (C.vertex a) (C.vertex (a + k))) :
    IsClosedChain (C.arcPieces a k ++ K) :=
  (isChainFrom_arcPieces C a k).isClosedChain_append hK

/--
@isnad1 id=ne.3h7v.s6.75e09180c61b from=translated src=- shape=ece98cce vocab=c81c7186
-/
theorem arcPieces_append_hgt_ne {K : List Piece}
    (hC : ∀ Q ∈ C.pieces, hgt u Q.1 ≠ hgt u Q.2) (hK : ∀ Q ∈ K, hgt u Q.1 ≠ hgt u Q.2) :
    ∀ Q ∈ C.arcPieces a k ++ K, hgt u Q.1 ≠ hgt u Q.2 :=
  hgt_ne_append (arcPieces_hgt_ne hC) hK

/-- **A curve of the split occupies its arc together with the crosscut.** Only the edge list of
`J` is assumed related to the split; its carrier then is what the blueprint calls `Aᵢ ∪ P`.
@isnad1 id=eq.1h7v.s6.603e96cfa73a from=translated src=- shape=734b4ca5 vocab=503f3bfe
-/
theorem carrier_eq_of_sameEdges {m' : ℕ} {J : ClosedPolygon m'} {K : List Piece}
    (h : SameEdges J.pieces (C.arcPieces a k ++ K)) :
    J.carrier = cover (C.arcPieces a k) ∪ cover K := by
  rw [← cover_pieces, h.cover_eq, cover_append]

/-- Hence a point off `C` and off the crosscut is off `J`: the blueprint's "a point of
`Int(C)` off `P`" needs nothing else.
@isnad1 id=not.3h8v.s6.c40d605c6e4a from=translated src=- shape=caf5dc9a vocab=0b496a52
-/
theorem notMem_carrier_of_sameEdges {m' : ℕ} {J : ClosedPolygon m'} {K : List Piece}
    (h : SameEdges J.pieces (C.arcPieces a k ++ K)) {x : Plane} (hxC : x ∉ C.carrier)
    (hxK : x ∉ cover K) : x ∉ J.carrier := by
  rw [carrier_eq_of_sameEdges h]
  rintro (hx | hx)
  · exact hxC (cover_arcPieces_subset C a k hx)
  · exact hxK hx

end ClosedPolygon

/-! ## The identity

Everything above was the definition. The identity itself is one line of `ZMod 2` arithmetic:
the crosscut is counted once in each of `π_{J₁}` and `π_{J₂}`, so its contribution cancels. -/

/-- **Parity splitting** (Lemma 2.7), in edge-list form and with no geometry whatever. If the
edge list of `C` is the two arcs `A₁, A₂` and the edge list of `Jᵢ` is `Aᵢ` together with the
crosscut's list `K` — in each case up to reordering and up to reversing individual edges — then
`π_{J₁} + π_{J₂} = π_C` at *every* point of the plane.

The hypotheses carry all of the blueprint's picture; the proof is that `K` is counted twice.
@isnad1 id=eq.3h8v.s7.2c7adca26de3 from=translated src=- shape=ebeb30fd vocab=1741ce06
-/
theorem parity_split (u : Plane) {LC A₁ A₂ K : List Piece}
    (hC : SameEdges LC (A₁ ++ A₂)) (h₁ : SameEdges L₁ (A₁ ++ K)) (h₂ : SameEdges L₂ (A₂ ++ K))
    (q : Plane) : parity u L₁ q + parity u L₂ q = parity u LC q := by
  rw [h₁.parity_eq u q, h₂.parity_eq u q, hC.parity_eq u q, parity_append, parity_append,
    parity_append]
  linear_combination add_self_zmod_two (parity u K q)

namespace ClosedPolygon

variable {C : ClosedPolygon m} {a : ZMod (m + 3)} {k : ℕ}

/-- **Parity splitting** (Lemma 2.7) for a simple closed polygon cut at two of its vertices.
`K` is the edge list of the crosscut, `L₁` and `L₂` the edge lists of the two curves
`Jᵢ = Aᵢ ∪ P`; each is required only to carry the right edges, in any order and with either
name for each edge.

No hypothesis on `K` is needed: whatever it is, it is counted once on each side and cancels.
@isnad1 id=eq.3h9v.s8.2b27a3accfa9 from=translated src=- shape=3b7fd5cf vocab=dd5af0c4
-/
theorem parity_splitting (C : ClosedPolygon m) (u : Plane) (a : ZMod (m + 3)) (hk : k ≤ m + 3)
    {K : List Piece} (h₁ : SameEdges L₁ (C.arcPieces a k ++ K))
    (h₂ : SameEdges L₂ (C.arcPieces (a + k) (m + 3 - k) ++ K)) (q : Plane) :
    parity u L₁ q + parity u L₂ q = parity u C.pieces q :=
  parity_split u (sameEdges_arcPieces_split C a hk) h₁ h₂ q

/-! ### What the identity says about the regions

Theorem 2.3 fixes the two values of `π` for each of the three curves — `1` on the bounded
region, `0` on the unbounded one — and the identity then reads off the blueprint's
"consequently". -/

/-- **The crossing count decides the region** (Theorem 2.3, last sentence, as a criterion).
Off the polygon, `π_C = 1` exactly on the bounded region.
@isnad1 id=iff.3h4v.s7.9adbe8d0bcfd from=translated src=- shape=b26af6c8 vocab=cd429e76
-/
theorem parity_eq_one_iff (C : ClosedPolygon m) {u : Plane} (hu : Plane.IsDirection u)
    (hL : ∀ Q ∈ C.pieces, hgt u Q.1 ≠ hgt u Q.2) {x : Plane} (hx : x ∉ C.carrier) :
    parity u C.pieces x = 1 ↔ x ∈ inside C.carrier := by
  have hmem : x ∈ inside C.carrier ∪ outside C.carrier := by
    rw [inside_union_outside]; exact hx
  refine ⟨fun h => ?_, C.parity_eq_one_of_mem_inside hu hL⟩
  rcases hmem with h' | h'
  · exact h'
  · rw [C.parity_eq_zero_of_mem_outside hu hL h'] at h
    exact absurd h (by decide)

/-- **A point inside `C` and off the crosscut is inside exactly one of `J₁, J₂`** — the first
half of the "Consequently" of Lemma 2.7. The left side of the splitting identity is `1`, so
exactly one of the two right-hand terms is.

"Off the crosscut" is `x ∉ cover K`; that `x` is off `J₁` and off `J₂` as well is not assumed
but derived, by `notMem_carrier_of_sameEdges`.
@isnad1 id=iff.8h11v.s8.c6bf7b673448 from=translated src=- shape=b7a5a6df vocab=d3fd96bf
-/
theorem crosscut_inside_exactly_one {m₁ m₂ : ℕ} (C : ClosedPolygon m) (J₁ : ClosedPolygon m₁)
    (J₂ : ClosedPolygon m₂) {u : Plane} (hu : Plane.IsDirection u)
    (hC : ∀ Q ∈ C.pieces, hgt u Q.1 ≠ hgt u Q.2) {K : List Piece}
    (hK : ∀ Q ∈ K, hgt u Q.1 ≠ hgt u Q.2) (hk : k ≤ m + 3)
    (h₁ : SameEdges J₁.pieces (C.arcPieces a k ++ K))
    (h₂ : SameEdges J₂.pieces (C.arcPieces (a + k) (m + 3 - k) ++ K))
    {x : Plane} (hx : x ∈ inside C.carrier) (hxK : x ∉ cover K) :
    x ∈ inside J₁.carrier ↔ x ∉ inside J₂.carrier := by
  have hJ₁ := h₁.hgt_ne (arcPieces_append_hgt_ne hC hK)
  have hJ₂ := h₂.hgt_ne (arcPieces_append_hgt_ne hC hK)
  have hsum := C.parity_splitting u a hk h₁ h₂ x
  rw [C.parity_eq_one_of_mem_inside hu hC hx] at hsum
  have harith : ∀ s t : ZMod 2, s + t = 1 → (s = 1 ↔ ¬ t = 1) := by decide
  rw [← J₁.parity_eq_one_iff hu hJ₁ (notMem_carrier_of_sameEdges h₁ hx.1 hxK),
    ← J₂.parity_eq_one_iff hu hJ₂ (notMem_carrier_of_sameEdges h₂ hx.1 hxK)]
  exact harith _ _ hsum

/-- **A point outside `C` and off the crosscut is inside both of `J₁, J₂` or inside neither** —
the second half of the "Consequently" of Lemma 2.7. The left side of the splitting identity is
`0`, so the two right-hand terms agree.
@isnad1 id=iff.8h11v.s8.b99e9dc879f7 from=translated src=- shape=60247cca vocab=8a484e07
-/
theorem crosscut_outside_agree {m₁ m₂ : ℕ} (C : ClosedPolygon m) (J₁ : ClosedPolygon m₁)
    (J₂ : ClosedPolygon m₂) {u : Plane} (hu : Plane.IsDirection u)
    (hC : ∀ Q ∈ C.pieces, hgt u Q.1 ≠ hgt u Q.2) {K : List Piece}
    (hK : ∀ Q ∈ K, hgt u Q.1 ≠ hgt u Q.2) (hk : k ≤ m + 3)
    (h₁ : SameEdges J₁.pieces (C.arcPieces a k ++ K))
    (h₂ : SameEdges J₂.pieces (C.arcPieces (a + k) (m + 3 - k) ++ K))
    {x : Plane} (hx : x ∈ outside C.carrier) (hxK : x ∉ cover K) :
    x ∈ inside J₁.carrier ↔ x ∈ inside J₂.carrier := by
  have hJ₁ := h₁.hgt_ne (arcPieces_append_hgt_ne hC hK)
  have hJ₂ := h₂.hgt_ne (arcPieces_append_hgt_ne hC hK)
  have hsum := C.parity_splitting u a hk h₁ h₂ x
  rw [C.parity_eq_zero_of_mem_outside hu hC hx] at hsum
  have harith : ∀ s t : ZMod 2, s + t = 0 → (s = 1 ↔ t = 1) := by decide
  rw [← J₁.parity_eq_one_iff hu hJ₁ (notMem_carrier_of_sameEdges h₁ hx.1 hxK),
    ← J₂.parity_eq_one_iff hu hJ₂ (notMem_carrier_of_sameEdges h₂ hx.1 hxK)]
  exact harith _ _ hsum

end ClosedPolygon

end Schoenflies
