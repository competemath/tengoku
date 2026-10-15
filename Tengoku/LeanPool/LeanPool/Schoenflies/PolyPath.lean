/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import Tengoku.LeanPool.LeanPool.Schoenflies.Plane
public import Tengoku

/-!
# Polygonal paths

A polygonal path is carried by a list of vertices; its `poly` carrier is the union of the
segments joining consecutive entries. This is the combinatorial representation the whole
of Part I works with — by the blueprint's polygonal overlay convention only finite
polygonal objects are ever overlaid, so vertex lists, not parametrizations, are the
primitive.

## Blueprint

* `poly` — the carrier of a polygonal path.
* `exists_poly_of_isPreconnected` — Lemma 1.1 (polygonal connectedness), less the passage
  to a *simple* arc, which needs the finite-graph machinery and is proved with Lemma 1.2.
-/

@[expose] public section

open Metric Set

namespace Schoenflies

variable {Ω : Set Plane} {x y z : Plane}

/-! ### Segments -/

/--
@isnad1 id=iscompac.0h2v.s7.7d48ee81b2c7 from=translated src=- shape=f355842b vocab=679c151c
-/
theorem isCompact_segment (x y : Plane) : IsCompact (segment ℝ x y) := by
  rw [segment_eq_image' ℝ x y]
  exact isCompact_Icc.image (by fun_prop)

/-! ### The carrier of a vertex list -/

/-- The carrier of a polygonal path: the union of the segments joining consecutive vertices.
A single vertex carries itself, so that a path may be constant. -/
def poly : List Plane → Set Plane
  | [] => ∅
  | [v] => {v}
  | u :: v :: rest => segment ℝ u v ∪ poly (v :: rest)

/--
@isnad1 id=eq.0h0v.s3.9bf2256ca58f from=translated src=- shape=c8180ac4 vocab=4c344cef
-/
@[simp] theorem poly_nil : poly [] = ∅ := rfl

/--
@isnad1 id=eq.0h1v.s4.852e9f3824a4 from=translated src=- shape=bc1a9a9a vocab=0db98d1f
-/
@[simp] theorem poly_singleton (v : Plane) : poly [v] = {v} := rfl

/--
@isnad1 id=eq.0h3v.s7.d7767705b5d1 from=translated src=- shape=3f554fe6 vocab=17374cba
-/
@[simp] theorem poly_cons_cons (u v : Plane) (rest : List Plane) :
    poly (u :: v :: rest) = segment ℝ u v ∪ poly (v :: rest) := rfl

/--
@isnad1 id=nonempty.1h1v.s3.d8c2e05e4996 from=translated src=- shape=625cc219 vocab=a6e22dc8
-/
theorem poly_nonempty : ∀ {vs : List Plane}, vs ≠ [] → (poly vs).Nonempty
  | [], h => absurd rfl h
  | [v], _ => ⟨v, rfl⟩
  | _ :: v :: _, _ => ⟨v, Or.inl (right_mem_segment ℝ _ _)⟩

/--
@isnad1 id=iscompac.0h1v.s5.57d649d5b510 from=translated src=- shape=0ae065e3 vocab=b8536f46
-/
theorem isCompact_poly : ∀ vs : List Plane, IsCompact (poly vs)
  | [] => by simp
  | [v] => by simp
  | u :: v :: rest => by
    rw [poly_cons_cons]
    exact (isCompact_segment u v).union (isCompact_poly (v :: rest))

/-- Every vertex lies on the carrier.
@isnad1 id=mem.1h2v.s4.98b45c17d21a from=translated src=- shape=9b9e4ee1 vocab=da392c31
-/
theorem mem_poly_of_mem : ∀ {vs : List Plane} {v : Plane}, v ∈ vs → v ∈ poly vs
  | [], _, h => absurd h (by simp)
  | [_], _, h => by simpa using h
  | u :: w :: rest, v, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact Or.inl (left_mem_segment ℝ _ _)
    · exact Or.inr (mem_poly_of_mem h)

/--
@isnad1 id=mem.1h1v.s4.e6da9e2b0d6d from=translated src=- shape=47492d6a vocab=b46a1458
-/
theorem head_mem_poly {vs : List Plane} (h : vs ≠ []) : vs.head h ∈ poly vs :=
  mem_poly_of_mem (List.head_mem h)

/--
@isnad1 id=mem.1h1v.s4.622ffb0afa5d from=translated src=- shape=47492d6a vocab=012a6245
-/
theorem getLast_mem_poly {vs : List Plane} (h : vs ≠ []) : vs.getLast h ∈ poly vs :=
  mem_poly_of_mem (List.getLast_mem h)

/-- The carrier of a nonempty vertex list is connected: consecutive segments share a vertex.
@isnad1 id=isconnec.1h1v.s5.e5929b1fb406 from=translated src=- shape=625cc219 vocab=60b71706
-/
theorem isConnected_poly : ∀ {vs : List Plane}, vs ≠ [] → IsConnected (poly vs)
  | [], h => absurd rfl h
  | [v], _ => by simpa using isConnected_singleton (x := v)
  | u :: v :: rest, _ => by
    rw [poly_cons_cons]
    refine IsConnected.union ⟨v, right_mem_segment ℝ u v, head_mem_poly (by simp)⟩
      ((convex_segment u v).isConnected ⟨u, left_mem_segment ℝ u v⟩)
      (isConnected_poly (List.cons_ne_nil v rest))

/-- Appending one vertex extends the carrier by one segment.
@isnad1 id=eq.1h2v.s7.63275d385cf4 from=translated src=- shape=eea6e798 vocab=be98f6ec
-/
theorem poly_concat : ∀ {vs : List Plane} (h : vs ≠ []) (z : Plane),
    poly (vs ++ [z]) = poly vs ∪ segment ℝ (vs.getLast h) z
  | [], h, _ => absurd rfl h
  | [v], _, z => by
    simp only [List.singleton_append, poly_cons_cons, poly_singleton, List.getLast_singleton]
    rw [union_singleton, insert_eq_self.2 (right_mem_segment ℝ v z), singleton_union,
      insert_eq_self.2 (left_mem_segment ℝ v z)]
  | u :: v :: rest, _, z => by
    simp only [List.cons_append, poly_cons_cons]
    rw [← List.cons_append, poly_concat (List.cons_ne_nil v rest) z,
      List.getLast_cons (List.cons_ne_nil v rest)]
    exact (union_assoc _ _ _).symm

/-! ### Polygonal connectedness -/

/-- Lemma 1.1 (polygonal connectedness), existence half. Any two points of a region are
joined in it by a polygonal path.

The blueprint goes on to make the path *simple*, by subdividing at self-intersections and
taking a simple path in the resulting finite graph; that half is deferred to the graph
module, where the subdivision procedure is available.
@isnad1 id=ex.4h3v.s7.20eebb6a66d6 from=translated src=- shape=db6ba73e vocab=07dc02d4
-/
theorem exists_poly_of_isPreconnected (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (hx : x ∈ Ω) (hy : y ∈ Ω) :
    ∃ vs : List Plane, ∃ h : vs ≠ [], poly vs ⊆ Ω ∧ vs.head h = x ∧ vs.getLast h = y := by
  -- `R` is the set of points reachable from `x` by a polygonal path inside `Ω`.
  set R : Set Plane :=
    {w ∈ Ω | ∃ vs : List Plane, ∃ h : vs ≠ [], poly vs ⊆ Ω ∧ vs.head h = x ∧ vs.getLast h = w}
    with hR
  -- Extending a path by a segment inside a convex subset of `Ω` keeps it inside `Ω`. Applied
  -- to a ball this makes `R` open, and applied in the other direction makes `Ω \ R` open.
  have key : ∀ C : Set Plane, Convex ℝ C → C ⊆ Ω → ∀ w ∈ C, ∀ z ∈ C,
      (∃ vs : List Plane, ∃ h : vs ≠ [], poly vs ⊆ Ω ∧ vs.head h = x ∧ vs.getLast h = w) →
      ∃ vs : List Plane, ∃ h : vs ≠ [], poly vs ⊆ Ω ∧ vs.head h = x ∧ vs.getLast h = z := by
    rintro C hC hCΩ w hw z hz ⟨vs, hne, hsub, hhead, hlast⟩
    refine ⟨vs ++ [z], by simp, ?_, ?_, ?_⟩
    · rw [poly_concat hne z, hlast]
      exact union_subset hsub ((hC.segment_subset hw hz).trans hCΩ)
    · rw [List.head_append_of_ne_nil hne]; exact hhead
    · simp
  have hRopen : IsOpen R := by
    rw [isOpen_iff_forall_mem_open]
    rintro w ⟨hw, hpath⟩
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hΩ w hw
    exact ⟨ball w r, fun z hz =>
      ⟨hball hz, key _ (convex_ball w r) hball w (mem_ball_self hr) z hz hpath⟩,
      isOpen_ball, mem_ball_self hr⟩
  have hRcompl : IsOpen (Ω \ R) := by
    rw [isOpen_iff_forall_mem_open]
    rintro w ⟨hw, hwR⟩
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hΩ w hw
    refine ⟨ball w r, fun z hz => ⟨hball hz, fun hzR => ?_⟩, isOpen_ball, mem_ball_self hr⟩
    -- A path to `z` runs back to `w` through the same ball, so `w ∈ R` after all.
    exact hwR ⟨hw, key _ (convex_ball w r) hball z hz w (mem_ball_self hr) hzR.2⟩
  -- `R` is nonempty, open and closed in the preconnected `Ω`, so `R = Ω`.
  have hxR : x ∈ R := ⟨hx, [x], by simp, by simpa using hx, rfl, rfl⟩
  have : y ∈ R := by
    by_contra hyR
    obtain ⟨w, _, hw⟩ := hconn R (Ω \ R) hRopen hRcompl
      (fun w hw => (em (w ∈ R)).imp id fun h => ⟨hw, h⟩) ⟨x, hx, hxR⟩ ⟨y, hy, hy, hyR⟩
    exact hw.2.2 hw.1
  exact this.2

/-- Concatenating two vertex lists that agree at the join concatenates their carriers. The
hypothesis is what makes this true: without it `poly [a] ∪ poly [b] = {a, b}` misses the segment
that `poly [a, b]` carries.
@isnad1 id=eq.2h3v.s5.f93c66bcb21e from=translated src=- shape=5d49d459 vocab=a82f534a
-/
theorem poly_append : ∀ {vs : List Plane} (h : vs ≠ []) (w : Plane) (rest : List Plane),
    vs.getLast h = w → poly (vs ++ w :: rest) = poly vs ∪ poly (w :: rest)
  | [], h, _, _, _ => absurd rfl h
  | [v], _, w, rest, hvw => by
    simp only [List.getLast_singleton] at hvw
    subst hvw
    simp [segment_same]
  | u :: v :: tl, _, w, rest, hvw => by
    have h' : (v :: tl).getLast (List.cons_ne_nil v tl) = w := by
      rw [← List.getLast_cons (a := u) (List.cons_ne_nil v tl)]; exact hvw
    simp only [List.cons_append, poly_cons_cons]
    rw [← List.cons_append, poly_append (List.cons_ne_nil v tl) w rest h']
    exact (union_assoc _ _ _).symm

end Schoenflies
