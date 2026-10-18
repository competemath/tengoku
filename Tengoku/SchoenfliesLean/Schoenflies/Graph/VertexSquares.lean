/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Tengoku.SchoenfliesLean.Schoenflies.Square
import Tengoku.SchoenfliesLean.Schoenflies.UniformBound
import Tengoku.SchoenfliesLean.Schoenflies.Subarc
import Tengoku.SchoenfliesLean.Schoenflies.Graph.Drawing

/-!
# The vertex squares, the last parameter inside a closed set, and the cores

Three of the ordinary bricks of the polygonal redrawing of a finite plane graph.

**The vertex squares.** Around each vertex of a finite plane graph sits a closed axis-parallel
square which meets no other vertex and no edge arc of an edge not incident with that vertex.
One compact separation per other vertex and per non-incident arc, then the single-`ε`-for-all
lemma of `Schoenflies/UniformBound.lean`. Squares rather than disks because the assembly needs
the boundary to be made of segments; convexity, which the radial segments of the last step
want, both shapes have.

Because the choice is made once for all vertices rather than vertex by vertex, halving the
common radius also makes *distinct squares disjoint* — which the cores of the next brick need
and which the per-vertex statement does not give. That is why `exists_vertexSquares` is the
form to consume and `exists_square_at` only its ingredient.

**The last parameter inside a closed set.** The parameters at which an arc lies in a closed
set form a compact subset of the parameter interval; if it is nonempty its supremum is
attained, and past that supremum the arc has left the set for good. The mirror statement about
the infimum is what the far end of an edge wants: the arc leaves the square at `v` for the last
time and enters the square at `w` for the first time.

**The cores.** The subarc of an edge between those two parameters. It meets the square at `v`
in its own first endpoint only, the square at `w` in its own last endpoint only, and — the
clause the assembly really uses — it contains no vertex, which makes distinct cores disjoint
without any further estimate.

## Blueprint

Bricks B2, B3 and B4 of `lem:polygonal-redrawing`.

* `Plane.closedBall_subset_closedSquare`, `Plane.closedSquare_subset_ball` — a square sits
  inside a ball and vice versa, the comparison every separation argument passes through.
* `Plane.supDist_triangle`, `Plane.closedSquare_mono_center`, `Plane.mem_closedSquare_self` —
  square arithmetic missing from `Schoenflies/Square.lean`.
* `exists_last_mem_Icc`, `exists_first_mem_Icc`, `exists_last_mem`, `exists_first_mem` — B3,
  with `isCompact_parameters_mem` behind them.
* `Graph.IsDrawing.exists_square_at` — B2 at one vertex.
* `Graph.IsDrawing.exists_vertexSquares` — B2 as consumed: one radius for every vertex, with
  distinct squares disjoint.
* `Graph.IsDrawing.exists_core` — B4, the core of one edge.
* `Graph.IsDrawing.disjoint_of_subset_edgeArc` — B4's "distinct cores are disjoint".
* `Graph.IsDrawing.closedSquare_disjoint_edgeArc_of_ne` — B4's "meets no other vertex square",
  which is a property of the whole arc.
-/

open Metric Set unitInterval

namespace Schoenflies

namespace Plane

/-! ### Square arithmetic

`Schoenflies/Square.lean` has convexity, openness and closedness of `closedSquare` but no
triangle inequality for `supDist` and no monotonicity at a general centre; both are needed
here. -/

/-- Squares about a common centre grow with the radius. `Bounded.closedSquare_mono` says this
only about the origin. -/
theorem closedSquare_mono_center (c : Plane) {r s : ℝ} (h : r ≤ s) :
    closedSquare c r ⊆ closedSquare c s := fun _ hx => le_trans hx h

/-- The centre lies in its own square. -/
theorem mem_closedSquare_self (c : Plane) {r : ℝ} (hr : 0 ≤ r) : c ∈ closedSquare c r := by
  change supDist c c ≤ r
  rw [supDist_self]; exact hr

theorem supDist_eq_dist_le (x c : Plane) : supDist x c ≤ dist x c := by
  rw [dist_eq_norm]; exact supNorm_le_norm _

/-- The inscribed ball: a ball is inside the square of the same radius, since the sup norm is
at most the Euclidean norm. -/
theorem closedBall_subset_closedSquare (c : Plane) (r : ℝ) :
    closedBall c r ⊆ closedSquare c r := fun _ hx =>
  le_trans (supDist_eq_dist_le _ _) (mem_closedBall.1 hx)

/-- The circumscribed ball, in the form the separations want: a square of *half* a given
radius sits inside the open ball of that radius, because `√2 < 2`. -/
theorem closedSquare_subset_ball {c : Plane} {ρ : ℝ} (hρ : 0 < ρ) :
    closedSquare c (ρ / 2) ⊆ ball c ρ := by
  have hsqrt : Real.sqrt 2 < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  intro x hx
  have hsup : supDist x c ≤ ρ / 2 := hx
  have hnorm : ‖x - c‖ ≤ Real.sqrt 2 * (ρ / 2) :=
    le_trans (norm_le_sqrt_two_mul_supNorm _)
      (mul_le_mul_of_nonneg_left hsup (Real.sqrt_nonneg 2))
  rw [mem_ball, dist_eq_norm]
  calc ‖x - c‖ ≤ Real.sqrt 2 * (ρ / 2) := hnorm
    _ < 2 * (ρ / 2) := by
        exact mul_lt_mul_of_pos_right hsqrt (by linarith)
    _ = ρ := by ring

end Plane

/-! ### B3 — the last point of an arc inside a closed set -/

/-- The parameters at which a curve lies in a closed set form a compact subset of the
parameter interval: the parametrisation is continuous there and the interval is compact.

Stated over an arbitrary `Icc` and not only over `[0, 1]`, because the *second* use of B3 —
the first entry into the far vertex's square — has to happen after the last exit from the near
one, i.e. on the interval `[a, 1]`. -/
theorem isCompact_parameters_mem {f : ℝ → Plane} {α β : ℝ} (hf : ContinuousOn f (Icc α β))
    {C : Set Plane} (hC : IsClosed C) : IsCompact {t | t ∈ Icc α β ∧ f t ∈ C} := by
  have hset : {t | t ∈ Icc α β ∧ f t ∈ C} = Icc α β ∩ f ⁻¹' C := rfl
  rw [hset]
  exact isCompact_Icc.of_isClosed_subset
    (hf.preimage_isClosed_of_isClosed isClosed_Icc hC) inter_subset_left

/-- The last parameter inside a closed set. Given one parameter whose point lies in `C`, there
is a largest one: the curve is in `C` there, and at every larger parameter of the interval it
has left `C` for good.

This is the supremum of a nonempty compact set of parameters, which is therefore attained. -/
theorem exists_last_mem_Icc {f : ℝ → Plane} {α β : ℝ} (hf : ContinuousOn f (Icc α β))
    {C : Set Plane} (hC : IsClosed C) {t₀ : ℝ} (ht₀ : t₀ ∈ Icc α β) (hmem : f t₀ ∈ C) :
    ∃ s ∈ Icc α β, t₀ ≤ s ∧ f s ∈ C ∧ ∀ t ∈ Icc α β, s < t → f t ∉ C := by
  set S : Set ℝ := {t | t ∈ Icc α β ∧ f t ∈ C} with hS
  have hcpt : IsCompact S := isCompact_parameters_mem hf hC
  have hne : S.Nonempty := ⟨t₀, ht₀, hmem⟩
  obtain ⟨hsI, hsC⟩ : sSup S ∈ S := hcpt.sSup_mem hne
  refine ⟨sSup S, hsI, le_csSup hcpt.bddAbove ⟨ht₀, hmem⟩, hsC, fun t htI hlt htC => ?_⟩
  -- A parameter past the supremum that still lands in `C` would be a member above it.
  exact absurd (le_csSup hcpt.bddAbove ⟨htI, htC⟩) (not_le.2 hlt)

/-- The mirror of `exists_last_mem_Icc`: the first parameter inside a closed set. Before it the
curve has not yet reached `C`. -/
theorem exists_first_mem_Icc {f : ℝ → Plane} {α β : ℝ} (hf : ContinuousOn f (Icc α β))
    {C : Set Plane} (hC : IsClosed C) {t₀ : ℝ} (ht₀ : t₀ ∈ Icc α β) (hmem : f t₀ ∈ C) :
    ∃ s ∈ Icc α β, s ≤ t₀ ∧ f s ∈ C ∧ ∀ t ∈ Icc α β, t < s → f t ∉ C := by
  set S : Set ℝ := {t | t ∈ Icc α β ∧ f t ∈ C} with hS
  have hcpt : IsCompact S := isCompact_parameters_mem hf hC
  have hne : S.Nonempty := ⟨t₀, ht₀, hmem⟩
  obtain ⟨hsI, hsC⟩ : sInf S ∈ S := hcpt.sInf_mem hne
  refine ⟨sInf S, hsI, csInf_le hcpt.bddBelow ⟨ht₀, hmem⟩, hsC, fun t htI hlt htC => ?_⟩
  exact absurd (csInf_le hcpt.bddBelow ⟨htI, htC⟩) (not_le.2 hlt)

/-- B3 on the unit interval: the last parameter at which an arc is inside a closed set. -/
theorem exists_last_mem {f : ℝ → Plane} (hf : ContinuousOn f I) {C : Set Plane}
    (hC : IsClosed C) {t₀ : ℝ} (ht₀ : t₀ ∈ I) (hmem : f t₀ ∈ C) :
    ∃ s ∈ I, t₀ ≤ s ∧ f s ∈ C ∧ ∀ t ∈ I, s < t → f t ∉ C :=
  exists_last_mem_Icc hf hC ht₀ hmem

/-- B3 on the unit interval, at the other end: the first parameter at which an arc is inside a
closed set. -/
theorem exists_first_mem {f : ℝ → Plane} (hf : ContinuousOn f I) {C : Set Plane}
    (hC : IsClosed C) {t₀ : ℝ} (ht₀ : t₀ ∈ I) (hmem : f t₀ ∈ C) :
    ∃ s ∈ I, s ≤ t₀ ∧ f s ∈ C ∧ ∀ t ∈ I, t < s → f t ∉ C :=
  exists_first_mem_Icc hf hC ht₀ hmem

end Schoenflies

/-! ### B2 — the vertex squares -/

open Schoenflies
open scoped Graph

namespace Graph

variable {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane}

/-- A vertex lies on no arc of an edge it is not incident with: the arc meets the vertex set
only at its own two ends, and those are the vertices it is incident with. -/
theorem IsDrawing.notMem_edgeArc_of_not_inc (h : IsDrawing G drawing) {e : β} (he : e ∈ E(G))
    {v : Plane} (hv : v ∈ V(G)) (hinc : ¬ G.Inc e v) : v ∉ edgeArc drawing e := by
  intro hmem
  obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet he
  rcases h.vertex_mem_edgeArc hxy hv hmem with rfl | rfl
  · exact hinc hxy.inc_left
  · exact hinc hxy.inc_right

/-- B2 at a single vertex: a closed square about `v` meeting no other vertex and no arc of an
edge not incident with `v`.

The two families are separated the same way — one compact separation each, then the common
positive bound of `exists_pos_forall_of_finite` — and the two radii are then merged by taking
the smaller, which is legitimate because shrinking a square preserves "meets nothing". -/
theorem IsDrawing.exists_square_at [G.Finite] (h : IsDrawing G drawing) {v : Plane}
    (hv : v ∈ V(G)) :
    ∃ r > 0, (∀ w ∈ V(G), w ≠ v → w ∉ Plane.closedSquare v r) ∧
      ∀ e ∈ E(G), ¬ G.Inc e v → Disjoint (Plane.closedSquare v r) (edgeArc drawing e) := by
  -- The other vertices.
  obtain ⟨r₁, hr₁, hvert⟩ :
      ∃ r > 0, ∀ w ∈ V(G), w ≠ v → w ∉ Plane.closedSquare v r := by
    refine exists_pos_forall_of_finite (Graph.finite_vertexSet (G := G))
      (P := fun w r => w ≠ v → w ∉ Plane.closedSquare v r) ?_ ?_
    · exact fun w δ ε _ hδε hP hne hmem =>
        hP hne (Plane.closedSquare_mono_center v hδε hmem)
    · intro w hw
      by_cases hwv : w = v
      · exact ⟨1, one_pos, fun hne => absurd hwv hne⟩
      · -- `w` is at positive Euclidean distance from `v`, and a square of half that radius
        -- sits inside the ball of that radius.
        have hpos : 0 < dist w v := dist_pos.2 hwv
        refine ⟨dist w v / 2, by linarith, fun _ hmem => ?_⟩
        exact absurd (mem_ball.1 (Plane.closedSquare_subset_ball hpos hmem)) (by simp)
  -- The non-incident edges.
  obtain ⟨r₂, hr₂, hedge⟩ :
      ∃ r > 0, ∀ e ∈ E(G), ¬ G.Inc e v →
        Disjoint (Plane.closedSquare v r) (edgeArc drawing e) := by
    refine exists_pos_forall_of_finite (Graph.finite_edgeSet (G := G))
      (P := fun e r => ¬ G.Inc e v → Disjoint (Plane.closedSquare v r) (edgeArc drawing e))
      ?_ ?_
    · exact fun e δ ε _ hδε hP hinc =>
        Set.disjoint_of_subset_left (Plane.closedSquare_mono_center v hδε) (hP hinc)
    · intro e he
      by_cases hinc : G.Inc e v
      · exact ⟨1, one_pos, fun h' => absurd hinc h'⟩
      · have hdisj : Disjoint ({v} : Set Plane) (edgeArc drawing e) :=
          Set.disjoint_singleton_left.2 (h.notMem_edgeArc_of_not_inc he hv hinc)
        obtain ⟨ρ, hρ, hsep⟩ :=
          Plane.exists_dist_pos isCompact_singleton (h.isCompact_edgeArc he) hdisj
        refine ⟨ρ / 2, by linarith, fun _ => Set.disjoint_left.2 fun x hx hxe => ?_⟩
        have hclose : dist x v < ρ := mem_ball.1 (Plane.closedSquare_subset_ball hρ hx)
        have hfar : ρ ≤ dist v x := hsep v rfl x hxe
        rw [dist_comm] at hfar
        linarith
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, fun w hw hne hmem => ?_, fun e he hinc => ?_⟩
  · exact hvert w hw hne (Plane.closedSquare_mono_center v (min_le_left _ _) hmem)
  · exact Set.disjoint_of_subset_left
      (Plane.closedSquare_mono_center v (min_le_right _ _)) (hedge e he hinc)

/-- B2 as its consumers want it: **one** radius serving every vertex at once, with the squares
about distinct vertices disjoint.

Disjointness is not a consequence of the per-vertex statement — a square about `v` avoiding
`w` says nothing about a square about `w` reaching towards `v`. It comes from choosing the
radius once for all vertices and then halving it: two squares of radius `r` that met would put
their centres within `2r` in the sup metric, i.e. each centre in the other's square of radius
`2r`, which the unhalved choice forbids. -/
theorem IsDrawing.exists_vertexSquares [G.Finite] (h : IsDrawing G drawing) :
    ∃ r > 0,
      (∀ v ∈ V(G), ∀ w ∈ V(G), w ≠ v → w ∉ Plane.closedSquare v r) ∧
      (∀ v ∈ V(G), ∀ e ∈ E(G), ¬ G.Inc e v →
        Disjoint (Plane.closedSquare v r) (edgeArc drawing e)) ∧
      ∀ v ∈ V(G), ∀ w ∈ V(G), v ≠ w →
        Disjoint (Plane.closedSquare v r) (Plane.closedSquare w r) := by
  -- One radius for all vertices, by the same monotone-downward bound.
  obtain ⟨r, hr, hall⟩ :
      ∃ r > 0, ∀ v ∈ V(G),
        (∀ w ∈ V(G), w ≠ v → w ∉ Plane.closedSquare v r) ∧
        ∀ e ∈ E(G), ¬ G.Inc e v →
          Disjoint (Plane.closedSquare v r) (edgeArc drawing e) := by
    refine exists_pos_forall_of_finite (Graph.finite_vertexSet (G := G))
      (P := fun v r => (∀ w ∈ V(G), w ≠ v → w ∉ Plane.closedSquare v r) ∧
        ∀ e ∈ E(G), ¬ G.Inc e v →
          Disjoint (Plane.closedSquare v r) (edgeArc drawing e)) ?_ ?_
    · rintro v δ ε _ hδε ⟨hP, hQ⟩
      exact ⟨fun w hw hne hmem => hP w hw hne (Plane.closedSquare_mono_center v hδε hmem),
        fun e he hinc =>
          Set.disjoint_of_subset_left (Plane.closedSquare_mono_center v hδε) (hQ e he hinc)⟩
    · exact fun v hv => h.exists_square_at hv
  refine ⟨r / 2, by linarith, fun v hv w hw hne hmem => ?_, fun v hv e he hinc => ?_,
    fun v hv w hw hne => Set.disjoint_left.2 fun x hxv hxw => ?_⟩
  · exact (hall v hv).1 w hw hne (Plane.closedSquare_mono_center v (by linarith) hmem)
  · exact Set.disjoint_of_subset_left (Plane.closedSquare_mono_center v (by linarith))
      ((hall v hv).2 e he hinc)
  · -- Both centres are within `r/2` of `x`, hence within `r` of each other.
    have hvx : Plane.supDist x v ≤ r / 2 := hxv
    have hwx : Plane.supDist x w ≤ r / 2 := hxw
    have : Plane.supDist w v ≤ r := by
      have := Plane.supDist_triangle w x v
      rw [Plane.supDist_comm w x] at this
      linarith
    exact (hall v hv).1 w hw (Ne.symm hne) this

/-! ### B4 — the cores -/

/-- An edge is incident only with its own two ends. -/
theorem not_inc_of_ne {e : β} {v w u : Plane} (hlink : G.IsLink e v w) (huv : u ≠ v)
    (huw : u ≠ w) : ¬ G.Inc e u := fun hinc => (hinc.eq_or_eq_of_isLink hlink).elim huv huw

/-- "The core meets no other vertex square" is really a statement about the whole arc: the
square about a vertex which is neither end of the edge misses the edge's arc entirely, by B2.
The hypothesis is exactly the second clause of `exists_vertexSquares`. -/
theorem IsDrawing.closedSquare_disjoint_edgeArc_of_ne {e : β} {v w u : Plane} {r : ℝ}
    (hsq : ∀ e ∈ E(G), ¬ G.Inc e u → Disjoint (Plane.closedSquare u r) (edgeArc drawing e))
    (hlink : G.IsLink e v w) (huv : u ≠ v) (huw : u ≠ w) :
    Disjoint (Plane.closedSquare u r) (edgeArc drawing e) :=
  hsq e hlink.edge_mem (not_inc_of_ne hlink huv huw)

/-- **Distinct cores are disjoint.** A subset of one edge's arc containing no vertex meets no
other edge's arc at all, because distinct edges meet only at vertices. Stated for arbitrary
subsets rather than for cores, since that is all the argument uses — and it is why
`exists_core` carries `Disjoint K V(G)` rather than a clause about other edges. -/
theorem IsDrawing.disjoint_of_subset_edgeArc (h : IsDrawing G drawing) {e f : β}
    (he : e ∈ E(G)) (hf : f ∈ E(G)) (hef : e ≠ f) {K L : Set Plane}
    (hK : K ⊆ edgeArc drawing e) (hKV : Disjoint K V(G)) (hL : L ⊆ edgeArc drawing f) :
    Disjoint K L :=
  Set.disjoint_left.2 fun _ hxK hxL =>
    Set.disjoint_left.1 hKV hxK (h.arcs_meet_at_vertex he hf hef (hK hxK) (hL hxL))

end Graph
