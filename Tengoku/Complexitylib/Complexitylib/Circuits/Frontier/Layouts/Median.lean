/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Tengoku.Complexitylib.Complexitylib.Circuits.Frontier.Layouts.Cubic
public import Tengoku

/-!
# Ordering a cubic graph by median edge scores

Give every edge of a cubic graph a real *score*. Each vertex has three incident edges, hence a
*median* score, and we list the vertices by their medians. This file bounds the cut of every
prefix of that list in terms of how the scores fall around a grid of thresholds
`a, a + δ, ..., a + M δ`. A vertex *straddles* a threshold `t` when one of its edges scores
below `t` and another at least `t`.

**The cut of a prefix** (`card_crossingFinset_le`). Let `P` be a set of vertices whose medians are
all at most some `m`, while the medians outside `P` are all at least `m`. An edge leaving `P`
that scores below a threshold `t ≤ m` is charged to its endpoint outside `P`: that endpoint
has its median above the edge's score, so it is charged at most once. An edge scoring at least
a threshold `t' > m` is charged to its endpoint inside `P`, again at most once. If
`a + i δ ≤ m < a + (i + 1) δ`, every vertex charged in this way straddles `a + i δ` or is an
endpoint of an edge scoring in the window `[a + i δ, a + (i + 1) δ)`, so the cut has at most

`#(vertices straddling a + i δ) + 3 #(edges scoring in the window)`

edges. If `m` lies below the grid, or above it, the cut is at most three times the number of
edges in the lower, or upper, tail.

**The layout** (`exists_key_of_edgeScore`). Listing the vertices by median, with ties broken
arbitrarily, every prefix has the property above, so all prefix cuts are bounded at once.
-/

@[expose] public section

namespace Complexity.Frontier

open Finset

variable {W : Type} [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]

variable {H}

omit [Fintype W] in
/-- Edges each with an endpoint in `Q`, no two sharing such an endpoint, number at most `|Q|`. -/
theorem card_le_of_endpoints {C : Finset (Sym2 W)} {Q : Finset W}
    (hend : ∀ e ∈ C, ∃ v ∈ Q, v ∈ e)
    (huniq : ∀ v ∈ Q, ∀ e ∈ C, ∀ e' ∈ C, v ∈ e → v ∈ e' → e = e') : #C ≤ #Q := by
  rcases C.eq_empty_or_nonempty with rfl | ⟨e₀, he₀⟩
  · simp
  have : Nonempty W := ⟨(hend e₀ he₀).choose⟩
  choose! g hgQ hge using hend
  exact card_le_card_of_injOn g (fun e he => hgQ e he) fun e he e' he' h =>
    huniq (g e) (hgQ e he) e he e' he' (hge e he) (h ▸ hge e' he')

/-- The endpoints of a set of edges number at most twice the edges. -/
theorem card_endpoints_le [DecidableEq W] (D : Finset (Sym2 W)) :
    #{w | ∃ e ∈ D, w ∈ e} ≤ 2 * #D := by
  calc #{w | ∃ e ∈ D, w ∈ e}
      ≤ #(D.biUnion fun e => {w | w ∈ e}) := by
        refine card_le_card fun w hw => ?_
        obtain ⟨e, he, hwe⟩ := (mem_filter.mp hw).2
        exact mem_biUnion.mpr ⟨e, he, mem_filter.mpr ⟨mem_univ w, hwe⟩⟩
    _ ≤ ∑ e ∈ D, #{w | w ∈ e} := card_biUnion_le
    _ ≤ ∑ _e ∈ D, 2 := by
        refine sum_le_sum fun e _ => ?_
        induction e using Sym2.ind with
        | _ a b =>
          calc #{w | w ∈ s(a, b)} ≤ #({a, b} : Finset W) :=
                card_le_card fun w hw => by simpa [Sym2.mem_iff] using hw
            _ ≤ 2 := card_le_two
    _ = 2 * #D := by rw [sum_const, smul_eq_mul, mul_comm]

/-! ### The cut of a prefix -/

section Cut

variable {score : Sym2 W → ℝ} {med : W → ℝ} {P : Finset W} {m : ℝ}

end Cut

/-! ### The layout -/

end Complexity.Frontier
