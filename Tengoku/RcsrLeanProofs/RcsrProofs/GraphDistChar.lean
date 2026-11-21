/-
Copyright (c) 2026 Steven Kotlarz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Kotlarz
-/

import Tengoku.Seed.Combinatorics.SimpleGraph.Metric

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A potential-function characterization of graph distance

This file characterizes the graph distance `SimpleGraph.dist` from a fixed
vertex `base` via a pair of purely local conditions on a candidate function
`f : V → ℕ`: every non-`base` vertex has a neighbor on which `f` is exactly
one smaller (`descent`), and `f` never increases by more than one across any
edge (`Lipschitz`). Together these force `f v = G.dist base v` for every `v`,
and in particular that every vertex is reachable from `base`.

This is the graph-theoretic analogue of characterizing a distance function on
a metric space via a "1-Lipschitz + descending path" pair of conditions, and
is proved by the same two-sided squeeze:

* `descent` produces, by strong induction on `f v`, a walk from `base` to `v`
  of length `f v`; this gives `G.dist base v ≤ f v` (and `Reachable`).
* `Lipschitz` bounds how much `f` can change along any walk, so along a
  shortest walk from `base` to `v` we get `f v ≤ G.dist base v`.

Note that `f base = 0` and `hdesc` together already force `f` to vanish
*only* at `base` (if `f v = 0` for `v ≠ base`, `hdesc` would give a neighbor
`w` with `f w + 1 = 0`, impossible in `ℕ`), so no separate hypothesis to that
effect is needed.

## Main results

* `SimpleGraph.reachable_of_descent`: the descent hypothesis alone gives
  reachability from `base`.
* `SimpleGraph.dist_eq_of_descent_of_lipschitz`: the headline theorem,
  `G.dist base v = f v` for all `v`.

## Tags

graph distance, potential function, Lipschitz, descent, shortest path
-/

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {base : V} {f : V → ℕ}

/-- **Descent gives a walk of the right length.**
If every non-`base` vertex `v` has a neighbor `w` with `f w + 1 = f v`
("descent"), then for every `v` there is a walk from `base` to `v` of length
exactly `f v`. Proved by strong induction on `f v`: if `v = base` this is the
trivial `Walk.nil` (using `h0` to know `f base = 0`); otherwise `hdesc`
gives a neighbor `w` one step closer to `base`, reached by the induction
hypothesis in `f w = f v - 1` steps, and appending the edge `w ⟶ v` reaches `v`
in `f v` steps.
@isnad1 id=ex.2h5v.s6.44dd3495ce44 from=translated src=- shape=900e542c vocab=e4c3a087
-/
theorem exists_walk_length_eq_of_descent (h0 : f base = 0)
    (hdesc : ∀ v, v ≠ base → ∃ w, G.Adj v w ∧ f w + 1 = f v) :
    ∀ v, ∃ p : G.Walk base v, p.length = f v := by
  intro v
  generalize hn : f v = n
  induction n using Nat.strong_induction_on generalizing v with
  | _ n ih =>
    by_cases hbv : v = base
    · subst hbv
      exact ⟨.nil, by rw [h0] at hn; simpa using hn⟩
    · obtain ⟨w, hadj, hw⟩ := hdesc v hbv
      have hfw : f w = n - 1 := by omega
      obtain ⟨p, hp⟩ := ih (n - 1) (by omega) w hfw
      refine ⟨p.concat hadj.symm, ?_⟩
      rw [Walk.length_concat, hp]
      omega

/-- **Descent alone gives connectivity from `base`.**
A convenience corollary of `exists_walk_length_eq_of_descent`: under just the
descent hypothesis, every vertex is reachable from `base`.
@isnad1 id=reachabl.2h5v.s6.b2787f4da780 from=translated src=- shape=55e67b62 vocab=4ed3cfec
-/
theorem reachable_of_descent (h0 : f base = 0)
    (hdesc : ∀ v, v ≠ base → ∃ w, G.Adj v w ∧ f w + 1 = f v) (v : V) :
    G.Reachable base v :=
  (exists_walk_length_eq_of_descent h0 hdesc v).elim fun p _ ↦ p.reachable

/-- **The Lipschitz bound propagates along any walk.**
If `f` changes by at most one across every edge (`hlip`), then along any walk
starting at `base`, `f` of the endpoint is at most `f base` plus the walk's
length. Proved by induction on the walk: `Walk.nil` is `f base ≤ f base`, and
each `cons` step adds at most one to the right-hand side by `hlip`.
@isnad1 id=le.1h6v.s6.fceedd893b50 from=translated src=- shape=9dbc7e0d vocab=8d5430d2
-/
theorem le_length_add_of_lipschitz (hlip : ∀ v w, G.Adj v w → f w ≤ f v + 1) :
    ∀ {v : V} (p : G.Walk base v), f v ≤ f base + p.length := by
  intro v p
  induction p with
  | nil => exact le_refl _
  | cons hadj p ih =>
    have hstep := hlip _ _ hadj
    rw [Walk.length_cons]
    omega

/-- **Headline theorem.** If `f base = 0`, every non-`base` vertex has a
descending neighbor (`hdesc`), and `f` is `1`-Lipschitz along edges (`hlip`),
then `f` *is* the graph distance from `base`: `G.dist base v = f v` for
every `v`.

The proof is the standard squeeze: `exists_walk_length_eq_of_descent` builds a
walk of length `f v` from `base` to `v`, giving `G.dist base v ≤ f v` (via
`SimpleGraph.dist_le`); and `le_length_add_of_lipschitz` applied to a shortest
walk gives `f v ≤ f base + G.dist base v = G.dist base v`.
@isnad1 id=eq.3h5v.s6.65972138448c from=translated src=- shape=7f4cc046 vocab=d3f9955e
-/
theorem dist_eq_of_descent_of_lipschitz (h0 : f base = 0)
    (hdesc : ∀ v, v ≠ base → ∃ w, G.Adj v w ∧ f w + 1 = f v)
    (hlip : ∀ v w, G.Adj v w → f w ≤ f v + 1) (v : V) :
    G.dist base v = f v := by
  obtain ⟨p, hp⟩ := exists_walk_length_eq_of_descent h0 hdesc v
  have hle : G.dist base v ≤ f v := hp ▸ G.dist_le p
  have hreach : G.Reachable base v := p.reachable
  obtain ⟨q, hq⟩ := hreach.exists_walk_length_eq_dist
  have hge : f v ≤ G.dist base v := by
    have := le_length_add_of_lipschitz hlip q
    rw [h0, hq] at this
    simpa using this
  omega

end SimpleGraph
