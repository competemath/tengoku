/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Tengoku.LeanPool.LeanPool.Komlos.Main
public import Tengoku

/-!
# The Beck–Fiala bound

Adapted for Lean Pool by changing module paths and selecting explicit imports.

If every vertex of a finite hypergraph belongs to at most `t` edges, each column of its
incidence matrix has Euclidean norm at most `√t`. The scaled Komlós bound therefore gives
an edge discrepancy bound of `36 * √t`.

`Hypergraph.incidenceMatrix` has rows indexed by edges and columns indexed by vertices.
`Hypergraph.discrepancy_incidenceMatrix_le` proves the matrix bound;
`Hypergraph.exists_isColouring_forall_abs_finsum_le` states it as a vertex colouring.
-/

@[expose] public section

namespace Hypergraph

open Komlos Finset

variable {α : Type*} {H : Hypergraph α}

/-- A hypergraph with finitely many vertices has finitely many edges. -/
lemma edgeSet_finite (hV : V(H).Finite) : E(H).Finite :=
  hV.finite_subsets.subset edgeSet_subset_powerset_vertexSet

open Classical in
/-- The incidence matrix of a hypergraph with finitely many vertices: its rows are indexed by
the edges, its columns by the vertices, and an entry is `1` when the vertex lies in the edge
and `0` otherwise. -/
noncomputable def incidenceMatrix (H : Hypergraph α) (hV : V(H).Finite) :
    Matrix (edgeSet_finite hV).toFinset hV.toFinset ℝ :=
  Matrix.of fun e x ↦ if (x : α) ∈ (e : Set α) then 1 else 0

open Classical in
lemma incidenceMatrix_apply (hV : V(H).Finite) (e : (edgeSet_finite hV).toFinset)
    (x : hV.toFinset) :
    H.incidenceMatrix hV e x = if (x : α) ∈ (e : Set α) then 1 else 0 := rfl

/-- The squared entries of a column of the incidence matrix count the edges containing the
vertex. -/
lemma sum_incidenceMatrix_sq (hV : V(H).Finite) (x : hV.toFinset) :
    ∑ e, H.incidenceMatrix hV e x ^ 2 = {e ∈ E(H) | (x : α) ∈ e}.ncard := by
  classical
  calc ∑ e, H.incidenceMatrix hV e x ^ 2
      = ∑ e ∈ (edgeSet_finite hV).toFinset, if (x : α) ∈ e then (1 : ℝ) else 0 := by
        refine Eq.trans ?_ (sum_coe_sort _ _)
        congr with e
        simp [incidenceMatrix_apply]
    _ = {e ∈ E(H) | (x : α) ∈ e}.ncard := by
        rw [sum_boole, ← Set.ncard_coe_finset, coe_filter]
        simp

end Hypergraph
