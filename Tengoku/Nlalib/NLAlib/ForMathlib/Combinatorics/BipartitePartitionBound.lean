import Tengoku.Nlalib.NLAlib.ForMathlib.Combinatorics.BipartiteSpanningTree
import Tengoku.Seed.Algebra.BigOperators.Fin

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Universal partition-sum bound for connected bipartite multigraphs

This file uses the spanning-tree construction to prove that for every connected
bipartite multigraph with finite row and column sets `U`, `V`, nonempty `U`, and edge
occurrences `sr : E -> U`, `tg : E -> V`, the sum over all labelings of the
product of the edge weights is bounded by

```
(Fintype.card I : ℝ) * a ^ (Fintype.card U - 1) * c ^ (Fintype.card V) *
  s ^ (Fintype.card E - (Fintype.card U - 1 + Fintype.card V))
```

when every `w i j` is nonnegative, bounded by `s`, every column sum is at most
`a`, and every row sum is at most `c`.

The proof selects a spanning tree via `exists_spanning_tree_syntax`, reindexes
the row and column labelings through the row/column equivalences
`ur : Fin (r+1) ≃ U`, `vc : Fin q ≃ V`, bounds the off-tree factors by
`s ^ O.card` using `prod_bipartite_edge_weight_le_prod_mul_pow`, and applies the tree
bound `partitionSum_le`.

The leading factor is the cardinality of the label type `I` (the number of free
root-row labels), not of the vertex type `U`. The `[DecidableEq U]` and
`[DecidableEq V]` assumptions are classical decidability assumptions providing
the `Fintype` instances for the function label spaces `U -> I`, `V -> J`.
-/

noncomputable section
namespace NLAlib

open scoped BigOperators
open Finset

variable {U V E I J : Type*}

/-- The product over the occurrence-indexed tree edges equals the syntax-tree
weight: if the injective occurrence map `occ` realizes each tree edge `(i, j)`
by an occurrence with endpoints `ur i`, `vc j`, then the product of the weights
over `univ.map occ` equals `weight w t X Y`.
@isnad1 id=eq.1h16v.s9.f65b9f20d344 from=translated src=- shape=2a87bf29 vocab=3c448117
-/
theorem prod_bipartite_tree_edges_eq_weight [Fintype E] [DecidableEq E]
    {r q : ℕ} (t : RowRootedBipartiteTree r q)
    (sr : E → U) (tg : E → V)
    (ur : Fin (r+1) ≃ U) (vc : Fin q ≃ V)
    (occ : Fin t.edgeList.length ↪ E)
    (hend : ∀ k : Fin t.edgeList.length,
      sr (occ k) = ur (t.edgeList.get k).1 ∧
        tg (occ k) = vc (t.edgeList.get k).2)
    (w : I → J → ℝ)
    (X : Fin (r+1) → I) (Y : Fin q → J) :
    (∏ e ∈ univ.map occ, w (X (ur.symm (sr e))) (Y (vc.symm (tg e)))) =
      RowRootedBipartiteTree.weight w t X Y := by
  unfold RowRootedBipartiteTree.weight
  calc
    (∏ e ∈ univ.map occ, w (X (ur.symm (sr e))) (Y (vc.symm (tg e))))
        = univ.prod (fun k : Fin t.edgeList.length =>
            w (X (ur.symm (sr (occ k)))) (Y (vc.symm (tg (occ k))))) := by
          rw [Finset.prod_map]
    _ = univ.prod (fun k : Fin t.edgeList.length =>
            w (X (t.edgeList.get k).1) (Y (t.edgeList.get k).2)) := by
          refine Finset.prod_congr rfl ?_
          intro k hk
          rcases hend k with ⟨hk1, hk2⟩
          rw [hk1, hk2]
          rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    _ = (List.ofFn (fun k : Fin t.edgeList.length =>
            w (X (t.edgeList.get k).1) (Y (t.edgeList.get k).2))).prod := by
          rw [← List.prod_ofFn]
    _ = (t.edgeList.map (fun e => w (X e.1) (Y e.2))).prod := by
          rw [List.ofFn_comp' (f := fun k : Fin t.edgeList.length => t.edgeList.get k)
            (g := fun e => w (X e.1) (Y e.2))]
          rw [List.ofFn_get]

end NLAlib
