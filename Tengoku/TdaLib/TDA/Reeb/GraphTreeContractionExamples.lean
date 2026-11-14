import Tengoku.TdaLib.TDA.Reeb.GraphTreeContraction
import Tengoku.TdaLib.TDA.Reeb.GraphCycleObstructionExamples
import Tengoku.Seed.Combinatorics.SimpleGraph.Star

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Fixtures for contractible realizations of finite trees

Acceptance fixtures for `TDA.Reeb.GraphTreeContraction`:

* **Empty vertex type.** For every `[IsEmpty V]` the realization is empty, hence not contractible.
  The graph is not a tree and the realization is not simply connected
  (`TDA.Reeb.Examples.GraphCycleObstruction.empty_not_isTree`, `empty_not_simplyConnectedSpace`),
  so both tree criteria hold with both sides false.
* **One vertex.** The realization of the one-vertex graph is contractible by the finite-tree
  theorem, from `SimpleGraph.IsTree.of_subsingleton`.
* **The path on three vertices.** `pathGraph 3` is the star centred at `1`, hence a tree, and its
  realization is contractible and simply connected. At the leaf `0` with neighbour `1` the slide
  moves `0` along the dart `0 → 1`, shortens that dart to `t ↦ 1 - (1 - t)(1 - s)`, and fixes the
  vertex `2` and the edge `1 — 2`; the collapse sends `0` to `1`. Through the leaf step the
  remaining edge `1 — 2` also has contractible realization.
* **The star with three leaves.** For `starGraph (0 : Fin 4)` the realization is contractible, and
  simply connected through the tree criterion.
* **The triangle.** `⊤ : SimpleGraph (Fin 3)` is not a tree
  (`TDA.Reeb.Examples.GraphCycleObstruction.triangle_not_isTree`), so by the two criteria its
  realization is neither simply connected nor contractible.

The star `starGraph (0 : ℕ)` is a tree on an infinite vertex type; the finite-tree theorems do not
apply to it, and no statement about its realization is made.
-/

open SimpleGraph unitInterval Topology
open scoped ContinuousMap

namespace TDA.Reeb.Examples.GraphTreeContraction

open TDA.Reeb.GraphRealization TDA.Reeb.GraphCycleObstruction TDA.Reeb.GraphTreeContraction

noncomputable section

/-! ### Empty vertex type -/

/-- The empty realization is not contractible: contractibility includes nonemptiness. Both sides
of the tree criteria are false here (`GraphCycleObstruction.empty_not_isTree`).
@isnad1 id=not.0h2v.s4.148a50a76ae0 from=translated src=- shape=733959af vocab=7d13587b
-/
theorem empty_not_contractibleSpace {V : Type*} [IsEmpty V] (G : SimpleGraph V) :
    ¬ ContractibleSpace (Realization G) := fun _ =>
  isEmptyElim (Classical.choice (PathConnectedSpace.nonempty (X := Realization G)))

/-! ### One vertex -/

open TDA.Reeb.Examples.GraphRealization in
/--
@isnad1 id=contract.0h0v.s2.abe854fc5d94 from=translated src=- shape=049cd614 vocab=42847dbf
-/
theorem point_contractibleSpace : ContractibleSpace (Realization pointGraph) :=
  contractibleSpace_realization_of_isTree _ IsTree.of_subsingleton

/-! ### The path on three vertices -/

open TDA.Reeb.Examples.GraphRealization

/-- The path `0 — 1 — 2` is the star centred at `1`.
@isnad1 id=eq.0h0v.s5.51aa438f270f from=translated src=- shape=b82582fa vocab=4c6ed6ea
-/
theorem path3_eq_starGraph : path3 = starGraph 1 := by
  ext u v
  simp only [pathGraph_adj, starGraph_adj]
  revert u v
  decide

/--
@isnad1 id=istree.0h0v.s3.fcf3e8716784 from=translated src=- shape=06f63001 vocab=a6d82257
-/
theorem path3_isTree : path3.IsTree := path3_eq_starGraph ▸ isTree_starGraph 1

/--
@isnad1 id=contract.0h0v.s4.a9741e402731 from=translated src=- shape=b781e9e2 vocab=d8476100
-/
theorem path3_contractibleSpace : ContractibleSpace (Realization path3) :=
  contractibleSpace_realization_of_isTree _ path3_isTree

/--
@isnad1 id=simplyco.0h0v.s4.00aff0755dec from=translated src=- shape=b781e9e2 vocab=5087804c
-/
theorem path3_simplyConnectedSpace : SimplyConnectedSpace (Realization path3) :=
  simplyConnectedSpace_realization_of_isTree _ path3_isTree

/--
@isnad1 id=adj.0h0v.s5.1e92efbb9ab6 from=translated src=- shape=6bd0b6cc vocab=001214b7
-/
theorem path3_adj_01 : path3.Adj 0 1 := d01.adj

/-- The end `0` is a leaf with neighbour `1`.
@isnad1 id=eq.1h1v.s5.b992d5ecba1b from=translated src=- shape=65ab36ec vocab=001214b7
-/
theorem path3_eq_one_of_adj_zero : ∀ w, path3.Adj 0 w → w = 1 := by
  simp only [pathGraph_adj]
  decide

/-- The leaf step at `0`: the realization of the path is homotopy equivalent to the realization of
the edge `1 — 2`.-/
def path3LeafEquiv : Realization path3 ≃ₕ Realization (path3.induce ({0}ᶜ : Set (Fin 3))) :=
  leafHomotopyEquiv path3_adj_01 path3_eq_one_of_adj_zero

/-- Along the leaf slide the leaf `0` travels along the dart `0 → 1`.
@isnad1 id=eq.0h1v.s9.3865d477cb7b from=translated src=- shape=2541cd27 vocab=aa073840
-/
theorem path3_slide_leaf (s : unitInterval) :
    leafHomotopy path3_adj_01 path3_eq_one_of_adj_zero (s, vertex path3 0) =
      edgePoint path3 d01 s :=
  leafHomotopy_vertex_self _ _ s

/-- The dart `0 → 1` is shortened towards `1`.
@isnad1 id=eq.0h2v.s9.5b1dba77bfc4 from=translated src=- shape=65f1a6e0 vocab=2798d717
-/
theorem path3_slide_d01 (s t : unitInterval) :
    leafHomotopy path3_adj_01 path3_eq_one_of_adj_zero (s, edgePoint path3 d01 t) =
      edgePoint path3 d01 (σ (σ t * σ s)) :=
  leafHomotopy_edgePoint_of_fst_eq _ _ rfl s t

/-- The far end `2` stays fixed.
@isnad1 id=eq.0h1v.s9.66c88973ae97 from=translated src=- shape=f76d55e2 vocab=cccc5b7b
-/
theorem path3_slide_two (s : unitInterval) :
    leafHomotopy path3_adj_01 path3_eq_one_of_adj_zero (s, vertex path3 2) = vertex path3 2 :=
  leafHomotopy_vertex_of_ne _ _ (by decide) s

/-- The edge `1 — 2` is fixed pointwise.
@isnad1 id=eq.0h2v.s9.fb78525d07ab from=translated src=- shape=18156fd0 vocab=059920a4
-/
theorem path3_slide_d12 (s t : unitInterval) :
    leafHomotopy path3_adj_01 path3_eq_one_of_adj_zero (s, edgePoint path3 d12 t) =
      edgePoint path3 d12 t :=
  leafHomotopy_edgePoint_of_ne _ _ (by decide) (by decide) s t

/-- The collapse sends the leaf to its neighbour.
@isnad1 id=eq.0h0v.s10.19e3fcce0155 from=translated src=- shape=52ca3a1e vocab=81d53919
-/
theorem path3_collapse_leaf :
    leafCollapse path3_adj_01 path3_eq_one_of_adj_zero (vertex path3 0) =
      vertex _ ⟨1, by decide⟩ :=
  leafCollapse_vertex_self _ _

/-- The remaining edge `1 — 2` has contractible realization, through the leaf step.
@isnad1 id=contract.0h0v.s7.090433a1ad16 from=translated src=- shape=7054b85f vocab=cf23bc0e
-/
theorem path3_remainder_contractibleSpace :
    ContractibleSpace (Realization (path3.induce ({0}ᶜ : Set (Fin 3)))) :=
  have := path3_contractibleSpace
  path3LeafEquiv.symm.contractibleSpace

/-! ### The star with three leaves -/

/-- The star on `Fin 4` centred at `0`.-/
abbrev star4 : SimpleGraph (Fin 4) := starGraph 0

/--
@isnad1 id=contract.0h0v.s4.4995f2945a68 from=translated src=- shape=b781e9e2 vocab=a0936e35
-/
theorem star4_contractibleSpace : ContractibleSpace (Realization star4) :=
  contractibleSpace_realization_of_isTree _ (isTree_starGraph 0)

/--
@isnad1 id=simplyco.0h0v.s4.328af4925975 from=translated src=- shape=b781e9e2 vocab=d7a80ab6
-/
theorem star4_simplyConnectedSpace : SimplyConnectedSpace (Realization star4) :=
  (isTree_iff_simplyConnectedSpace_realization _).1 (isTree_starGraph 0)

/-! ### The triangle -/

open TDA.Reeb.Examples.GraphCycleObstruction (triangle triangle_not_isTree)

/-- The triangle is not a tree, so its realization is not simply connected by the tree criterion.
@isnad1 id=not.0h0v.s4.bc7be64082ea from=translated src=- shape=375783c1 vocab=b75f000f
-/
theorem triangle_not_simplyConnectedSpace : ¬ SimplyConnectedSpace (Realization triangle) :=
  (isTree_iff_simplyConnectedSpace_realization _).not.1 triangle_not_isTree

/--
@isnad1 id=not.0h0v.s4.f56a6e3860a3 from=translated src=- shape=375783c1 vocab=82423060
-/
theorem triangle_not_contractibleSpace : ¬ ContractibleSpace (Realization triangle) :=
  (isTree_iff_contractibleSpace_realization _).not.1 triangle_not_isTree

end

end TDA.Reeb.Examples.GraphTreeContraction
