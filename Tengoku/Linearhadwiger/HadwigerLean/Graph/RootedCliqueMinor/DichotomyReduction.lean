import Tengoku.Linearhadwiger.HadwigerLean.Graph.RootedCliqueMinor.ContractionAttached
import Tengoku.Linearhadwiger.HadwigerLean.Graph.RootedCliqueMinor.SeparationPullback

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The contraction step of the rooted-clique separator dichotomy

An attached model in the quotient lifts through a root-free contraction.
A small quotient separation either already pulls back with order below r,
or gives an order-r separation whose boundary contains the contracted edge.
-/

namespace HadwigerLean

/--
@isnad1 id=eq.3h9v.s8.887b770a1d7e from=translated src=- shape=7c629769 vocab=2962d4bb
-/
theorem cliqueModel_contract_nonroot_edge_branch
    {V : Type*} {G : SimpleGraph V} {r : ℕ}
    (root : Fin r → V)
    (M : MinorModel (SimpleGraph.completeGraph (Fin (2 * r)))
      (completeRoots G (Set.range root)))
    {a b : V} (hab : G.Adj a b)
    (i₀ : Fin (2 * r))
    (ha : a ∈ M.branch i₀) (hb : b ∈ M.branch i₀)
    (j : Fin (2 * r)) :
    (cliqueModel_contract_nonroot_edge root M hab i₀ ha hb).branch j =
      (edgeContractionPartition G hab).index '' M.branch j := by
  let Pplus := edgeContractionPartition (completeRoots G (Set.range root))
    (completeRoots.supergraph hab)
  let P := edgeContractionPartition G hab
  have hindex (x : V) : Pplus.index x = P.index x := by
    apply P.index_eq_of_mem
    exact Pplus.index_mem x
  change Pplus.index '' M.branch j = P.index '' M.branch j
  ext q
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, hindex x⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, (hindex x).symm⟩

/-- The third outcome of a contraction step is the order-r boundary used
for the recursive torso argument.-/
structure RootCliqueCriticalSeparation
    {V : Type*} [Fintype V] (G : SimpleGraph V) {r : ℕ}
    (root : Fin r → V)
    (M : MinorModel (SimpleGraph.completeGraph (Fin (2 * r)))
      (completeRoots G (Set.range root)))
    (a b : V) where
  sep : VertexSeparation G
  order_eq : sep.separatorFinset.card = r
  roots_left : ∀ i, root i ∈ sep.left
  branch_far : ∃ j, M.branch j ⊆ sep.strictRight
  a_boundary : a ∈ sep.separatorFinset
  b_boundary : b ∈ sep.separatorFinset

end HadwigerLean
