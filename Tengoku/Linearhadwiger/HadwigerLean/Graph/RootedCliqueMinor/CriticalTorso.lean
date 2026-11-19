import Tengoku.Linearhadwiger.HadwigerLean.Graph.RootedCliqueMinor.DichotomyReduction
import Tengoku.Linearhadwiger.HadwigerLean.Graph.RootedCliqueMinor.TorsoConnectivity
import Tengoku.Seed.Data.Fintype.EquivFin

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The smaller torso supplied by a critical separator

The order-r boundary is enumerated as a new root family. All original
clique branches restrict to the right torso, whose vertex type is smaller.
-/

namespace HadwigerLean

/-- Restrict a completed-root model using an explicit enumeration of the
boundary, retaining the original restricted branch sets definitionally.-/
noncomputable def VertexSeparation.restrictCompletedRootModel_at_roots
    {V W : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (S : VertexSeparation G)
    (R : Set V) (hR : R ⊆ S.left)
    {H : SimpleGraph W} (M : MinorModel H (completeRoots G R))
    (hmeet : ∀ i, ∃ x ∈ M.branch i, x ∈ S.right)
    {r : ℕ} (xroot : Fin r → S.right)
    (hxrange : Set.range xroot = {x : S.right | (x : V) ∈ S.left}) :
    MinorModel H (completeRoots (G.induce S.right) (Set.range xroot)) := by
  let N := S.restrictCompletedRootModel R hR M hmeet
  refine {
    branch := N.branch
    connected := ?_
    disjoint := N.disjoint
    adjacent := ?_
  }
  · intro i
    simpa only [hxrange] using N.connected i
  · intro i j hij
    simpa only [hxrange] using N.adjacent hij

/--
@isnad1 id=eq.3h10v.s7.47fa966f07a7 from=translated src=- shape=f19dba1f vocab=60761b4b
-/
@[simp] theorem VertexSeparation.restrictCompletedRootModel_at_roots_branch
    {V W : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (S : VertexSeparation G)
    (R : Set V) (hR : R ⊆ S.left)
    {H : SimpleGraph W} (M : MinorModel H (completeRoots G R))
    (hmeet : ∀ i, ∃ x ∈ M.branch i, x ∈ S.right)
    {r : ℕ} (xroot : Fin r → S.right)
    (hxrange : Set.range xroot = {x : S.right | (x : V) ∈ S.left})
    (i : W) :
    (S.restrictCompletedRootModel_at_roots R hR M hmeet xroot hxrange).branch i =
      {x : S.right | (x : V) ∈ M.branch i} := by
  rfl

end HadwigerLean
