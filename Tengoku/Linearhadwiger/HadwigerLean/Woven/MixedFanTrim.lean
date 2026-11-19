import Tengoku.Linearhadwiger.HadwigerLean.Woven.MixedFanLeaf

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# First-hit trimming of a mixed fan

The Menger interface records the two endpoint sets, but its paths may visit
the target set before their designated finishes.  Taking each path up to its
first target preserves disjointness and all avoidance properties.
-/

namespace HadwigerLean
namespace Woven

variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
  {G : SimpleGraph V} {P : IndexedPairs ι V} {H : Finset V}

private structure FirstTarget (p : G.Path s t) (H : Finset V) where
  finish : V
  finish_mem : finish ∈ H
  path : G.Path s finish
  support_subset : pathVertexSet path ⊆ pathVertexSet p
  only_target : ∀ v ∈ pathVertexSet path, v ∈ H → v = finish

private theorem firstTarget_nonempty (p : G.Path s t) (H : Finset V)
    (ht : t ∈ H) : Nonempty (FirstTarget p H) := by
  classical
  let w : G.Walk s t := p
  have hnon : {x ∈ H | x ∈ w.support}.Nonempty := by
    refine ⟨t, ?_⟩
    simp [ht, w]
  obtain ⟨u, huH, huW, hfirst⟩ :=
    w.exists_mem_support_forall_mem_support_imp_eq H hnon
  let q : G.Path s u := ⟨w.takeUntil u huW, p.property.takeUntil huW⟩
  refine ⟨⟨u, huH, q, ?_, ?_⟩⟩
  · intro v hv
    exact w.support_takeUntil_subset_support huW hv
  · intro v hv hvH
    exact hfirst v hvH hv

private noncomputable def firstTarget (p : G.Path s t) (H : Finset V)
    (ht : t ∈ H) : FirstTarget p H :=
  Classical.choice (firstTarget_nonempty p H ht)

/-- Trim each linkage path at its first vertex in `H`.  All starts and
disjointness are preserved; the new path support is contained in the old
one.-/
theorem IndexedLinkage.exists_trimFinishToSet (L : IndexedLinkage G P)
    (hH : ∀ i, P.finish i ∈ H) :
    ∃ (Q : IndexedPairs ι V) (M : IndexedLinkage G Q),
      (∀ i, Q.start i = P.start i) ∧
      (∀ i, Q.finish i ∈ H) ∧
      (∀ i, pathVertexSet (M.path i) ⊆ pathVertexSet (L.path i)) ∧
      (∀ i v, v ∈ pathVertexSet (M.path i) → v ∈ H → v = Q.finish i) := by
  classical
  let d (i : ι) := firstTarget (L.path i) H (hH i)
  let Q : IndexedPairs ι V := ⟨P.start, fun i => (d i).finish⟩
  let M : IndexedLinkage G Q := {
    path := fun i => (d i).path
    disjoint := by
      intro i j hij
      apply Set.disjoint_left.mpr
      intro v hvi hvj
      exact (Set.disjoint_left.mp (L.disjoint hij))
        ((d i).support_subset hvi) ((d j).support_subset hvj)
  }
  exact ⟨Q, M, fun _ => rfl, fun i => (d i).finish_mem,
    fun i => (d i).support_subset, fun i v => (d i).only_target v⟩

/-- If every vertex of `Z` starts a path, no path can meet `Z`
except at its own start.-/
theorem IndexedLinkage.source_only_of_covered
    (L : IndexedLinkage G P) (Z : Finset V)
    (f : Z → ι) (hstart : ∀ z : Z, P.start (f z) = z.1)
    (i : ι) (v : V) (hv : v ∈ pathVertexSet (L.path i))
    (hvZ : v ∈ Z) : v = P.start i := by
  let z : Z := ⟨v, hvZ⟩
  by_cases hi : i = f z
  · subst i
    exact (hstart z).symm
  · have hz : v ∈ pathVertexSet (L.path (f z)) := by
      simpa only [hstart, z] using pathVertexSet.start_mem (L.path (f z))

    exact False.elim ((Set.disjoint_left.mp (L.disjoint hi)) hv hz)

/-- Trim every path at its last visit to `U`. Endpoints at the far side,
disjointness, and path-support containment are preserved.-/
theorem IndexedLinkage.exists_trimStartFromSet
    (L : IndexedLinkage G P) (U : Finset V)
    (hU : ∀ i, P.start i ∈ U) :
    ∃ (Q : IndexedPairs ι V) (M : IndexedLinkage G Q),
      (∀ i, Q.start i ∈ U) ∧
      (∀ i, Q.finish i = P.finish i) ∧
      (∀ i, pathVertexSet (M.path i) ⊆ pathVertexSet (L.path i)) ∧
      (∀ i v, v ∈ pathVertexSet (M.path i) → v ∈ U → v = Q.start i) := by
  classical
  let d (i : ι) := firstTarget (L.path i).reverse U (hU i)
  let Q : IndexedPairs ι V := ⟨fun i => (d i).finish, P.finish⟩
  let M : IndexedLinkage G Q := {
    path := fun i => (d i).path.reverse
    disjoint := by
      intro i j hij
      apply Set.disjoint_left.mpr
      intro v hvi hvj
      have hvi₀ : v ∈ pathVertexSet ((d i).path) := by
        simpa [pathVertexSet, SimpleGraph.Walk.support_reverse] using hvi
      have hvj₀ : v ∈ pathVertexSet ((d j).path) := by
        simpa [pathVertexSet, SimpleGraph.Walk.support_reverse] using hvj
      have hvi' : v ∈ pathVertexSet (L.path i) := by
        have h := (d i).support_subset hvi₀
        simpa [pathVertexSet, SimpleGraph.Walk.support_reverse] using h
      have hvj' : v ∈ pathVertexSet (L.path j) := by
        have h := (d j).support_subset hvj₀
        simpa [pathVertexSet, SimpleGraph.Walk.support_reverse] using h
      exact (Set.disjoint_left.mp (L.disjoint hij)) hvi' hvj'
  }
  refine ⟨Q,M,fun i => (d i).finish_mem,fun _ => rfl,?_,?_⟩
  · intro i v hv
    have hv₀ : v ∈ pathVertexSet ((d i).path) := by
      change v ∈ pathVertexSet ((d i).path.reverse) at hv
      simpa [pathVertexSet, SimpleGraph.Walk.support_reverse] using hv
    have hv' := (d i).support_subset hv₀
    simpa [pathVertexSet, SimpleGraph.Walk.support_reverse] using hv'
  · intro i v hv hvU
    have hv₀ : v ∈ pathVertexSet ((d i).path) := by
      change v ∈ pathVertexSet ((d i).path.reverse) at hv
      simpa [pathVertexSet, SimpleGraph.Walk.support_reverse] using hv
    exact (d i).only_target v hv₀ hvU
variable {a : ℕ} {Z U : Finset V}
  {P : IndexedPairs (Fin a × Fin 2) V}

end Woven
end HadwigerLean
