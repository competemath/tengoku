import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.PathMetric
import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.TokenMove

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Path-token adjacency has coordinate distance one

An allowed token move on a path replaces exactly one entry of the increasing coordinate
enumeration by an adjacent, previously unoccupied vertex.
-/

namespace BurningPath

private theorem coordinate_mem {n k : ℕ} (A : Configuration (Fin n) k) (i : Fin k) :
    coordinate A i ∈ A.1 := by
  change A.1.orderEmbOfFin A.2 i ∈ A.1
  exact Finset.orderEmbOfFin_mem A.1 A.2 i

private theorem strictMono_update_of_pathGraph_adj {n k : ℕ} {f : Fin k → Fin n}
    (hf : StrictMono f) {i : Fin k} {u v : Fin n} (hi : f i = u)
    (hv : ∀ j, f j ≠ v) (huv : (SimpleGraph.pathGraph n).Adj u v) :
    StrictMono (Function.update f i v) := by
  intro a b hab
  have hpath := SimpleGraph.pathGraph_adj.mp huv
  by_cases hai : a = i
  · subst a
    have hbi : b ≠ i := by
      intro h
      subst b
      exact (lt_irrefl i hab).elim
    rw [Function.update_self, Function.update_of_ne hbi]
    have hub : u < f b := by
      rw [← hi]
      exact hf hab
    have hbne : (f b).val ≠ v.val := fun h ↦ hv b (Fin.ext h)
    change v.val < (f b).val
    rcases hpath with hpath | hpath <;> omega
  · by_cases hbi : b = i
    · subst b
      rw [Function.update_of_ne hai, Function.update_self]
      have hau : f a < u := by
        rw [← hi]
        exact hf hab
      have hane : (f a).val ≠ v.val := fun h ↦ hv a (Fin.ext h)
      change (f a).val < v.val
      rcases hpath with hpath | hpath <;> omega
    · rw [Function.update_of_ne hai, Function.update_of_ne hbi]
      exact hf hab

/--
Along an edge of the path token graph, the target coordinate list is obtained by updating
one source coordinate to an adjacent unoccupied path vertex.-/
theorem pathTokenGraph_adj_exists_coordinate_update {n k : ℕ}
    (A B : Configuration (Fin n) k) (h : (pathTokenGraph n k).Adj A B) :
    ∃ i : Fin k, ∃ v : Fin n,
      (SimpleGraph.pathGraph n).Adj (coordinate A i) v ∧
        v ∉ A.1 ∧ coordinate B = Function.update (coordinate A) i v := by
  classical
  obtain ⟨u, huA, v, hvA, huv, hB⟩ :=
    (tokenGraph_adj_iff_exists_move (SimpleGraph.pathGraph n) k A B).mp h
  have huRange : u ∈ Set.range (A.1.orderEmbOfFin A.2) := by
    rw [Finset.range_orderEmbOfFin]
    exact huA
  obtain ⟨i, hi'⟩ := huRange
  have hi : coordinate A i = u := by
    change A.1.orderEmbOfFin A.2 i = u
    exact hi'
  have hvcoord : ∀ j, coordinate A j ≠ v := by
    intro j hj
    exact hvA (hj ▸ coordinate_mem A j)
  let updated : Fin k → Fin n := Function.update (coordinate A) i v
  have hupdated : StrictMono updated := by
    exact strictMono_update_of_pathGraph_adj (coordinate_strictMono A) hi hvcoord huv
  let updatedEmb : Fin k ↪o Fin n := OrderEmbedding.ofStrictMono updated hupdated
  have hupdatedMem : ∀ j, updatedEmb j ∈ B.1 := by
    intro j
    rw [hB]
    by_cases hji : j = i
    · subst j
      simp [updatedEmb, updated]
    · have hju : coordinate A j ≠ u := by
        intro hju
        apply hji
        exact (coordinate_strictMono A).injective (hju.trans hi.symm)
      simp [updatedEmb, updated, hji, hju, coordinate_mem A j]
  have hemb : updatedEmb = B.1.orderEmbOfFin B.2 :=
    Finset.orderEmbOfFin_unique' B.2 hupdatedMem
  have hcoordinate : coordinate B = updated := by
    funext j
    change B.1.orderEmbOfFin B.2 j = updated j
    rw [← hemb]
    rfl
  refine ⟨i, v, ?_, hvA, ?_⟩
  · rw [hi]
    exact huv
  · simpa [updated] using hcoordinate

/-- Adjacent path-token configurations have ordered-coordinate `ℓ₁` distance one.-/
theorem pathConfigurationDist_eq_one_of_adj {n k : ℕ}
    (A B : Configuration (Fin n) k) (h : (pathTokenGraph n k).Adj A B) :
    pathConfigurationDist A B = 1 := by
  classical
  obtain ⟨i, v, hiv, _, hcoordinate⟩ :=
    pathTokenGraph_adj_exists_coordinate_update A B h
  rw [pathConfigurationDist, hcoordinate, Fintype.sum_eq_single i]
  · rw [Function.update_self]
    rcases SimpleGraph.pathGraph_adj.mp hiv with hiv | hiv <;> unfold Nat.dist <;> omega
  · intro j hji
    rw [Function.update_of_ne hji]
    exact Nat.dist_self _

end BurningPath
