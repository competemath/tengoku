import Tengoku.Linearhadwiger.HadwigerLean.Graph.Linkedness.Massed
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Transport of linkedness across induced graph isomorphisms
-/

namespace HadwigerLean
namespace Linkedness

/-- `k`-linkedness is invariant under graph isomorphism.
@isnad1 id=klinked.1h6v.s4.e346beddcf69 from=translated src=- shape=1880b659 vocab=b757df76
-/
theorem kLinked_of_iso
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (k : ℕ) (hG : KLinked G k) : KLinked H k := by
  intro P hP hne
  let Q : IndexedPairs (Fin k) V :=
    ⟨fun i => e.symm (P.start i), fun i => e.symm (P.finish i)⟩
  have hQterm (i : Fin k) : Q.terminals i = e ⁻¹' P.terminals i := by
    ext v
    simp only [Q, IndexedPairs.terminals, Set.mem_preimage, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro (rfl | rfl)
      · left; exact e.apply_symm_apply _
      · right; exact e.apply_symm_apply _
    · rintro (h | h)
      · left; exact e.injective (by simpa using h)
      · right; exact e.injective (by simpa using h)
  have hQ : Q.DisjointTerminals := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro v hvi hvj
    rw [hQterm] at hvi hvj
    exact (Set.disjoint_left.mp (hP hij)) hvi hvj
  have hQne : ∀ i, Q.start i ≠ Q.finish i := by
    intro i heq
    exact hne i (e.symm.injective heq)
  obtain ⟨L⟩ := hG Q hQ hQne
  let mappedPath : ∀ i : Fin k, H.Path (P.start i) (P.finish i) := fun i => by
      let p := (L.path i).mapEmbedding e.toEmbedding
      exact ⟨(p : H.Walk (e (Q.start i)) (e (Q.finish i))).copy
        (by simp [Q]) (by simp [Q]), by simpa using p.property⟩
  let M : IndexedLinkage H P := {
    path := mappedPath
    disjoint := by
      intro i j hij
      apply Set.disjoint_left.mpr
      intro v hvi hvj
      have hpre (i : Fin k) (hv : v ∈ pathVertexSet
          ((L.path i).mapEmbedding e.toEmbedding)) :
          e.symm v ∈ pathVertexSet (L.path i) := by
        change v ∈ (((L.path i : G.Path (Q.start i) (Q.finish i)).1.map
          e.toHom).support) at hv
        rw [SimpleGraph.Walk.support_map] at hv
        obtain ⟨u, hu, heq⟩ := List.mem_map.mp hv
        have huv : e.symm v = u := by simpa [← heq]
        exact huv ▸ hu
      have hi : e.symm v ∈ pathVertexSet (L.path i) :=
        hpre i (by simpa [mappedPath, pathVertexSet, SimpleGraph.Walk.support_copy] using hvi)
      have hj : e.symm v ∈ pathVertexSet (L.path j) :=
        hpre j (by simpa [mappedPath, pathVertexSet, SimpleGraph.Walk.support_copy] using hvj)
      exact (Set.disjoint_left.mp (L.disjoint hij)) hi hj
  }
  exact ⟨M⟩

/-- Passing from an induced graph of an induced graph to the corresponding
induced graph of the original graph preserves linkedness.
@isnad1 id=klinked.1h5v.s6.705118df66bf from=translated src=- shape=2e4493c4 vocab=e92d4360
-/
theorem kLinked_induce_image_of_nested
    {V : Type*} (G : SimpleGraph V) (R : Set V) (S : Set R)
    (k : ℕ) (h : KLinked ((G.induce R).induce S) k) :
    KLinked (G.induce (Subtype.val '' S)) k := by
  let e : (G.induce R).induce S ≃g G.induce (Subtype.val '' S) := {
    toEquiv := Equiv.Set.image (fun r : R => (r : V)) S Subtype.val_injective
    map_rel_iff' := by
      intro a b
      rfl
  }
  exact kLinked_of_iso e k h
