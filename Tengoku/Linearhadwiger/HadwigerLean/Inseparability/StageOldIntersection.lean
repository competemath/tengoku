import Tengoku.Linearhadwiger.HadwigerLean.Inseparability.Stages
import Tengoku.Linearhadwiger.HadwigerLean.Woven.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exact old-model intersection with the mixed and rerouted paths

Tangency of every old branch to the previous connected region makes
the old model's region intersection exactly its root set. Rerouting
through disjoint child regions preserves that exact intersection.
-/

namespace HadwigerLean.Inseparability

universe u v

/--
@isnad1 id=eq.1h6v.s6.5ba6bde64bdd from=translated src=- shape=11d14be2 vocab=b32ba323
-/
theorem rooted_model_vertices_inter_region_eq_roots
    {I : Type u} {V : Type v} {G : SimpleGraph V}
    {root : I → V}
    (A : RootedMinorModel (SimpleGraph.completeGraph I) G root)
    (R : Set V)
    (htangent : ∀ i, A.branch i ∩ R = {root i}) :
    A.toMinorModel.vertices ∩ R = Set.range root := by
  ext v
  constructor
  · rintro ⟨hvA,hvR⟩
    obtain ⟨i,hvi⟩ := Set.mem_iUnion.mp hvA
    have hv : v ∈ ({root i} : Set V) := by
      rw [← htangent i]
      exact ⟨hvi,hvR⟩
    exact ⟨i,by simpa using hv.symm⟩
  · rintro ⟨i,rfl⟩
    have hi : root i ∈ A.branch i ∩ R := by
      rw [htangent]
      simp
    exact ⟨Set.mem_iUnion.mpr ⟨i,hi.1⟩,hi.2⟩

/--
@isnad1 id=eq.3h9v.s7.b4a656c1ef30 from=translated src=- shape=bd72664d vocab=d75fff8f
-/
theorem rooted_model_exact_inter_linkage_of_region
    {I : Type u} {K : Type*} {V : Type v}
    {G : SimpleGraph V} {root : I → V}
    (A : RootedMinorModel (SimpleGraph.completeGraph I) G root)
    {P : IndexedPairs K V} (L : IndexedLinkage G P)
    (R : Set V)
    (htangent : ∀ i, A.branch i ∩ R = {root i})
    (hLR : L.vertices ⊆ R)
    (hroots : Set.range root ⊆ L.vertices) :
    A.toMinorModel.vertices ∩ L.vertices = Set.range root := by
  have hAR := rooted_model_vertices_inter_region_eq_roots A R htangent
  apply Set.Subset.antisymm
  · intro v hv
    rw [← hAR]
    exact ⟨hv.1,hLR hv.2⟩
  · rintro v ⟨i,rfl⟩
    exact ⟨Set.mem_iUnion.mpr ⟨i,A.root_mem i⟩,
      hroots ⟨i,rfl⟩⟩

/--
@isnad1 id=eq.4h12v.s7.13d04e693b37 from=translated src=- shape=e9474e66 vocab=09b385e0
-/
theorem rooted_model_exact_inter_linkage_of_reroute
    {I : Type u} {K K' : Type*} {V : Type v}
    {G : SimpleGraph V} {root : I → V}
    (A : RootedMinorModel (SimpleGraph.completeGraph I) G root)
    {P : IndexedPairs K V} (L : IndexedLinkage G P)
    {Q : IndexedPairs K' V} (L' : IndexedLinkage G Q)
    (J : Set V)
    (hExact : A.toMinorModel.vertices ∩ L.vertices = Set.range root)
    (hSupport : L'.vertices ⊆ L.vertices ∪ J)
    (hAJ : Disjoint A.toMinorModel.vertices J)
    (hroots : Set.range root ⊆ L'.vertices) :
    A.toMinorModel.vertices ∩ L'.vertices = Set.range root := by
  apply Set.Subset.antisymm
  · intro v hv
    rcases hSupport hv.2 with hvL | hvJ
    · rw [← hExact]
      exact ⟨hv.1,hvL⟩
    · exact False.elim ((Set.disjoint_left.mp hAJ) hv.1 hvJ)
  · rintro v ⟨i,rfl⟩
    exact ⟨Set.mem_iUnion.mpr ⟨i,A.root_mem i⟩,
      hroots ⟨i,rfl⟩⟩

end HadwigerLean.Inseparability
